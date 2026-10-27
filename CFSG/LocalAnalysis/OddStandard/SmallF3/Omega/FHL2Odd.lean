module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHCent3Gen
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

theorem fh_odd3Inner_psl2 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : f ∣ 4)
    (hS : LieModel S .PSL 2 3 f) : FHOdd3Inner S := by
  intro σ hσ
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hxo : orderOf (autEquiv e σ) ∣ 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_dvd_of_pow_eq_one hσ
  have hright : (autEquiv e σ).right = 1 := by
    have h1 : orderOf (autEquiv e σ).right ∣ f := by
      have := orderOf_dvd_natCard (autEquiv e σ).right
      rwa [card_ringAut F Nat.prime_three hF] at this
    have h2 : orderOf (autEquiv e σ).right ∣ orderOf (autEquiv e σ) :=
      orderOf_map_dvd (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) _
    have h3 := Nat.dvd_gcd (h2.trans hxo) (h1.trans hf)
    rwa [show Nat.gcd 3 4 = 1 by decide, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have hx : autEquiv e σ = SemidirectProduct.inl (autEquiv e σ).left :=
    SemidirectProduct.ext rfl hright
  have hlo : Odd (orderOf (autEquiv e σ).left) := by
    have h := hxo
    rw [hx, orderOf_injective _ SemidirectProduct.inl_injective] at h
    exact Odd.of_dvd_nat (by decide) h
  obtain ⟨z, hz⟩ := pgl2_mem_psl2Range_of_odd_orderOf hlo
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply, incl_apply, hz]
  exact hx

end CFSG.OddStandard.SmallF3.Omega
