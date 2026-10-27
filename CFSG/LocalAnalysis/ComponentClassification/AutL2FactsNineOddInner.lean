module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

theorem mem_psl2Range_of_odd {F : Type} [Field F] (t : PGL2 F) (ht : Odd (orderOf t)) :
    t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_odd_orderOf ht

theorem footeNineOddInner :
    ∀ (S : Type) [Group S] [Finite S], Blueprint.LieModel S .PSL 2 3 2 →
      FooteLit.OddOuterInner S := by
  intro S _ _ hS σ hσ
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hxo : Odd (orderOf (autEquiv e σ)) := by rwa [MulEquiv.orderOf_eq]
  have hright : (autEquiv e σ).right = 1 := by
    have h1 : orderOf (autEquiv e σ).right ∣ 2 := by
      have := orderOf_dvd_natCard (autEquiv e σ).right
      rwa [card_ringAut F Nat.prime_three hF] at this
    have h2 : orderOf (autEquiv e σ).right ∣ orderOf (autEquiv e σ) :=
      orderOf_map_dvd (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) _
    have := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hxo), Nat.dvd_one,
      orderOf_eq_one_iff] at this
  have hx : autEquiv e σ = SemidirectProduct.inl (autEquiv e σ).left :=
    SemidirectProduct.ext rfl hright
  have hlo : Odd (orderOf (autEquiv e σ).left) := by
    rw [hx, orderOf_injective _ SemidirectProduct.inl_injective] at hxo
    exact hxo
  obtain ⟨z, hz⟩ := mem_psl2Range_of_odd _ hlo
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply, incl_apply, hz]
  exact hx

end CFSG.ComponentClassification.AutL2Facts
