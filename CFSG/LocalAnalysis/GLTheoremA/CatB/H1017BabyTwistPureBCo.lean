module

public import Certificates.Certificate101704
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Co2Cert.Cert

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwistCo

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu CFSG.RankThree.Native
  CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T


private theorem eq_Dg_of_le_Qg {A : Subgroup (Equiv.Perm (Fin 2300))} (hAQ : A ≤ Qg)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 4) : A = Dg :=
  Subgroup.eq_of_le_of_card_ge ((Certificates.certificate101704 A hAQ hA hc).trans
      ((Subgroup.closure_le _).2 fun _ ⟨_, hk, e⟩ => e ▸ dEltP_mem_Dg hk))
    (by rw [card_Dg, hc]; norm_num)

private theorem exists_conj_le_Qg {B : Subgroup (Equiv.Perm (Fin 2300))} (hBP : B ≤ co2P)
    (hB : IsPGroup 3 B) : ∃ g ∈ co2P, B.map (MulAut.conj g).toMonoidHom ≤ Qg := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card (Qg.subgroupOf co2P) = 3 ^ (Nat.card co2P).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qg_le).toEquiv, card_Qg,
      factorization_card_co2P_three]
    norm_num
  obtain ⟨S, hS⟩ := (hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBP).symm).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq co2P S (Sylow.ofCard _ hQ)
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmem : MulAut.conj g • (⟨x, hBP hx⟩ : co2P) ∈ ((g • S : Sylow 3 co2P) : Subgroup co2P) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hS (Subgroup.mem_subgroupOf.2 hx))
  rw [hg, Sylow.coe_ofCard] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

private theorem exists_conj_eq_Dg {B : Subgroup (Equiv.Perm (Fin 2300))} (hBP : B ≤ co2P)
    (hB : IsElemAbelian 3 B) (hc : Nat.card B = 3 ^ 4) :
    ∃ g ∈ co2P, B.map (MulAut.conj g).toMonoidHom = Dg := by
  obtain ⟨g, hg, hle⟩ := exists_conj_le_Qg hBP (IsPGroup.of_card hc)
  exact ⟨g, hg, eq_Dg_of_le_Qg hle (hB.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc])⟩

theorem co2_exists_conj_elemAbelian_four {A₁ A₂ : Subgroup CFSG.Blueprint.NativeSporadic.Co2}
    (h₁ : IsElemAbelian 3 A₁) (h₂ : IsElemAbelian 3 A₂) (hc₁ : Nat.card A₁ = 3 ^ 4)
    (hc₂ : Nat.card A₂ = 3 ^ 4) : ∃ k, A₁.map (MulAut.conj k).toMonoidHom = A₂ := by
  have hP (A : Subgroup CFSG.Blueprint.NativeSporadic.Co2) : A.map co2PermHom ≤ co2P :=
    (Subgroup.map_le_range co2PermHom A).trans co2PermHom_range.le
  obtain ⟨g₁, hg₁, e₁⟩ := exists_conj_eq_Dg (hP A₁) (h₁.map _)
    (by rw [Subgroup.card_map_of_injective co2PermHom_injective, hc₁])
  obtain ⟨g₂, hg₂, e₂⟩ := exists_conj_eq_Dg (hP A₂) (h₂.map _)
    (by rw [Subgroup.card_map_of_injective co2PermHom_injective, hc₂])
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (by rw [co2PermHom_range]; exact co2P.mul_mem (co2P.inv_mem hg₂) hg₁ :
      g₂⁻¹ * g₁ ∈ co2PermHom.range)
  refine ⟨k, Subgroup.map_injective co2PermHom_injective
    (Subgroup.map_injective (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective ?_)⟩
  rw [e₂, Subgroup.map_map_conj, hk, Subgroup.map_conj_map_conj, mul_inv_cancel_left, e₁]

end CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwistCo
