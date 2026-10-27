module

public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.GH74.GLS.C3.Layer1.P34Stmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement

theorem isFAutL2A7_of_not_innDiag {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (hF9 : Nat.card F = 9) {H : Type} [Group H] [Finite H] (e : H ≃* L2 F) {ρ : MulAut H}
    (hdiag : ρ ∉ innDiagSub e) (hρ2 : ρ ^ 2 = 1) : P34.IsFAutL2A7 H ρ := by
  have : (innDiagSub e).Normal := innDiagSub_normal e
  have htop := innDiagSub_sup_fieldAutSub e
  have hρtop : ρ ∈ innDiagSub e ⊔ fieldAutSub e := htop ▸ Subgroup.mem_top ρ
  obtain ⟨d, hd, g, hg, hdg⟩ := Subgroup.mem_sup_of_normal_left.1 hρtop
  have hg1 : g ≠ 1 := by
    intro h1
    apply hdiag
    rw [← hdg, h1, mul_one]
    exact hd
  have hF2 := card_fieldAutSub_nine hF hF9 e
  have hg2 : orderOf g = 2 := by
    have hdvd : orderOf g ∣ 2 := hF2 ▸ Subgroup.orderOf_dvd_natCard _ hg
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  have hρ1 : ρ ≠ 1 := fun h => hdiag (h ▸ Subgroup.one_mem _)
  obtain ⟨N⟩ := exists_notation hF e
  have hFp : IsPGroup 2 ↥(fieldAutSub e) := IsPGroup.of_card (n := 1) (by rw [hF2]; norm_num)
  have hFT : fieldAutSub e ≤ (N.T : Subgroup (MulAut H)) := by
    have h1 := IsPGroup.inf_normalizer_sylow hFp N.T
    have h2 : fieldAutSub e ⊓ normalizer ((N.T : Subgroup (MulAut H)) : Set (MulAut H)) =
        fieldAutSub e := inf_eq_left.2 N.T_inv
    have h3 : fieldAutSub e ⊓ (N.T : Subgroup (MulAut H)) = fieldAutSub e := h1.symm.trans h2
    exact inf_eq_left.1 h3
  have hgR : g ∈ (N.T : Subgroup (MulAut H)) ⊓ fieldAutSub e := ⟨hFT hg, hg⟩
  have hdg2 : orderOf (d * g) = 2 := by rw [hdg]; exact orderOf_eq_prime hρ2 hρ1
  obtain ⟨a, -, hconj⟩ := ivk_1_2h_c F hF H e N g hgR hg2 d hd hdg2
  have hmem : a⁻¹⁻¹ * ρ * a⁻¹ ∈ fieldAutSub e := by
    rw [← hdg, inv_inv, hconj]
    exact hg
  refine ⟨hρ1, Or.inl ⟨F, inferInstance, inferInstance, twistEquiv e a⁻¹⁻¹, ?_, ?_⟩⟩
  · rw [hF9]; decide
  · exact (mem_fieldAutSub_twist_iff e a⁻¹ ρ).2 hmem

theorem involution_trichotomy_alt6 {H : Type} [Group H] [Finite H]
    (e : H ≃* alternatingGroup (Fin 6)) {ρ : MulAut H} (hρ2 : ρ ^ 2 = 1) :
    ρ ∈ (MulAut.conj : H →* MulAut H).range ∨
      (3 ≤ Nat.card ↥(xu ρ) ∧ Odd (Nat.card ↥(xu ρ))) ∨ P34.IsFAutL2A7 H ρ := by
  obtain ⟨F, _, _, e', hF9⟩ := exists_L2_nine_equiv e
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  by_cases hdiag : ρ ∈ innDiagSub e'
  · by_cases hin : ρ ∈ innAut H
    · exact Or.inl hin
    · right; left
      have hρ1 : ρ ≠ 1 := fun h => hin (h ▸ Subgroup.one_mem _)
      have hord : orderOf ρ = 2 := orderOf_eq_prime hρ2 hρ1
      obtain ⟨-, hodd, h3, -⟩ := Proofs2.xu_outer_data hF e' hdiag hin hord
      exact ⟨h3, hodd⟩
  · right; right
    exact isFAutL2A7_of_not_innDiag hF hF9 e' hdiag hρ2

end CFSG.GH74.GLS.C3.Layer1.Bk
