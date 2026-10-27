module

public import CFSG.GH74.GLS.Stage1.Thm4.L98d

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem t_ne_z : t ≠ z := by
  intro htz
  apply h.std.comm_nle
  rw [htz]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hc : Commute a z := h.z_comm ha
  have : ⁅a, z ^ k⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hc.zpow_right k).eq
  rw [this]
  exact one_mem _

theorem P_conj (hC : IVK_5_1f) (hF : Step9_8_Fstar) (h96 : Lemma9_6) {n : ℕ} (hn8 : 8 ≤ n)
    (hn11 : n ≤ 11) (hcov : IsDoubleCoverOfAlt Lh n) :
    ∀ u ∈ S ⊓ K, orderOf u = 2 → IsConj z u := by
  intro u huP hu2
  by_cases huz : u = z
  · rw [huz]
  have htK := h.t_mem_K h96 hF hcov
  have htC : t ∈ Cz z := h.std.t_cen
  haveI : (K.subgroupOf (Cz z)).Normal := h.K_normal_C
  have hyp := h.hypC hF hn8 hn11 hcov
  have hconj := core_P_conj (N := pPrimeCore 2 ↥(Cz z)) (K := K.subgroupOf (Cz z))
    (S := S.subgroupOf (Cz z)) hC hyp odd_card_pPrimeCore h.sylowC
    (zc := ⟨z, h.z_cen⟩) h.z_mem (fun k hk => Subtype.ext (h.z_comm hk))
    (by rw [Subgroup.orderOf_mk]; exact h.z_ord)
    (t := ⟨t, htC⟩) ⟨h.std.t_mem, htK⟩ (by rw [Subgroup.orderOf_mk]; exact h.std.t_ord)
    (fun heq => h.t_ne_z (congrArg Subtype.val heq)) h.z_mem_S
    ⟨u, h.S_le huP.1⟩ ⟨huP.1, huP.2⟩ (by rw [Subgroup.orderOf_mk]; exact hu2)
    (fun heq => huz (congrArg Subtype.val heq))
  have hG : IsConj u t := by
    have := MonoidHom.map_isConj (Cz z).subtype hconj
    simpa using this
  exact (h.isConj_z_t hcov).trans hG.symm

theorem relIndex_le (hA : IVK_5_1_index) (hF : Step9_8_Fstar) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) : (S ⊓ K).relIndex S ≤ 2 := by
  haveI : (K.subgroupOf (Cz z)).Normal := h.K_normal_C
  have hyp := h.hypC hF hn8 hn11 hcov
  have hle := core_relIndex_le (N := pPrimeCore 2 ↥(Cz z)) (K := K.subgroupOf (Cz z))
    (S := S.subgroupOf (Cz z)) hA hyp odd_card_pPrimeCore h.sylowC.isPGroup
  have e := Subgroup.relIndex_subgroupOf (H := S ⊓ K) (K := S) (L := Cz z) h.S_le
  have e2 : (S ⊓ K).subgroupOf (Cz z) = S.subgroupOf (Cz z) ⊓ K.subgroupOf (Cz z) :=
    Subgroup.ext fun x => Iff.rfl
  rw [e2] at e
  rw [← e]
  exact hle

theorem inv_S_conj (hA : IVK_5_1_index) (hC : IVK_5_1f) (hF : Step9_8_Fstar) (h96 : Lemma9_6) {n : ℕ}
    (hn8 : 8 ≤ n) (hn11 : n ≤ 11) (hcov : IsDoubleCoverOfAlt Lh n) (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    ∀ u ∈ S, orderOf u = 2 → IsConj z u := by
  intro u huS hu2
  by_cases huP : u ∈ S ⊓ K
  · exact h.P_conj hC hF h96 hn8 hn11 hcov u huP hu2
  have hle := h.relIndex_le hA hF hn8 hn11 hcov
  have h2 : (S ⊓ K).relIndex S = 2 := by
    have hne1 : (S ⊓ K).relIndex S ≠ 1 := by
      intro h1
      exact huP ((Subgroup.relIndex_eq_one.1 h1) huS)
    have hne0 : (S ⊓ K).relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hnorm : ∀ s ∈ S, ∀ q ∈ S ⊓ K, s * q * s⁻¹ ∈ S ⊓ K := fun s hs q hq =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hq.1) (Subgroup.inv_mem _ hs),
      (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer (h.S_le hs)) q).1 hq.2⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_relIndex_two hsimple hnab ((CFSG.ABGLocalTools.isSylowOf_iff).1 hS)
    inf_le_left hnorm h2 huS huP hu2
  have hv2 : orderOf (g⁻¹ * u * g) = 2 := by
    have := orderOf_conj_eq' g⁻¹ u
    rw [inv_inv] at this
    rw [this]
    exact hu2
  have h1 := h.P_conj hC hF h96 hn8 hn11 hcov _ hg hv2
  exact h1.trans (isConj_iff.2 ⟨g, by group⟩)

theorem one_class (hA : IVK_5_1_index) (hB : IVK_5_1g) (hC : IVK_5_1f) (hF : Step9_8_Fstar)
    (h96 : Lemma9_6) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11) (hcov : IsDoubleCoverOfAlt Lh n)
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  have hSylG := (h.sylowG hB hF hn8 hn11 hcov).1
  have hall : ∀ a : G, orderOf a = 2 → IsConj z a := by
    intro a ha
    have hpg : IsPGroup 2 ↥(zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow hSylG hpg
    have hga : orderOf (g * a * g⁻¹) = 2 := by rw [orderOf_conj_eq']; exact ha
    have h1 := h.inv_S_conj hA hC hF h96 hn8 hn11 hcov hsimple hnab hSylG _ hg hga
    exact h1.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  intro a b ha hb
  exact (hall a ha).symm.trans (hall b hb)

end Ctx98

end CFSG.GH74.GLS.Stage1.Thm4
