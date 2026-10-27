module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27SmallU42
public import CFSG.GH74.KGroups.L34Tables
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Data.Seitz77Sec27L34Ord3

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.KGroups.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Certificates

theorem orderIsA_toA_iff {n : ℕ} (g : Equiv.Perm (Fin n)) :
    orderIsA n (toA g) 3 = true ↔ orderOf g = 3 := by
  rw [orderIsA_rep (rep_toA g) 3]
  exact orderIs_iff g (by norm_num)

theorem l34Ord3Check_sound
    (h : Certificates.Seitz77Sec27.l34Ord3Check = true) : ∀ x ∈ L34.QP.originalSubgroup, ∀ y ∈ L34.QP.originalSubgroup, orderOf x = 3 → orderOf y = 3 → ∃ g ∈ L34.QP.originalSubgroup, g * x * g⁻¹ = y := by
  have hQ := L34.QP_ok
  unfold Certificates.Seitz77Sec27.l34Ord3Check Certificates.Seitz77Sec27.l34Ord3CheckL at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hm⟩ := h
  set L3 := (enumA L34.QP).filter (fun a => orderIsA 42 a 3) with hL3
  have hcount : Nat.card {g : L34.QP.originalSubgroup // orderOf (g : Equiv.Perm (Fin 42)) = 3} =
      2240 := by
    classical
    have hcongr : ∀ g ∈ elemsT L34.QP, decide (orderOf g = 3) =
        ((fun a => orderIsA 42 a 3) ∘ toA) g := by
      intro g _
      simp only [Function.comp_apply]
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact (orderIsA_toA_iff g).symm
    rw [card_filter L34.QP hQ (fun g => orderOf g = 3), ← hlen, hL3, enumA_eq,
      List.filter_map, List.length_map, List.filter_congr hcongr]
  obtain ⟨a, tl, hatl⟩ : ∃ a tl, L3 = a :: tl := by
    rcases hL : L3 with _ | ⟨a, tl⟩
    · rw [hL] at hm
      exact absurd hm Bool.false_ne_true
    · exact ⟨a, tl, rfl⟩
  rw [hatl] at hm
  simp only [decide_eq_true_eq] at hm
  have haL3 : a ∈ L3 := by rw [hatl]; exact List.mem_cons_self
  obtain ⟨haE, hao⟩ := List.mem_filter.1 haL3
  rw [enumA_eq] at haE
  obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.1 haE
  have hx₀G : x₀ ∈ L34.QP.originalSubgroup := (mem_elemsT L34.QP hQ x₀).1 hx₀
  have hx₀o : orderOf x₀ = 3 := (orderIsA_toA_iff x₀).1 hao
  have hcent : Nat.card ↥(centralizerIn L34.QP.originalSubgroup x₀) = 9 := by
    have := centLenA_enumA L34.QP hQ x₀
    rw [hm] at this
    exact this.symm
  have hG : Nat.card L34.QP.originalSubgroup = 20160 := by
    rw [card_group L34.QP hQ, L34.QP_valid.2]
  have hos := ncard_conjClass_mul_card L34.QP.originalSubgroup x₀
  rw [hcent, hG] at hos
  have hA : (conjClass L34.QP.originalSubgroup x₀).ncard = 2240 := by omega
  set B : Set (Equiv.Perm (Fin 42)) :=
    {y | y ∈ L34.QP.originalSubgroup ∧ orderOf y = 3} with hB
  have hAB : conjClass L34.QP.originalSubgroup x₀ ⊆ B := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨L34.QP.originalSubgroup.mul_mem
      (L34.QP.originalSubgroup.mul_mem hc hx₀G) (L34.QP.originalSubgroup.inv_mem hc), ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx₀o
  have hBfin : B.Finite := (Set.toFinite _ : (Set.univ : Set (Equiv.Perm (Fin 42))).Finite).subset
    (Set.subset_univ _)
  have hBcard : B.ncard = 2240 := by
    have e : B = Subtype.val ''
        {g : L34.QP.originalSubgroup | orderOf (g : Equiv.Perm (Fin 42)) = 3} := by
      ext y
      constructor
      · rintro ⟨hy, hyo⟩
        exact ⟨⟨y, hy⟩, hyo, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.2, hg⟩
    rw [e, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    exact hcount
  have hEq : conjClass L34.QP.originalSubgroup x₀ = B :=
    Set.eq_of_subset_of_ncard_le hAB (by rw [hA, hBcard]) hBfin
  intro x hx y hy hxo hyo
  have hxB : x ∈ B := ⟨hx, hxo⟩
  have hyB : y ∈ B := ⟨hy, hyo⟩
  rw [← hEq] at hxB hyB
  obtain ⟨c₁, hc₁, rfl⟩ := hxB
  obtain ⟨c₂, hc₂, rfl⟩ := hyB
  refine ⟨c₂ * c₁⁻¹, L34.QP.originalSubgroup.mul_mem hc₂ (L34.QP.originalSubgroup.inv_mem hc₁), ?_⟩
  group

end CFSG.OddStandard.Seitz77
