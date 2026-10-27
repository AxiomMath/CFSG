module

public import CFSG.CGT.M24R.L2SubB

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

theorem length_le_card_of_injOn {G : Type*} [Group G] [Finite G] {S : List ℕ} (hS : S.Nodup)
    {f : ℕ → G} (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) {A : Subgroup G}
    (hA : ∀ a ∈ S, f a ∈ A) : S.length ≤ Nat.card A := by
  classical
  have hnd : (S.map f).Nodup := List.Nodup.map_on hf hS
  have h1 : (S.map f).toFinset.card = S.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  have hsub : ((S.map f).toFinset : Set G) ⊆ (A : Set G) := by
    intro y hy
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact hA a ha
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, h1] at h2
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact h2

section FA

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem commCount_le {X : Table} {x : N8} (hX : IsTab X x) (A' : Subgroup N8)
    (hcent : ∀ t ∈ T8, t * x = x * t → t ∈ A') : (mkCtx ()).commCount X ≤ Nat.card A' := by
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [Ctx8.commCount, List.countP_eq_length_filter]
  refine length_le_card_of_injOn (List.nodup_range.sublist List.filter_sublist)
    (f := fun k => n8 (tw k)) ?_ ?_
  · intro a ha b hb hab
    exact tw_inj hcard (List.mem_range.1 (List.mem_filter.1 ha).1)
      (List.mem_range.1 (List.mem_filter.1 hb).1) hab
  · intro a ha
    obtain ⟨ha16, hc⟩ := List.mem_filter.1 ha
    have hk := List.mem_range.1 ha16
    have hcomm := (hX.commT_iff hcard (isTab_tt hk)).1 hc
    exact hcent _ (n8_tw_mem a) hcomm.symm

theorem inv_class8 (x : N8) (hx : x * x = 1) (hxT : x ∉ T8) (A' : Subgroup N8)
    (hA' : Nat.card A' ≤ 4) (hcent : ∀ t ∈ T8, t * x = x * t → t ∈ A') :
    ∃ n : N8, n * bb0 * n⁻¹ = x := by
  obtain ⟨c, hc, rfl⟩ := el_surj hcard x
  have hX := isTab_tab (mem_codes.1 hc).1
  have hXs := tab_size c
  have h := Certificates.certificate21193.2.2.2.2.2.1
  simp only [faCheck, List.all_eq_true] at h
  have hc' := h c hc
  have hsq : (compT 16 ((mkCtx ()).tab c) ((mkCtx ()).tab c) == idT 16) = true :=
    ((hX.mul hX).beq_iff hcard IsTab.one (compT_size _ _) idT_size).2 hx
  have hT : (mkCtx ()).isTt ((mkCtx ()).tab c) = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hxT ((isTt_iff hcard hX hXs).1 h')
  have hcnt : decide (4 < (mkCtx ()).commCount ((mkCtx ()).tab c)) = false := by
    rw [decide_eq_false_iff_not, not_lt]
    exact (commCount_le hcard hX A' hcent).trans hA'
  rw [hsq, hT, hcnt] at hc'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨hn, heq⟩ := hc'
  set n := (faMap (mkCtx ()) (mkCtx ()).codes)[codeOf ((mkCtx ()).tab c)]!
  have hN := isTab_tab hn
  have e := ((hN.mul isTab_b0T).beq_iff hcard (hX.mul hN) (compT_size _ _) (compT_size _ _)).1 heq
  refine ⟨el n, ?_⟩
  rw [e, mul_inv_cancel_right]

end FA

end CFSG.CGT.M24R
