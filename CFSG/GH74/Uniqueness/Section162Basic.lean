module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Section123
public import CFSG.GH74.Uniqueness.Section12Center
public import CFSG.GH74.Uniqueness.Section162Suzuki

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section FZero

omit [Finite X] in
theorem fZero_le {F : Subgroup X} {t : X} (htF : t ∈ F) : fZero Z M F t ≤ F := by
  refine (closure_le _).mpr fun x hx => ?_
  rcases hx with hx | hx
  · exact (Cor713.zHull_le (M ⊓ F) hx).2
  · rw [Set.mem_singleton_iff.mp hx]
    exact htF

omit [Finite X] in
theorem mem_fZero_of_mem {F : Subgroup X} {t w : X} (hw : w ∈ Z) (hwM : w ∈ M) (hwF : w ∈ F) :
    w ∈ fZero Z M F t :=
  subset_closure (Or.inl (subset_closure ⟨hw, mem_inf.mpr ⟨hwM, hwF⟩⟩))

omit [Finite X] in
theorem t_mem_fZero {F : Subgroup X} {t : X} : t ∈ fZero Z M F t :=
  subset_closure (Or.inr rfl)

omit [Finite X] in
theorem fZero_le_of {F K : Subgroup X} {t : X} (h1 : ∀ w ∈ Z, w ∈ M → w ∈ F → w ∈ K)
    (h2 : t ∈ K) : fZero Z M F t ≤ K := by
  refine (closure_le _).mpr fun x hx => ?_
  rcases hx with hx | hx
  · refine (closure_le _).mpr (fun w hw => ?_) hx
    obtain ⟨hwZ, hwMF⟩ := hw
    obtain ⟨hwM, hwF⟩ := mem_inf.mp hwMF
    exact h1 w hwZ hwM hwF
  · rw [Set.mem_singleton_iff.mp hx]
    exact h2

omit [Finite X] in
theorem closure_mul_self_fZero (hZ : IsInvariantInvolutionSet Z) {F : Subgroup X} {t : X}
    (ht : t * t = 1) : closure {x : ↥(fZero Z M F t) | x * x = 1} = ⊤ := by
  set F₀ := fZero Z M F t with hF₀
  have hle : F₀ ≤ (closure {x : ↥F₀ | x * x = 1}).map F₀.subtype := by
    refine fZero_le_of (fun w hw hwM hwF => ?_) ?_
    · refine ⟨⟨w, mem_fZero_of_mem hw hwM hwF⟩, subset_closure ?_, rfl⟩
      exact Subtype.ext (hZ.mul_self_eq_one hw)
    · exact ⟨⟨t, t_mem_fZero⟩, subset_closure (Subtype.ext ht), rfl⟩
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

end FZero

section BenderSubAPI

omit [Finite X] in
theorem BenderSub.closure_mul_self (hZ : IsInvariantInvolutionSet Z) {F : Subgroup X}
    {n i e : ℕ} (hB : BenderSub Z M F n i e) : closure {x : ↥F | x * x = 1} = ⊤ := by
  have hle : F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
    have h1 : zHull Z F ≤ (closure {x : ↥F | x * x = 1}).map F.subtype := by
      refine (closure_le _).mpr fun y hy => ?_
      refine ⟨⟨y, hy.2⟩, subset_closure ?_, rfl⟩
      exact Subtype.ext (hZ.mul_self_eq_one hy.1)
    rwa [hB.zhull] at h1
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

theorem BenderSub.center_eq_bot
    (hZ : IsInvariantInvolutionSet Z) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) (hi : i = 1 ∨ i = 2) : center ↥F = ⊥ :=
  center_eq_bot_of_benderType hi (hB.closure_mul_self hZ) (A2.odd_card_center_of_benderSub hB)
    hB.bender

theorem ZDSetup.fZero_eq_of_benderSub
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) (hi : i = 1 ∨ i = 2) {t : X} (htZ : t ∈ Z) (htM : t ∉ M)
    (htF : t ∈ F) : fZero Z M F t = F ∧ Bender.BenderType ↥F n i 1 := by
  have hcen := hB.center_eq_bot S.invariant hi
  have he : e = 1 := by
    rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
    · exact he
    · exact he
    · omega
  subst he
  have hBF : Bender.BenderType ↥F n i 1 := benderType_of_center_eq_bot hB.bender hcen
  refine ⟨?_, hBF⟩
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨Q, hQ⟩ := exists_sylow_normalizer_eq_of_center_eq_bot hcen hT
  have : IsSimpleGroup ↥F := hBF.isSimple
  set t' : ↥F := ⟨t, htF⟩ with ht'def
  have ht' : t' * t' = 1 := Subtype.ext (S.invariant.mul_self_eq_one htZ)
  have hborel : Bender.borel (Q : Subgroup ↥F) = (M ⊓ F).subgroupOf F := hQ.symm
  have ht'Q : t' ∉ Bender.borel (Q : Subgroup ↥F) := by
    rw [hborel]
    intro h
    exact htM (mem_inf.mp (mem_subgroupOf.mp h)).1
  have hc := hBF.benderCore Q ht' ht'Q
  have htop : Bender.rootCenter (Q : Subgroup ↥F) ⊔ zpowers t' = ⊤ := by
    rcases hi with rfl | rfl
    · have hZQ : Bender.rootCenter (Q : Subgroup ↥F) = Q :=
        Subgroup.eq_of_le_of_card_ge (Bender.rootCenter_le _)
          (by rw [hc.card_center, hc.card_eq, pow_one])
      rw [hZQ]
      exact hc.sup_zpowers_eq_top ht'Q
    · exact hBF.rootCenter_sup_zpowers_suzuki Q ht' ht'Q
  have hle : Bender.rootCenter (Q : Subgroup ↥F) ⊔ zpowers t' ≤ (fZero Z M F t).subgroupOf F := by
    refine sup_le (fun x hx => ?_) (zpowers_le.mpr (mem_subgroupOf.mpr t_mem_fZero))
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    have hxM : (x : X) ∈ M := by
      have hxB : x ∈ Bender.borel (Q : Subgroup ↥F) :=
        Bender.le_borel _ (Bender.rootCenter_le _ hx)
      rw [hborel] at hxB
      exact (mem_inf.mp (mem_subgroupOf.mp hxB)).1
    have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hc.center_sq x hx) hx1
    have hxZ : (x : X) ∈ Z := hB.invol _ x.2 (by rw [Subgroup.orderOf_coe]; exact hx2)
    exact mem_subgroupOf.mpr (mem_fZero_of_mem hxZ hxM x.2)
  rw [htop, top_le_iff, subgroupOf_eq_top] at hle
  exact le_antisymm (fZero_le htF) hle

end BenderSubAPI

end CFSG.GH74.Uniqueness
