module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4Model

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Sylow

theorem U_inf_N₂sub : hypUnitriangular h 2 1 ⊓ N₂sub h = patSub h sI₂ isPattern_sI₂ := by
  refine le_antisymm (fun g ⟨hgU, hgN⟩ => ?_) (le_inf (patSub_le_U _ _) patSub_sI₂_le_N₂sub)
  obtain ⟨-, c2⟩ := mem_N₂sub.1 hgN
  have r := N₂sub_rows hgN
  refine mem_patSub_sI₂.2 ⟨hgU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(r ιe₂).1, one_apply_ne (by decide)]
  · rw [c2, one_apply_ne (by decide)]
  · rw [(r ιz).1, one_apply_ne (by decide)]
  · rw [c2, one_apply_ne (by decide)]
  · rw [(r ιf₂).1, one_apply_ne (by decide)]
  · rw [c2, one_apply_ne (by decide)]
  · rw [(r ιf₁).1, one_apply_ne (by decide)]

theorem patSub_sI₂_rel {x : hypSU h 2 1} (hx : x ∈ patSub h sI₂ isPattern_sI₂) :
    mat x ιz ιf₂ = h.bar (mat x ιe₂ ιz) ∧
      mat x ιe₂ ιf₂ + h.bar (mat x ιe₂ ιf₂) = mat x ιe₂ ιz * h.bar (mat x ιe₂ ιz) := by
  obtain ⟨-, r2, -, -, r5, -⟩ := U_rel (patSub_le_U _ _ hx)
  exact ⟨r2, r5⟩

theorem mem_patSub_sI₆_of {x : hypSU h 2 1} (hx : x ∈ patSub h sI₂ isPattern_sI₂)
    (h0 : mat x ιe₂ ιz = 0) : x ∈ patSub h sI₆ isPattern_sI₆ := by
  obtain ⟨hxU, x1, x2, x3, x4, x5, x6, x7⟩ := mem_patSub_sI₂.1 hx
  refine mem_patSub_sI₆.2 ⟨hxU, x1, x2, x3, x4, h0, ?_, x5, x6, x7⟩
  rw [(patSub_sI₂_rel hx).1, h0, map_zero]

theorem patSub_sI₆_le_sI₂ : patSub h sI₆ isPattern_sI₆ ≤ patSub h sI₂ isPattern_sI₂ :=
  patSub_mono _ _ (by decide)

theorem card_patSub_sI₆ : Nat.card (patSub h sI₆ isPattern_sI₆) = 2 ^ f := by
  have := h.charP
  rw [← h.card_fixedField]
  have hfix : ∀ g ∈ patSub h sI₆ isPattern_sI₆, h.bar (mat g ιe₂ ιf₂) = mat g ιe₂ ιf₂ := by
    intro g hg
    have r := (patSub_sI₂_rel (patSub_sI₆_le_sI₂ hg)).2
    rw [(mem_patSub_sI₆.1 hg).2.2.2.2.2.1, zero_mul] at r
    exact bar_eq_of_add_eq_zero h r
  refine Nat.card_congr (Equiv.ofBijective (fun g : patSub h sI₆ isPattern_sI₆ =>
    (⟨mat g.1 ιe₂ ιf₂, h.mem_fixedField.2 (hfix g g.2)⟩ : h.fixedField)) ⟨?_, ?_⟩)
  · rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
    have e' : mat g ιe₂ ιf₂ = mat g' ιe₂ ιf₂ := congrArg Subtype.val e
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_patSub_sI₆.1 hg
    obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := mem_patSub_sI₆.1 hg'
    exact Subtype.ext (eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all)))
  · rintro ⟨c, hc⟩
    obtain ⟨g, hg, hgc⟩ := exists_rootI₆ h (h.mem_fixedField.1 hc)
    exact ⟨⟨g, hg⟩, Subtype.ext hgc⟩

theorem card_patSub_sI₂ : Nat.card (patSub h sI₂ isPattern_sI₂) = (2 ^ f) ^ 3 := by
  rw [card_eq_mul_of_coord patSub_sI₆_le_sI₂ (fun x => mat x ιe₂ ιz)
    (fun x hx y hy => mul_e₂z (patSub_le_U _ _ hx) (patSub_le_U _ _ hy)) ?_ ?_, card_patSub_sI₆]
  · ring
  · intro x hx
    exact ⟨mem_patSub_sI₆_of hx, fun h6 => (mem_patSub_sI₆.1 h6).2.2.2.2.2.1⟩
  · intro u
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u) (by
      rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, hgu, -⟩ := exists_rootI₂ h hc
    exact ⟨g, hg, hgu⟩

theorem isSylowOf_patSub_sI₂ : IsSylowOf 2 (patSub h sI₂ isPattern_sI₂) (N₂sub h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_hypSU (hK := h)
  obtain ⟨hU, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) (by norm_num)
    (by norm_num)
  have hQc := Q.card_eq_multiplicity
  rw [hQ, hU, Nat.card_congr (N₂equiv h).toEquiv] at hQc
  refine CFSG.ABGLocalTools.isSylowOf_of_card patSub_sI₂_le_N₂sub ?_
  rw [card_patSub_sI₂, ← hQc]

end Sylow

section Omega

theorem mul_self_eq_one_iff_mem_patSub_sI₆ {x : hypSU h 2 1}
    (hx : x ∈ patSub h sI₂ isPattern_sI₂) : x * x = 1 ↔ x ∈ patSub h sI₆ isPattern_sI₆ := by
  have := h.charP
  have hxU := patSub_le_U _ _ hx
  have hxx := mul_mem hx hx
  obtain ⟨hxxU, s1, s2, s3, s4, s5, s6, s7⟩ := mem_patSub_sI₂.1 hxx
  have e1 : mat (x * x) ιe₂ ιz = 0 := by
    rw [mul_e₂z hxU hxU, CharTwo.add_self_eq_zero]
  have e2 : mat (x * x) ιz ιf₂ = 0 := by
    rw [mul_zf₂ hxU hxU, CharTwo.add_self_eq_zero]
  have e3 : mat (x * x) ιe₂ ιf₂ = mat x ιe₂ ιz * h.bar (mat x ιe₂ ιz) := by
    rw [mul_e₂f₂ hxU hxU, CharTwo.add_self_eq_zero, zero_add, (patSub_sI₂_rel hx).1]
  constructor
  · intro h1
    rw [h1, mat_one, one_apply_ne (by decide)] at e3
    exact mem_patSub_sI₆_of hx (eq_zero_of_mul_bar_eq_zero e3.symm)
  · intro h6
    rw [(mem_patSub_sI₆.1 h6).2.2.2.2.2.1, zero_mul] at e3
    exact eq_one_of_U_entries hxxU s1 s3 s5 s7 e1 e3 s6 e2 s4 s2

theorem patSub_sI₆_comm {x y : hypSU h 2 1} (hx : x ∈ patSub h sI₆ isPattern_sI₆)
    (hy : y ∈ patSub h sI₂ isPattern_sI₂) : x * y = y * x := by
  have hx₂ := patSub_sI₆_le_sI₂ hx
  have hxU := patSub_le_U _ _ hx₂
  have hyU := patSub_le_U _ _ hy
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7⟩ := mem_patSub_sI₂.1 (mul_mem hx₂ hy)
  obtain ⟨-, b1, b2, b3, b4, b5, b6, b7⟩ := mem_patSub_sI₂.1 (mul_mem hy hx₂)
  obtain ⟨-, -, -, -, -, x5, x6, -, -, -⟩ := mem_patSub_sI₆.1 hx
  refine eq_of_U_entries (mul_mem hxU hyU) (mul_mem hyU hxU) (forall_upper.2 ?_)
  refine ⟨by rw [a1, b1], by rw [a3, b3], by rw [a5, b5], by rw [a7, b7], ?_, ?_, by rw [a6, b6],
    ?_, by rw [a4, b4], by rw [a2, b2]⟩
  · rw [mul_e₂z hxU hyU, mul_e₂z hyU hxU, add_comm]
  · rw [mul_e₂f₂ hxU hyU, mul_e₂f₂ hyU hxU, x5, x6, zero_mul, mul_zero, add_zero, add_zero,
      add_comm]
  · rw [mul_zf₂ hxU hyU, mul_zf₂ hyU hxU, add_comm]

theorem closure_involutions_patSub_sI₂ :
    closure {x | x ∈ patSub h sI₂ isPattern_sI₂ ∧ x * x = 1} = patSub h sI₆ isPattern_sI₆ := by
  refine le_antisymm ((closure_le _).2 fun x hx =>
    (mul_self_eq_one_iff_mem_patSub_sI₆ hx.1).1 hx.2) fun x hx => subset_closure
      ⟨patSub_sI₆_le_sI₂ hx, (mul_self_eq_one_iff_mem_patSub_sI₆ (patSub_sI₆_le_sI₂ hx)).2 hx⟩

end Omega

namespace Data

variable {G : Type} [Group G] (d : Data G h)

@[expose] def CPI₂ : Subgroup G := d.pull (patSub h sI₂ isPattern_sI₂)

@[expose] def CPI₆ : Subgroup G := d.pull (patSub h sI₆ isPattern_sI₆)

theorem isSylowOf_N₂_inf_P [Finite G] : d.N₂ ⊓ d.P = d.CPI₂ ∧ IsSylowOf 2 d.CPI₂ d.N₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_antisymm ?_ (le_inf (d.pull_mono patSub_sI₂_le_N₂sub)
    (d.pull_mono (patSub_le_U _ _))), ?_⟩
  · rintro _ ⟨⟨n, hn, rfl⟩, hP⟩
    obtain ⟨u, hu, e⟩ := hP
    have hnu : n⁻¹ * u ∈ hypScalars h 2 1 :=
      (d.η_eq_one_iff _).1 (by rw [map_mul, map_inv, e, inv_mul_cancel])
    obtain ⟨c, -, hcm⟩ := exists_scalar_of_mem_hypScalars hnu
    have h1 : c = 1 := by
      have hu' : mat u = mat n * mat (n⁻¹ * u) := by rw [← mat_mul, mul_inv_cancel_left]
      have := congrFun (congrFun hu' ιe₁) ιe₁
      rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by
        rw [hcm, ite_eq_right hk, mul_zero]) (by simp), hcm, ite_eq_left rfl,
        U_diag hu, (N₂sub_rows hn _).1, one_apply_eq, one_mul] at this
      exact this.symm
    have h2 : n⁻¹ * u = 1 := by
      apply mat_injective
      ext a b
      rw [hcm, h1, mat_one, one_apply]
    have hun : u = n := by rw [← mul_inv_cancel_left n u, h2, mul_one]
    refine ⟨n, ?_, rfl⟩
    rw [← U_inf_N₂sub]
    exact ⟨hun ▸ hu, hn⟩
  · have hcardN : Nat.card d.N₂ = Nat.card (N₂sub h) :=
      (Nat.card_congr (d.pullEquiv N₂sub_inf_hypScalars).toEquiv).symm
    have hcardC : Nat.card d.CPI₂ = Nat.card (patSub h sI₂ isPattern_sI₂) :=
      d.card_pull (patSub_le_U _ _)
    refine CFSG.ABGLocalTools.isSylowOf_of_card (d.pull_mono patSub_sI₂_le_N₂sub) ?_
    rw [hcardC, hcardN, (isSylowOf_patSub_sI₂ (h := h)).card_eq]

theorem card_CPI₆ : Nat.card d.CPI₆ = 2 ^ f := by
  rw [CPI₆, d.card_pull (patSub_le_U _ _), card_patSub_sI₆]

theorem closure_involutions_CPI₂ :
    closure {x | x ∈ d.CPI₂ ∧ x * x = 1} = d.CPI₆ ∧ ∀ x ∈ d.CPI₆, ∀ y ∈ d.CPI₂, x * y = y * x := by
  refine ⟨?_, ?_⟩
  · have hset : {x | x ∈ d.CPI₂ ∧ x * x = 1} =
        d.η '' {x | x ∈ patSub h sI₂ isPattern_sI₂ ∧ x * x = 1} := by
      ext x
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hx2⟩
        refine ⟨u, ⟨hu, d.η_injOn (mul_mem (patSub_le_U _ _ hu) (patSub_le_U _ _ hu))
          (one_mem _) (by rw [map_mul, hx2, map_one])⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hu2⟩, rfl⟩
        exact ⟨⟨u, hu, rfl⟩, by rw [← map_mul, hu2, map_one]⟩
    rw [hset, ← MonoidHom.map_closure, closure_involutions_patSub_sI₂]
    rfl
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, patSub_sI₆_comm hx hy]

end Data

end CFSG.LocalAnalysis.EvenBN.U5
