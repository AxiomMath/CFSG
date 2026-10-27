module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSUCover

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm epsAct)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (rootVec posRoots negRoots
  mem_negRoots simpleRefl simpleRefl_mem simpleRefl_mul_self simpleRootVec
  simpleRootVec_mem_posRoots epsAct_neg epsAct_epsAct_inv IsSpReducedWord signed_descents
  exists_word_length_eq spLength_eq_invCount rootVec_mem_posRoots_iff simpleSnd
  rootVec_simpleSnd neg_rootVec epsAct_simpleRefl_simpleRootVec)
open Matrix
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem li_uRootMat_apply_diag (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (t : K) (x : HypIndex r ε) : uRootMat ε h a b t x x = 1 := by
  have h1 : ¬(lineCoord (ε := ε) a = x ∧ lineCoord (ε := ε) b = x) := fun hh =>
    hab (lineCoord_injective (hh.1.trans hh.2.symm))
  have h2 : ¬(lineCoord (ε := ε) b.swap = x ∧ lineCoord (ε := ε) a.swap = x) := fun hh => by
    have e : b.swap = a.swap := lineCoord_injective (hh.1.trans hh.2.symm)
    have e' := congrArg Sum.swap e
    rw [Sum.swap_swap, Sum.swap_swap] at e'
    exact hab e'.symm
  rw [uRootMat, Matrix.add_apply, one_apply_eq, uRootNil]
  split_ifs <;> simp [Matrix.single_apply, h1, h2]

theorem li_uRootSubgroup_le_U (h : UnitaryFieldData p f K) {α : Fin r → ℤ}
    (hα : α ∈ posRoots r) : uRootSubgroup ε h α ≤ hypUnitriangular h r ε := by
  refine iSup_le fun q => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := q
  rintro _ ⟨t, rfl⟩
  refine mem_hypUnitriangular.mpr ⟨?_, fun x => ?_⟩
  · change (uRootMat ε h a b t.toAdd).BlockTriangular fullPos
    exact uRootMat_blockTriangular h ((rootVec_mem_posRoots_iff hab).mp hα) _
  · change uRootMat ε h a b t.toAdd x x = 1
    exact li_uRootMat_apply_diag h hab _ x

theorem li_root_mem (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (t : uRootDom h a b) : uRootElt (ε := ε) h hab t ∈ uRootSubgroup ε h (rootVec a b) := by
  rw [uRootSubgroup_eq_range h hab]
  exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem li_neg_simple (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε)) (hU : hypUnitriangular h r ε ≤ A)
    (hn : ∀ k : Fin r, uWeylRep ε h k c hc ∈ A) (k : Fin r) :
    uRootSubgroup ε h (-simpleRootVec r k) ≤ A := by
  have hpos : uRootSubgroup ε h (simpleRootVec r k) ≤ A :=
    (li_uRootSubgroup_le_U h (simpleRootVec_mem_posRoots k)).trans hU
  have hmap := map_conj_uRootSubgroup (simpleRefl_mem k) (uWeylRep ε h k c hc)
    (isLinePerm_uWeylRep hc hc0 k) (simpleRootVec r k)
  rw [epsAct_simpleRefl_simpleRootVec] at hmap
  rw [← hmap]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem (hn k) (hpos hx)) (inv_mem (hn k))

theorem li_mem_traceZero (h : UnitaryFieldData p f K) {x : K} :
    x ∈ h.traceZero ↔ x + h.bar x = 0 := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]

abbrev li_succ (m : Fin r) (hm : (m : ℕ) + 1 < r) : Fin r := ⟨(m : ℕ) + 1, hm⟩

theorem li_ne_succ (m : Fin r) (hm : (m : ℕ) + 1 < r) : m ≠ li_succ m hm := by
  simp [li_succ, Fin.ext_iff]

theorem li_inl_ne_succ (m : Fin r) (hm : (m : ℕ) + 1 < r) :
    (Sum.inl m : Fin r ⊕ Fin r) ≠ Sum.inl (li_succ m hm) :=
  fun h' => li_ne_succ m hm (Sum.inl_injective h')

theorem li_hyp_ne_succ (m : Fin r) (hm : (m : ℕ) + 1 < r) :
    (Sum.inl m : HypIndex r ε) ≠ Sum.inl (li_succ m hm) :=
  fun h' => li_ne_succ m hm (Sum.inl_injective h')

theorem li_rootVec_short (m : Fin r) (hm : (m : ℕ) + 1 < r) :
    rootVec (Sum.inl m) (Sum.inl (li_succ m hm)) = simpleRootVec r m := by
  have := rootVec_simpleSnd m
  rw [simpleSnd_of_lt hm] at this
  exact this

theorem li_rootVec_short_neg (m : Fin r) (hm : (m : ℕ) + 1 < r) :
    rootVec (Sum.inl (li_succ m hm)) (Sum.inl m) = -simpleRootVec r m := by
  rw [← li_rootVec_short m hm, neg_rootVec]

theorem li_dom_short (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    s ∈ uRootDom h (Sum.inl m) (Sum.inl (li_succ m hm)) := by
  have hb : (Sum.inl (li_succ m hm) : Fin r ⊕ Fin r) ≠ (Sum.inl m).swap := by simp
  rw [uRootDom_of_ne h hb]
  exact AddSubgroup.mem_top s

theorem li_dom_short' (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    s ∈ uRootDom h (Sum.inl (li_succ m hm)) (Sum.inl m) := by
  have hb : (Sum.inl m : Fin r ⊕ Fin r) ≠ (Sum.inl (li_succ m hm)).swap := by simp
  rw [uRootDom_of_ne h hb]
  exact AddSubgroup.mem_top s

noncomputable def li_xS (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (s : K) : hypSU h r ε :=
  uRootElt (ε := ε) h (li_inl_ne_succ m hm) ⟨s, li_dom_short h m hm s⟩

noncomputable def li_yS (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (u : K) : hypSU h r ε :=
  uRootElt (ε := ε) h (li_inl_ne_succ m hm).symm ⟨u, li_dom_short' h m hm u⟩

noncomputable def li_nS (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (s : K) : hypSU h r ε :=
  li_xS h m hm s * li_yS h m hm (-s⁻¹) * li_xS h m hm s

theorem li_xS_mem (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    li_xS (ε := ε) h m hm s ∈ uRootSubgroup ε h (simpleRootVec r m) := by
  rw [← li_rootVec_short m hm]
  exact li_root_mem h (li_inl_ne_succ m hm) ⟨s, li_dom_short h m hm s⟩

theorem li_yS_mem (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K) :
    li_yS (ε := ε) h m hm u ∈ uRootSubgroup ε h (-simpleRootVec r m) := by
  rw [← li_rootVec_short_neg m hm]
  exact li_root_mem h (li_inl_ne_succ m hm).symm ⟨u, li_dom_short' h m hm u⟩

theorem li_rootVec_last (L : Fin r) (hL : ¬ ((L : ℕ) + 1 < r)) :
    rootVec (Sum.inl L) (Sum.inr L) = simpleRootVec r L := by
  have := rootVec_simpleSnd L
  have hs : simpleSnd L = Sum.inr L := by
    unfold simpleSnd
    rw [dif_neg hL]
  rw [hs] at this
  exact this

theorem li_rootVec_last_neg (L : Fin r) (hL : ¬ ((L : ℕ) + 1 < r)) :
    rootVec (Sum.inr L) (Sum.inl L) = -simpleRootVec r L := by
  rw [← li_rootVec_last L hL, neg_rootVec]

noncomputable def li_xL (h : UnitaryFieldData p f K) (L : Fin r) {s : K}
    (hs : s ∈ h.traceZero) : hypSU h r ε :=
  uRootElt (ε := ε) h (inl_ne_inr L) ⟨s, by
    rw [show (Sum.inr L : Fin r ⊕ Fin r) = (Sum.inl L).swap from rfl, uRootDom_swap]
    exact hs⟩

noncomputable def li_yL (h : UnitaryFieldData p f K) (L : Fin r) {u : K}
    (hu : u ∈ h.traceZero) : hypSU h r ε :=
  uRootElt (ε := ε) h (inl_ne_inr L).symm ⟨u, by
    rw [show (Sum.inl L : Fin r ⊕ Fin r) = (Sum.inr L).swap from rfl, uRootDom_swap]
    exact hu⟩

theorem li_xL_mem (h : UnitaryFieldData p f K) (L : Fin r) (hL : ¬ ((L : ℕ) + 1 < r)) {s : K}
    (hs : s ∈ h.traceZero) : li_xL (ε := ε) h L hs ∈ uRootSubgroup ε h (simpleRootVec r L) := by
  rw [← li_rootVec_last L hL]
  exact li_root_mem h (inl_ne_inr L) _

theorem li_yL_mem (h : UnitaryFieldData p f K) (L : Fin r) (hL : ¬ ((L : ℕ) + 1 < r)) {u : K}
    (hu : u ∈ h.traceZero) :
    li_yL (ε := ε) h L hu ∈ uRootSubgroup ε h (-simpleRootVec r L) := by
  rw [← li_rootVec_last_neg L hL]
  exact li_root_mem h (inl_ne_inr L).symm _

abbrev li_M {h : UnitaryFieldData p f K} (g : hypSU h r ε) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)

noncomputable def li_MS (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (s u : K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s

noncomputable def li_ML (h : UnitaryFieldData p f K) (L : Fin r) (s u : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  uRootMat ε h (Sum.inl L) (Sum.inr L) s * uRootMat ε h (Sum.inr L) (Sum.inl L) u *
    uRootMat ε h (Sum.inl L) (Sum.inr L) s

theorem li_mulVec3 (A B C : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (v : HypIndex r ε → K) : (A * B * C) *ᵥ v = A *ᵥ (B *ᵥ (C *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem li_X_act (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K)
    (x : HypIndex r ε) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = Sum.inl (li_succ m hm) then s • Pi.single (Sum.inl m : HypIndex r ε)
          1 else 0) -
        (if x = Sum.inr (Sum.inr m) then h.bar s • Pi.single (Sum.inr (Sum.inr (li_succ m hm)) :
            HypIndex r ε) 1
          else 0) := by
  have hb : (Sum.inl (li_succ m hm) : Fin r ⊕ Fin r) ≠ (Sum.inl m).swap := by simp
  exact uRootMat_mulVec_single h hb s x

theorem li_Y_act (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K)
    (x : HypIndex r ε) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = Sum.inl m then u • Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε)
          1 else 0) -
        (if x = Sum.inr (Sum.inr (li_succ m hm)) then h.bar u • Pi.single (Sum.inr (Sum.inr m) :
            HypIndex r ε) 1
          else 0) := by
  have hb : (Sum.inl m : Fin r ⊕ Fin r) ≠ (Sum.inl (li_succ m hm)).swap := by simp
  exact uRootMat_mulVec_single h hb u x

theorem li_XL_act (h : UnitaryFieldData p f K) (L : Fin r) (s : K) (x : HypIndex r ε) :
    uRootMat ε h (Sum.inl L) (Sum.inr L) s *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = Sum.inr (Sum.inr L) then s • Pi.single (Sum.inl L : HypIndex r ε) 1
          else 0) :=
  uRootMat_swap_mulVec_single h (Sum.inl L) s x

theorem li_YL_act (h : UnitaryFieldData p f K) (L : Fin r) (u : K) (x : HypIndex r ε) :
    uRootMat ε h (Sum.inr L) (Sum.inl L) u *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = Sum.inl L then u • Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1
          else 0) :=
  uRootMat_swap_mulVec_single h (Sum.inr L) u x

theorem li_X_m (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ
      Pi.single (Sum.inl m : HypIndex r ε) 1 = Pi.single (Sum.inl m : HypIndex r ε) 1 := by
  rw [li_X_act, if_neg (li_hyp_ne_succ m hm), if_neg Sum.inl_ne_inr, add_zero, sub_zero]

theorem li_X_s (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ
      Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 =
      Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 +
        s • Pi.single (Sum.inl m : HypIndex r ε) 1 := by
  rw [li_X_act, if_pos rfl, if_neg Sum.inl_ne_inr, sub_zero]

theorem li_X_F (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ
      Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 -
        h.bar s • Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 := by
  rw [li_X_act, if_neg Sum.inr_ne_inl, if_pos rfl, add_zero]

theorem li_X_FM (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ
      Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 := by
  rw [li_X_act, if_neg Sum.inr_ne_inl,
    if_neg (fun h' => li_ne_succ m hm (Sum.inr_injective (Sum.inr_injective h')).symm),
    add_zero, sub_zero]

theorem li_Y_m (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ
      Pi.single (Sum.inl m : HypIndex r ε) 1 =
      Pi.single (Sum.inl m : HypIndex r ε) 1 +
        u • Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 := by
  rw [li_Y_act, if_pos rfl, if_neg Sum.inl_ne_inr, sub_zero]

theorem li_Y_s (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ
      Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 =
      Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 := by
  rw [li_Y_act, if_neg (li_hyp_ne_succ m hm).symm, if_neg Sum.inl_ne_inr, add_zero, sub_zero]

theorem li_Y_F (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ
      Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 := by
  rw [li_Y_act, if_neg Sum.inr_ne_inl,
    if_neg (fun h' => li_ne_succ m hm (Sum.inr_injective (Sum.inr_injective h'))),
    add_zero, sub_zero]

theorem li_Y_FM (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ
      Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 -
        h.bar u • Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 := by
  rw [li_Y_act, if_neg Sum.inr_ne_inl, if_pos rfl, add_zero]

theorem li_X_gen (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s : K)
    (x : HypIndex r ε) (hx2 : x ≠ Sum.inl (li_succ m hm)) (hx3 : x ≠ Sum.inr (Sum.inr m)) :
    uRootMat ε h (Sum.inl m) (Sum.inl (li_succ m hm)) s *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [li_X_act, if_neg hx2, if_neg hx3, add_zero, sub_zero]

theorem li_Y_gen (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (u : K)
    (x : HypIndex r ε) (hx1 : x ≠ Sum.inl m) (hx4 : x ≠ Sum.inr (Sum.inr (li_succ m hm))) :
    uRootMat ε h (Sum.inl (li_succ m hm)) (Sum.inl m) u *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [li_Y_act, if_neg hx1, if_neg hx4, add_zero, sub_zero]

theorem li_XL_L (h : UnitaryFieldData p f K) (L : Fin r) (s : K) :
    uRootMat ε h (Sum.inl L) (Sum.inr L) s *ᵥ Pi.single (Sum.inl L : HypIndex r ε) 1 =
      Pi.single (Sum.inl L : HypIndex r ε) 1 := by
  rw [li_XL_act, if_neg Sum.inl_ne_inr, add_zero]

theorem li_XL_F (h : UnitaryFieldData p f K) (L : Fin r) (s : K) :
    uRootMat ε h (Sum.inl L) (Sum.inr L) s *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 +
        s • Pi.single (Sum.inl L : HypIndex r ε) 1 := by
  rw [li_XL_act, if_pos rfl]

theorem li_YL_L (h : UnitaryFieldData p f K) (L : Fin r) (u : K) :
    uRootMat ε h (Sum.inr L) (Sum.inl L) u *ᵥ Pi.single (Sum.inl L : HypIndex r ε) 1 =
      Pi.single (Sum.inl L : HypIndex r ε) 1 +
        u • Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 := by
  rw [li_YL_act, if_pos rfl]

theorem li_YL_F (h : UnitaryFieldData p f K) (L : Fin r) (u : K) :
    uRootMat ε h (Sum.inr L) (Sum.inl L) u *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 =
      Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 := by
  rw [li_YL_act, if_neg Sum.inr_ne_inl, add_zero]

theorem li_XL_gen (h : UnitaryFieldData p f K) (L : Fin r) (s : K) (x : HypIndex r ε)
    (hx : x ≠ Sum.inr (Sum.inr L)) :
    uRootMat ε h (Sum.inl L) (Sum.inr L) s *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [li_XL_act, if_neg hx, add_zero]

theorem li_YL_gen (h : UnitaryFieldData p f K) (L : Fin r) (u : K) (x : HypIndex r ε)
    (hx : x ≠ Sum.inl L) :
    uRootMat ε h (Sum.inr L) (Sum.inl L) u *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [li_YL_act, if_neg hx, add_zero]

theorem li_MS_col_m (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) {s u : K}
    (hsu : s * u = -1) :
    li_MS (ε := ε) h m hm s u *ᵥ Pi.single (Sum.inl m : HypIndex r ε) 1 =
      u • Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 := by
  have hus : u * s = -1 := by rw [mul_comm]; exact hsu
  unfold li_MS
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, li_X_m, li_X_s, li_Y_m, li_Y_s, smul_add,
    smul_smul, hsu, hus]
  module

theorem li_MS_col_succ (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) {s u : K}
    (hsu : s * u = -1) :
    li_MS (ε := ε) h m hm s u *ᵥ Pi.single (Sum.inl (li_succ m hm) : HypIndex r ε) 1 =
      s • Pi.single (Sum.inl m : HypIndex r ε) 1 := by
  have hus : u * s = -1 := by rw [mul_comm]; exact hsu
  unfold li_MS
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, li_X_m, li_X_s, li_Y_m, li_Y_s, smul_add,
    smul_smul, hsu, hus]
  module

theorem li_MS_col_FL (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) {s u : K}
    (hsu : s * u = -1) :
    li_MS (ε := ε) h m hm s u *ᵥ Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 =
      (-h.bar s) • Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 := by
  have hbsu : h.bar s * h.bar u = -1 := by rw [← map_mul, hsu, map_neg, map_one]
  unfold li_MS
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, li_X_F, li_X_FM,
    li_Y_F, li_Y_FM, smul_add, smul_sub, smul_smul, hbsu]
  module

theorem li_MS_col_FM (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) {s u : K}
    (hsu : s * u = -1) :
    li_MS (ε := ε) h m hm s u *ᵥ Pi.single (Sum.inr (Sum.inr (li_succ m hm)) : HypIndex r ε) 1 =
      (-h.bar u) • Pi.single (Sum.inr (Sum.inr m) : HypIndex r ε) 1 := by
  have hbsu : h.bar u * h.bar s = -1 := by rw [← map_mul, mul_comm, hsu, map_neg, map_one]
  unfold li_MS
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, li_X_F, li_X_FM,
    li_Y_F, li_Y_FM, smul_add, smul_sub, smul_smul, hbsu]
  module

theorem li_MS_col_gen (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) (s u : K)
    (x : HypIndex r ε) (hx1 : x ≠ Sum.inl m) (hx2 : x ≠ Sum.inl (li_succ m hm))
    (hx3 : x ≠ Sum.inr (Sum.inr m)) (hx4 : x ≠ Sum.inr (Sum.inr (li_succ m hm))) :
    li_MS (ε := ε) h m hm s u *ᵥ Pi.single x 1 = Pi.single x 1 := by
  unfold li_MS
  rw [li_mulVec3, li_X_gen h m hm s x hx2 hx3, li_Y_gen h m hm u x hx1 hx4,
    li_X_gen h m hm s x hx2 hx3]

theorem li_ML_col_L (h : UnitaryFieldData p f K) (L : Fin r) {s u : K} (hsu : s * u = -1) :
    li_ML (ε := ε) h L s u *ᵥ Pi.single (Sum.inl L : HypIndex r ε) 1 =
      u • Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 := by
  have hus : u * s = -1 := by rw [mul_comm]; exact hsu
  unfold li_ML
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, li_XL_L, li_XL_F, li_YL_L, li_YL_F,
    smul_add, smul_smul, hsu, hus]
  module

theorem li_ML_col_FL (h : UnitaryFieldData p f K) (L : Fin r) {s u : K} (hsu : s * u = -1) :
    li_ML (ε := ε) h L s u *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r ε) 1 =
      s • Pi.single (Sum.inl L : HypIndex r ε) 1 := by
  have hus : u * s = -1 := by rw [mul_comm]; exact hsu
  unfold li_ML
  rw [li_mulVec3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, li_XL_L, li_XL_F, li_YL_L, li_YL_F,
    smul_add, smul_smul, hsu, hus]
  module

theorem li_ML_col_gen (h : UnitaryFieldData p f K) (L : Fin r) (s u : K) (x : HypIndex r ε)
    (hx1 : x ≠ Sum.inl L) (hx2 : x ≠ Sum.inr (Sum.inr L)) :
    li_ML (ε := ε) h L s u *ᵥ Pi.single x 1 = Pi.single x 1 := by
  unfold li_ML
  rw [li_mulVec3, li_XL_gen h L s x hx2, li_YL_gen h L u x hx1, li_XL_gen h L s x hx2]

noncomputable def li_eS (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (s : K) : HypIndex r ε → K := fun x =>
  if x = Sum.inl m then s
  else if x = Sum.inl (li_succ m hm) then s⁻¹
  else if x = Sum.inr (Sum.inr m) then (h.bar s)⁻¹
  else if x = Sum.inr (Sum.inr (li_succ m hm)) then h.bar s
  else 1

noncomputable def li_eL (h : UnitaryFieldData p f K) (L : Fin r) (t : K) :
    HypIndex r ε → K := fun x =>
  if x = Sum.inl L then t
  else if x = Sum.inr (Sum.inr L) then t⁻¹
  else 1

theorem li_diag_basis (e : HypIndex r ε → K) (y : HypIndex r ε) :
    diagonal e *ᵥ Pi.single y 1 = e y • Pi.single y 1 := by
  funext z
  rw [Matrix.mulVec_diagonal]
  by_cases hz : z = y
  · subst hz; simp
  · simp [hz]

theorem li_short_matrix (h : UnitaryFieldData p f K) (m : Fin r) (hm : (m : ℕ) + 1 < r) {s : K}
    (hs : s ≠ 0) :
    li_MS (ε := ε) h m hm s (-s⁻¹) = diagonal (li_eS (ε := ε) h m hm s) * li_MS (ε := ε) h m hm 1
        (-(1 : K)⁻¹) := by
  have hsu : s * (-s⁻¹) = -1 := by field_simp
  have hN : (1 : K) * (-(1 : K)⁻¹) = -1 := by simp
  have hcol : ∀ j : HypIndex r ε, li_MS (ε := ε) h m hm s (-s⁻¹) *ᵥ Pi.single j 1 =
      (diagonal (li_eS (ε := ε) h m hm s) * li_MS (ε := ε) h m hm 1 (-(1 : K)⁻¹)) *ᵥ Pi.single j 1
          := by
    intro j
    rw [← Matrix.mulVec_mulVec]
    by_cases h1 : j = Sum.inl m
    · subst h1
      rw [li_MS_col_m h m hm hsu, li_MS_col_m h m hm hN, Matrix.mulVec_smul, li_diag_basis,
        smul_smul]
      congr 1
      simp [li_eS, li_hyp_ne_succ m hm, (li_hyp_ne_succ m hm).symm] <;> ring
    by_cases h2 : j = Sum.inl (li_succ m hm)
    · subst h2
      rw [li_MS_col_succ h m hm hsu, li_MS_col_succ h m hm hN, Matrix.mulVec_smul,
        li_diag_basis, smul_smul]
      congr 1
      simp [li_eS, li_hyp_ne_succ m hm, (li_hyp_ne_succ m hm).symm]
    by_cases h3 : j = Sum.inr (Sum.inr m)
    · subst h3
      rw [li_MS_col_FL h m hm hsu, li_MS_col_FL h m hm hN, Matrix.mulVec_smul, li_diag_basis,
        smul_smul]
      congr 1
      simp [li_eS, li_hyp_ne_succ m hm, (li_hyp_ne_succ m hm).symm, li_ne_succ m hm,
        (li_ne_succ m hm).symm] <;> ring
    by_cases h4 : j = Sum.inr (Sum.inr (li_succ m hm))
    · subst h4
      rw [li_MS_col_FM h m hm hsu, li_MS_col_FM h m hm hN, Matrix.mulVec_smul, li_diag_basis,
        smul_smul]
      congr 1
      simp [li_eS, li_hyp_ne_succ m hm, (li_hyp_ne_succ m hm).symm, li_ne_succ m hm,
        (li_ne_succ m hm).symm] <;> ring
    rw [li_MS_col_gen h m hm s _ j h1 h2 h3 h4, li_MS_col_gen h m hm 1 _ j h1 h2 h3 h4,
      li_diag_basis]
    simp [li_eS, h1, h2, h3, h4]
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (hcol j) i

theorem li_long_matrix (h : UnitaryFieldData p f K) (L : Fin r) {c t : K} (hc0 : c ≠ 0)
    (ht : t ≠ 0) :
    li_ML (ε := ε) h L (-(t * c⁻¹)) (-(-(t * c⁻¹))⁻¹) = diagonal (li_eL (ε := ε) h L t) * li_ML (ε
        := ε) h L (-c⁻¹) c := by
  have hsu : (-(t * c⁻¹)) * (-(-(t * c⁻¹))⁻¹) = -1 := by field_simp
  have hsu0 : (-c⁻¹) * c = -1 := by field_simp
  have hcol : ∀ j : HypIndex r ε, li_ML (ε := ε) h L (-(t * c⁻¹)) (-(-(t * c⁻¹))⁻¹) *ᵥ Pi.single j
      1 =
      (diagonal (li_eL (ε := ε) h L t) * li_ML (ε := ε) h L (-c⁻¹) c) *ᵥ Pi.single j 1 := by
    intro j
    rw [← Matrix.mulVec_mulVec]
    by_cases h1 : j = Sum.inl L
    · subst h1
      rw [li_ML_col_L h L hsu, li_ML_col_L h L hsu0, Matrix.mulVec_smul, li_diag_basis,
        smul_smul]
      congr 1
      simp [li_eL] <;> ring
    by_cases h2 : j = Sum.inr (Sum.inr L)
    · subst h2
      rw [li_ML_col_FL h L hsu, li_ML_col_FL h L hsu0, Matrix.mulVec_smul, li_diag_basis,
        smul_smul]
      congr 1
      simp [li_eL] <;> ring
    rw [li_ML_col_gen h L _ _ j h1 h2, li_ML_col_gen h L _ _ j h1 h2, li_diag_basis]
    simp [li_eL, h1, h2]
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (hcol j) i

theorem li_M_mul_inv (h : UnitaryFieldData p f K) (g : hypSU h r ε) :
    li_M g * li_M g⁻¹ = 1 := by
  unfold li_M
  rw [Subgroup.coe_inv]
  exact Units.mul_inv ((g : GL (HypIndex r ε) K))

theorem li_M_uWeyl_last (h : UnitaryFieldData p f K) (L : Fin r) (hL : ¬ ((L : ℕ) + 1 < r))
    {c : K} (hc : c ∈ h.traceZero) :
    li_M (uWeylRep ε h L c hc) = li_ML (ε := ε) h L (-c⁻¹) c := by
  unfold uWeylRep
  rw [dif_neg hL]
  rfl

theorem li_mem_torus_of_diag (h : UnitaryFieldData p f K) (g : hypSU h r ε)
    (e : HypIndex r ε → K) (hg : li_M g = diagonal e) (he : ∀ x, e x ≠ 0) :
    g ∈ hypTorus h r ε := by
  apply mem_hypTorus_of_isLinePerm
  change IsLinePerm 1 (li_M g)
  rw [hg]
  intro x y
  rw [diagonal_apply, Equiv.Perm.one_apply]
  by_cases hyx : y = x
  · subst hyx
    simp [he y]
  · simp [hyx]

theorem li_torus_diag (h : UnitaryFieldData p f K) {t : hypSU h r ε}
    (ht : t ∈ hypTorus h r ε) :
    ∃ e : HypIndex r ε → K, li_M t = diagonal e ∧ ∀ x, e x ≠ 0 := by
  obtain ⟨a, d, -, -, hg⟩ := ht
  refine ⟨torusEntries h a d, hg, fun x => ?_⟩
  rcases x with i | k | i
  · exact (a i).ne_zero
  · exact (d k).ne_zero
  · exact inv_ne_zero ((map_ne_zero h.bar).mpr (a i).ne_zero)

theorem li_mul_entry (h : UnitaryFieldData p f K) {t g : hypSU h r ε}
    (ht : t ∈ hypTorus h r ε) (hg : g ∈ hypTorus h r ε) (x : HypIndex r ε) :
    li_M (t * g) x x = li_M t x x * li_M g x x := by
  obtain ⟨e, he, -⟩ := li_torus_diag h ht
  obtain ⟨e', he', -⟩ := li_torus_diag h hg
  change (li_M t * li_M g) x x = _
  rw [he, he']
  simp [Matrix.diagonal_mul_diagonal]

theorem li_inv_entry (h : UnitaryFieldData p f K) {g : hypSU h r ε}
    (hg : g ∈ hypTorus h r ε) (x : HypIndex r ε) :
    li_M g⁻¹ x x = (li_M g x x)⁻¹ := by
  obtain ⟨e, he, he0⟩ := li_torus_diag h hg
  have hmul := li_M_mul_inv h g
  rw [he] at hmul ⊢
  have := congrFun (congrFun hmul x) x
  simp [Matrix.diagonal_mul] at this
  rw [Matrix.diagonal_apply_eq]
  exact eq_inv_of_mul_eq_one_right this

theorem li_short_coroot (h : UnitaryFieldData p f K) (A : Subgroup (hypSU h r ε))
    (m : Fin r) (hm : (m : ℕ) + 1 < r)
    (hpos : uRootSubgroup ε h (simpleRootVec r m) ≤ A)
    (hneg : uRootSubgroup ε h (-simpleRootVec r m) ≤ A) {s : K} (hs : s ≠ 0) :
    ∃ g ∈ A, g ∈ hypTorus h r ε ∧ li_M g (Sum.inl m) (Sum.inl m) = s ∧
      ∀ i : Fin r, (i : ℕ) < m → li_M g (Sum.inl i) (Sum.inl i) = 1 := by
  have hn : ∀ t : K, li_nS (ε := ε) h m hm t ∈ A := fun t =>
    mul_mem (mul_mem (hpos (li_xS_mem h m hm t)) (hneg (li_yS_mem h m hm (-t⁻¹))))
      (hpos (li_xS_mem h m hm t))
  have hN1 : li_MS (ε := ε) h m hm 1 (-(1 : K)⁻¹) = li_M (li_nS h m hm 1) := rfl
  have hM : li_M (li_nS h m hm s * (li_nS h m hm 1)⁻¹) = diagonal (li_eS (ε := ε) h m hm s) := by
    rw [show li_M (li_nS h m hm s * (li_nS h m hm 1)⁻¹) =
        li_M (li_nS h m hm s) * li_M (li_nS h m hm 1)⁻¹ from rfl,
      show li_M (li_nS h m hm s) = li_MS (ε := ε) h m hm s (-s⁻¹) from rfl,
      li_short_matrix h m hm hs, hN1, mul_assoc, li_M_mul_inv, mul_one]
  have hbs : h.bar s ≠ 0 := (map_ne_zero h.bar).mpr hs
  have he0 : ∀ x, li_eS (ε := ε) h m hm s x ≠ 0 := by
    intro x
    unfold li_eS
    split_ifs <;> simp [hs, hbs]
  refine ⟨li_nS h m hm s * (li_nS h m hm 1)⁻¹, mul_mem (hn s) (inv_mem (hn 1)),
    li_mem_torus_of_diag h _ _ hM he0, ?_, ?_⟩
  · rw [hM]
    simp [li_eS]
  · intro i hi
    have hne1 : i ≠ m := fun h' => by
      rw [h'] at hi
      exact lt_irrefl _ hi
    have hne2 : i ≠ li_succ m hm := fun h' => by
      have := congrArg Fin.val h'
      simp [li_succ] at this
      omega
    rw [hM]
    simp [li_eS, hne1, hne2]

theorem li_factor (h : UnitaryFieldData p f K) (A : Subgroup (hypSU h r ε)) (hr : 1 ≤ r)
    (hshort : ∀ (m : Fin r) (hm : (m : ℕ) + 1 < r) {s : K}, s ≠ 0 →
      ∃ g ∈ A, g ∈ hypTorus h r ε ∧ li_M g (Sum.inl m) (Sum.inl m) = s ∧
        ∀ i : Fin r, (i : ℕ) < m → li_M g (Sum.inl i) (Sum.inl i) = 1)
    (hbase : ∀ t ∈ hypTorus h r ε,
      (∀ i : Fin r, (i : ℕ) < r - 1 → li_M t (Sum.inl i) (Sum.inl i) = 1) → t ∈ A) :
    hypTorus h r ε ≤ A := by
  have key : ∀ j m : ℕ, m + j + 1 = r → ∀ t ∈ hypTorus h r ε,
      (∀ i : Fin r, (i : ℕ) < m → li_M t (Sum.inl i) (Sum.inl i) = 1) → t ∈ A := by
    intro j
    induction j with
    | zero =>
      intro m hm t ht hent
      exact hbase t ht fun i hi => hent i (by omega)
    | succ j ih =>
      intro m hm t ht hent
      have hmr : m < r := by omega
      have hm1 : m + 1 < r := by omega
      obtain ⟨e, he, he0⟩ := li_torus_diag h ht
      have hs0 : li_M t (Sum.inl ⟨m, hmr⟩) (Sum.inl ⟨m, hmr⟩) ≠ 0 := by
        rw [he, Matrix.diagonal_apply_eq]
        exact he0 _
      obtain ⟨g, hgA, hgT, hgm, hgl⟩ := hshort ⟨m, hmr⟩ hm1 hs0
      have ht' : t * g⁻¹ ∈ hypTorus h r ε := mul_mem ht (inv_mem hgT)
      have hent' : ∀ i : Fin r, (i : ℕ) < m + 1 → li_M (t * g⁻¹) (Sum.inl i) (Sum.inl i) = 1 := by
        intro i hi
        rw [li_mul_entry h ht (inv_mem hgT), li_inv_entry h hgT]
        rcases Nat.lt_or_ge (i : ℕ) m with hlt | hge
        · rw [hent i hlt, hgl i hlt]
          simp
        · have hieq : i = ⟨m, hmr⟩ := Fin.ext (by simp; omega)
          subst hieq
          rw [hgm]
          exact mul_inv_cancel₀ hs0
      have hA' : t * g⁻¹ ∈ A := ih (m + 1) (by omega) (t * g⁻¹) ht' hent'
      have := mul_mem hA' hgA
      rwa [inv_mul_cancel_right] at this
  intro t ht
  exact key (r - 1) 0 (by omega) t ht (fun i hi => absurd hi (Nat.not_lt_zero _))

theorem li_base0 (h : UnitaryFieldData p f K) (L : Fin r) (hL : (L : ℕ) + 1 = r)
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r 0))
    (hA : uRootSubgroup 0 h (simpleRootVec r L) ≤ A)
    (hB : uRootSubgroup 0 h (-simpleRootVec r L) ≤ A)
    (hW : uWeylRep 0 h L c hc ∈ A) :
    ∀ t ∈ hypTorus h r 0, (∀ i : Fin r, (i : ℕ) < r - 1 → li_M t (Sum.inl i) (Sum.inl i) = 1) →
      t ∈ A := by
  intro t ht hent
  have hLr : ¬ ((L : ℕ) + 1 < r) := by omega
  obtain ⟨a, d, -, hp, hg⟩ := ht
  have ha : ∀ i : Fin r, i ≠ L → a i = 1 := by
    intro i hi
    have hlt : (i : ℕ) < r - 1 := by
      have h1 : (i : ℕ) ≠ (L : ℕ) := fun h' => hi (Fin.ext h')
      have h2 := i.2
      omega
    have h3 := hent i hlt
    rw [show li_M t = diagonal (torusEntries h a d) from hg, Matrix.diagonal_apply_eq] at h3
    exact Units.val_eq_one.mp h3
  have hratio : (a L : K) / h.bar (a L) = 1 := by
    have hp' : (∏ i : Fin r, (a i : K) / h.bar (a i)) = 1 := by
      simpa [torusRatio] using hp
    rw [Finset.prod_eq_single L (fun i _ hi => by simp [ha i hi])
      (fun hL' => absurd (Finset.mem_univ L) hL')] at hp'
    exact hp'
  have hbar : (a L : K) = h.bar (a L) :=
    (div_eq_one_iff_eq ((map_ne_zero h.bar).mpr (a L).ne_zero)).mp hratio
  set lam : K := (a L : K) with hlam_def
  have hlam0 : lam ≠ 0 := (a L).ne_zero
  have hbc : h.bar c = -c := by
    have := (li_mem_traceZero h).mp hc
    linear_combination this
  have hstr : -(lam * c⁻¹) ∈ h.traceZero := by
    rw [li_mem_traceZero, map_neg, map_mul, map_inv₀, hbc, ← hbar]
    ring
  have hu : -(-(lam * c⁻¹))⁻¹ ∈ h.traceZero := neg_mem (inv_mem_traceZero hstr)
  have hX : li_xL (ε := 0) h L hstr ∈ A := hA (li_xL_mem (ε := 0) h L hLr hstr)
  have hY : li_yL (ε := 0) h L hu ∈ A := hB (li_yL_mem (ε := 0) h L hLr hu)
  have hDA : li_xL (ε := 0) h L hstr * li_yL (ε := 0) h L hu * li_xL (ε := 0) h L hstr *
      (uWeylRep 0 h L c hc)⁻¹ ∈ A :=
    mul_mem (mul_mem (mul_mem hX hY) hX) (inv_mem hW)
  have hLM : li_ML (ε := 0) h L (-(lam * c⁻¹)) (-(-(lam * c⁻¹))⁻¹) =
      diagonal (li_eL (ε := 0) h L lam) * li_M (uWeylRep 0 h L c hc) := by
    rw [li_long_matrix h L hc0 hlam0, li_M_uWeyl_last h L hLr hc]
  have hDM : li_M (li_xL (ε := 0) h L hstr * li_yL (ε := 0) h L hu *
      li_xL (ε := 0) h L hstr * (uWeylRep 0 h L c hc)⁻¹) = diagonal (li_eL (ε := 0) h L lam) := by
    show li_ML (ε := 0) h L (-(lam * c⁻¹)) (-(-(lam * c⁻¹))⁻¹) * li_M (uWeylRep 0 h L c hc)⁻¹ = _
    rw [hLM, mul_assoc, li_M_mul_inv, mul_one]
  have hEq : t = li_xL (ε := 0) h L hstr * li_yL (ε := 0) h L hu *
      li_xL (ε := 0) h L hstr * (uWeylRep 0 h L c hc)⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    refine (hg.trans ?_).trans hDM.symm
    congr 1
    funext x
    rcases x with i | k | i
    · by_cases hi : i = L
      · rw [hi]
        simp [torusEntries, li_eL, ← hlam_def]
      · simp [torusEntries, li_eL, hi, ha i hi]
    · exact Fin.elim0 k
    · by_cases hi : i = L
      · rw [hi]
        simp [torusEntries, li_eL, ← hlam_def, ← hbar]
      · simp [torusEntries, li_eL, hi, ha i hi]
  rw [hEq]
  exact hDA

def li_middle : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (r : ℕ) (c : K)
    (hc : c ∈ h.traceZero), c ≠ 0 → ∀ A : Subgroup (hypSU h r 1), 2 ≤ r →
      hypUnitriangular h r 1 ≤ A → (∀ k : Fin r, uWeylRep 1 h k c hc ∈ A) →
      ∀ (a : Fin r → Kˣ) (d : Fin 1 → Kˣ), (∀ i : Fin r, (i : ℕ) < r - 1 → a i = 1) →
        (∀ k, h.norm (d k : K) = 1) → torusRatio h a d = 1 →
        ∃ g ∈ A, ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
          diagonal (torusEntries h a d)

theorem li_short_all (h : UnitaryFieldData p f K) (A : Subgroup (hypSU h r ε)) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (hU : hypUnitriangular h r ε ≤ A)
    (hn : ∀ k : Fin r, uWeylRep ε h k c hc ∈ A) :
    ∀ (m : Fin r) (hm : (m : ℕ) + 1 < r) {s : K}, s ≠ 0 →
      ∃ g ∈ A, g ∈ hypTorus h r ε ∧ li_M g (Sum.inl m) (Sum.inl m) = s ∧
        ∀ i : Fin r, (i : ℕ) < m → li_M g (Sum.inl i) (Sum.inl i) = 1 := fun m hm {s} hs =>
  li_short_coroot h A m hm
    ((li_uRootSubgroup_le_U h (simpleRootVec_mem_posRoots m)).trans hU)
    (li_neg_simple h hc hc0 A hU hn m) hs

theorem li_torus_eps0 (h : UnitaryFieldData p f K) (r : ℕ) (hr : 2 ≤ r) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r 0))
    (hU : hypUnitriangular h r 0 ≤ A) (hn : ∀ k : Fin r, uWeylRep 0 h k c hc ∈ A) :
    hypTorus h r 0 ≤ A := by
  have hL : ((⟨r - 1, by omega⟩ : Fin r) : ℕ) + 1 = r := by
    simp only
    omega
  refine li_factor h A (by omega) (li_short_all h A hc hc0 hU hn) ?_
  refine li_base0 h ⟨r - 1, by omega⟩ hL hc hc0 A ?_ ?_ (hn _)
  · exact (li_uRootSubgroup_le_U h (simpleRootVec_mem_posRoots _)).trans hU
  · exact li_neg_simple h hc hc0 A hU hn _

theorem psuTorusOvergroup_of_middle (hmid : li_middle) : PSUTorusOvergroup := by
  intro f K _ h r ε hr hε c hc hc0 A hU hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exact li_torus_eps0 h r hr hc hc0 A hU hn
  · refine li_factor h A (by omega) (li_short_all h A hc hc0 hU hn) ?_
    intro t ht hent
    obtain ⟨a, d, hd, hp, hg⟩ := ht
    have ha : ∀ i : Fin r, (i : ℕ) < r - 1 → a i = 1 := fun i hi => by
      have h3 := hent i hi
      rw [show li_M t = diagonal (torusEntries h a d) from hg, Matrix.diagonal_apply_eq] at h3
      exact Units.val_eq_one.mp h3
    obtain ⟨g, hgA, hgeq⟩ := hmid f K h r c hc hc0 A hr hU hn a d ha hd hp
    have hEq : t = g := by
      apply Subtype.ext
      apply Units.ext
      exact hg.trans hgeq.symm
    rw [hEq]
    exact hgA

@[expose] noncomputable def lmN (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a -
    single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) (h.bar a) +
    single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) b

@[expose] noncomputable def lmX (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  1 + lmN h L a b

@[expose] noncomputable def lmY (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  1 + (single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inl L : HypIndex r 1) (-h.bar a) +
    single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inl L : HypIndex r 1) b +
    single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a)

theorem lmX_e (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmX h L a b *ᵥ Pi.single (Sum.inl L : HypIndex r 1) 1 = Pi.single (Sum.inl L) 1 := by
  simp [-Matrix.mulVec_single, lmX, lmN, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply]

theorem lmX_z (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmX h L a b *ᵥ Pi.single (Sum.inr (Sum.inl 0) : HypIndex r 1) 1 =
      Pi.single (Sum.inr (Sum.inl 0)) 1 + a • Pi.single (Sum.inl L) 1 := by
  simp [-Matrix.mulVec_single, lmX, lmN, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply]

theorem lmX_f (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmX h L a b *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r 1) 1 =
      Pi.single (Sum.inr (Sum.inr L)) 1 + b • Pi.single (Sum.inl L) 1 -
        h.bar a • Pi.single (Sum.inr (Sum.inl 0)) 1 := by
  simp [-Matrix.mulVec_single, lmX, lmN, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply]
  abel

theorem lmX_gen (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) (y : HypIndex r 1)
    (h1 : y ≠ Sum.inl L) (h2 : y ≠ Sum.inr (Sum.inl 0)) (h3 : y ≠ Sum.inr (Sum.inr L)) :
    lmX h L a b *ᵥ Pi.single y 1 = Pi.single y 1 := by
  simp [-Matrix.mulVec_single, lmX, lmN, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.single_mulVec_eq, Pi.single_apply, h1, h2, h3, h1.symm, h2.symm, h3.symm]

theorem lmY_e (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmY h L a b *ᵥ Pi.single (Sum.inl L : HypIndex r 1) 1 =
      Pi.single (Sum.inl L) 1 + (-h.bar a) • Pi.single (Sum.inr (Sum.inl 0)) 1 +
        b • Pi.single (Sum.inr (Sum.inr L)) 1 := by
  simp [-Matrix.mulVec_single, lmY, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply]
  abel

theorem lmY_z (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmY h L a b *ᵥ Pi.single (Sum.inr (Sum.inl 0) : HypIndex r 1) 1 =
      Pi.single (Sum.inr (Sum.inl 0)) 1 + a • Pi.single (Sum.inr (Sum.inr L)) 1 := by
  simp [-Matrix.mulVec_single, lmY, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply]

theorem lmY_f (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    lmY h L a b *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r 1) 1 =
      Pi.single (Sum.inr (Sum.inr L)) 1 := by
  simp [-Matrix.mulVec_single, lmY, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply]

theorem lmY_gen (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) (y : HypIndex r 1)
    (h1 : y ≠ Sum.inl L) (h2 : y ≠ Sum.inr (Sum.inl 0)) (h3 : y ≠ Sum.inr (Sum.inr L)) :
    lmY h L a b *ᵥ Pi.single y 1 = Pi.single y 1 := by
  simp [-Matrix.mulVec_single, lmY, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    Pi.single_apply, h1, h2, h3, h1.symm, h2.symm, h3.symm]

theorem lm_eq_of_mulVec {M N : Matrix (HypIndex r 1) (HypIndex r 1) K}
    (hv : ∀ y : HypIndex r 1, M *ᵥ Pi.single y 1 = N *ᵥ Pi.single y 1) : M = N := by
  ext i j
  have := congrFun (hv j) i
  simpa [Matrix.mulVec_single_one] using this

theorem lmN_upper (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) (x y : HypIndex r 1)
    (hxy : lmN h L a b x y ≠ 0) : fullPos x < fullPos y := by
  have hL := L.2
  rw [lmN, Matrix.add_apply, Matrix.sub_apply] at hxy
  by_cases hC : single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) b x y = 0
  · rw [hC, add_zero] at hxy
    by_cases hB : single (Sum.inr (Sum.inl 0) : HypIndex r 1)
        (Sum.inr (Sum.inr L) : HypIndex r 1) (h.bar a) x y = 0
    · rw [hB, sub_zero] at hxy
      obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hxy
      simp only [fullPos_inl, fullPos_inr_inl]
      omega
    · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hB
      simp only [fullPos_inr_inl, fullPos_inr_inr]
      omega
  · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hC
    simp only [fullPos_inl, fullPos_inr_inr]
    omega

theorem lmX_gram (h : UnitaryFieldData p f K) (L : Fin r) {a b : K}
    (hab : b + h.bar b + a * h.bar a = 0) :
    ((lmX h L a b).map h.bar)ᵀ * hypGram r 1 K * lmX h L a b = hypGram r 1 K := by
  have hez : (Sum.inl L : HypIndex r 1) ≠ Sum.inr (Sum.inl 0) := by simp
  have hzf : (Sum.inr (Sum.inl 0) : HypIndex r 1) ≠ Sum.inr (Sum.inr L) := by simp
  have hef : (Sum.inl L : HypIndex r 1) ≠ Sum.inr (Sum.inr L) := by simp
  unfold lmX
  set N := lmN h L a b with hN
  have hT : ((1 + N).map h.bar)ᵀ = 1 + (N.map h.bar)ᵀ := by
    rw [Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      transpose_add, transpose_one]
  have hexp : (1 + (N.map h.bar)ᵀ) * hypGram r 1 K * (1 + N) = hypGram r 1 K +
      ((N.map h.bar)ᵀ * hypGram r 1 K + hypGram r 1 K * N) +
      (N.map h.bar)ᵀ * hypGram r 1 K * N := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNs : (N.map h.bar)ᵀ = single (Sum.inr (Sum.inl 0) : HypIndex r 1)
      (Sum.inl L : HypIndex r 1) (h.bar a) -
      single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a +
      single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inl L : HypIndex r 1) (h.bar b) := by
    rw [hN, lmN, Matrix.map_add _ (map_add h.bar), Matrix.map_sub _ (map_sub h.bar),
      transpose_add, transpose_sub, UnitaryHigher.conjTranspose_single,
      UnitaryHigher.conjTranspose_single, UnitaryHigher.conjTranspose_single, h.bar_bar]
  have h1 : (N.map h.bar)ᵀ * hypGram r 1 K + hypGram r 1 K * N =
      single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (h.bar b + b) := by
    rw [hNs, hN, lmN, single_add]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      single_mul_hypGram, hypGram_mul_single, hypPartner_inl, hypPartner_inr_inl,
      hypPartner_inr_inr]
    abel
  have h2 : (N.map h.bar)ᵀ * hypGram r 1 K * N =
      single (Sum.inr (Sum.inr L) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (a * h.bar a) := by
    rw [hNs, hN, lmN]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      single_mul_hypGram, hypGram_mul_single, hypPartner_inl, hypPartner_inr_inl,
      hypPartner_inr_inr]
    simp [single_mul_single_same, single_mul_single_of_ne, hez, hzf, hef, hez.symm, hzf.symm,
      hef.symm]
  rw [hT, hexp, h1, h2, add_assoc, ← single_add,
    show h.bar b + b + a * h.bar a = 0 by linear_combination hab, single_zero, add_zero]

theorem lmX_det (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    (lmX h L a b).det = 1 := by
  have hez : (Sum.inl L : HypIndex r 1) ≠ Sum.inr (Sum.inl 0) := by simp
  have hzf : (Sum.inr (Sum.inl 0) : HypIndex r 1) ≠ Sum.inr (Sum.inr L) := by simp
  have hef : (Sum.inl L : HypIndex r 1) ≠ Sum.inr (Sum.inr L) := by simp
  have h12 : transvection (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a *
      transvection (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (-h.bar a) =
      1 + (single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a +
        single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
          (-h.bar a) + single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
          (a * -h.bar a)) := by
    rw [transvection, transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, single_mul_single_same]
    abel
  have hAC : (single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a +
      single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) (-h.bar a) +
      single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) (a * -h.bar a)) *
      single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) (b + a * h.bar a) =
      0 := by
    rw [Matrix.add_mul, Matrix.add_mul, single_mul_single_of_ne _ _ _ _ hez.symm,
      single_mul_single_of_ne _ _ _ _ hef.symm, single_mul_single_of_ne _ _ _ _ hef.symm,
      add_zero, add_zero]
  have hsplit : single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
      (b + a * h.bar a) = single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) b +
      single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1) (a * h.bar a) :=
    single_add _ _ _ _
  have hneg : single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
      (a * -h.bar a) = -single (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (a * h.bar a) := by
    rw [mul_neg, single_neg]
  have hneg' : single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
      (-h.bar a) = -single (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (h.bar a) := by
    rw [single_neg]
  have hfac : lmX h L a b =
      transvection (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inl 0) : HypIndex r 1) a *
      transvection (Sum.inr (Sum.inl 0) : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (-h.bar a) * transvection (Sum.inl L : HypIndex r 1) (Sum.inr (Sum.inr L) : HypIndex r 1)
        (b + a * h.bar a) := by
    rw [h12, transvection, lmX, lmN, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, hAC, add_zero, hsplit, hneg, hneg']
    abel
  rw [hfac, det_mul, det_mul, det_transvection_of_ne _ _ hez, det_transvection_of_ne _ _ hzf,
    det_transvection_of_ne _ _ hef, mul_one, mul_one]

@[expose] noncomputable def lm_xEl (h : UnitaryFieldData p f K) (L : Fin r) {a b : K}
    (hab : b + h.bar b + a * h.bar a = 0) : hypSU h r 1 :=
  mkHypSU h (lmX h L a b) (lmX_gram h L hab) (lmX_det h L a b)

theorem lm_xEl_mem (h : UnitaryFieldData p f K) (L : Fin r) {a b : K}
    (hab : b + h.bar b + a * h.bar a = 0) : lm_xEl h L hab ∈ hypUnitriangular h r 1 :=
  mem_hypUnitriangular_of_strict (N := lmN h L a b) rfl fun x y hxy => lmN_upper h L a b x y hxy

theorem lm_par_conj (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {a b : K} (hab : b + h.bar b + a * h.bar a = 0) :
    -(b / c ^ 2) + h.bar (-(b / c ^ 2)) + a / c * h.bar (a / c) = 0 := by
  have hbc : h.bar c = -c := by
    have := (li_mem_traceZero h).mp hc
    linear_combination this
  simp only [map_neg, map_div₀, map_pow, hbc]
  linear_combination (-(c⁻¹ ^ 2)) * hab

@[expose] noncomputable def lm_yEl (h : UnitaryFieldData p f K) (L : Fin r) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (a b : K) (hab : b + h.bar b + a * h.bar a = 0) :
    hypSU h r 1 :=
  uWeylRep 1 h L c hc * lm_xEl h L (lm_par_conj h hc hc0 hab) * (uWeylRep 1 h L c hc)⁻¹

theorem lm_key (h : UnitaryFieldData p f K) (L : Fin r) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) (a b : K) :
    li_ML (ε := 1) h L (-c⁻¹) c * lmX h L (a / c) (-(b / c ^ 2)) =
      lmY h L a b * li_ML (ε := 1) h L (-c⁻¹) c := by
  have hbc : h.bar c = -c := by
    have := (li_mem_traceZero h).mp hc
    linear_combination this
  have hsu : -c⁻¹ * c = -1 := by field_simp
  have hbar : h.bar (a / c) = -(h.bar a / c) := by
    rw [map_div₀, hbc, div_neg]
  apply lm_eq_of_mulVec
  intro y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hy1 : y = Sum.inl L
  · subst hy1
    rw [lmX_e, li_ML_col_L h L hsu, Matrix.mulVec_smul, lmY_f]
  by_cases hy2 : y = Sum.inr (Sum.inl 0)
  · subst hy2
    rw [lmX_z, Matrix.mulVec_add, Matrix.mulVec_smul, li_ML_col_L h L hsu,
      li_ML_col_gen h L _ _ _ (by simp) (by simp), lmY_z, smul_smul,
      div_mul_cancel₀ a hc0]
  by_cases hy3 : y = Sum.inr (Sum.inr L)
  · subst hy3
    rw [lmX_f, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      li_ML_col_FL h L hsu, li_ML_col_L h L hsu, li_ML_col_gen h L _ _ _ (by simp) (by simp),
      Matrix.mulVec_smul, lmY_e, hbar]
    match_scalars <;> field_simp <;> ring
  · rw [lmX_gen h L _ _ y hy1 hy2 hy3, li_ML_col_gen h L _ _ y hy1 hy3,
      lmY_gen h L _ _ y hy1 hy2 hy3]

theorem lm_yEl_coe (h : UnitaryFieldData p f K) {L : Fin r} (hL : ¬ ((L : ℕ) + 1 < r))
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (a b : K)
    (hab : b + h.bar b + a * h.bar a = 0) :
    li_M (lm_yEl h L hc hc0 a b hab) = lmY h L a b := by
  have hnM : li_M (uWeylRep 1 h L c hc) = li_ML (ε := 1) h L (-c⁻¹) c :=
    li_M_uWeyl_last (ε := 1) h L hL hc
  have hmul : li_M (uWeylRep 1 h L c hc) * li_M (uWeylRep 1 h L c hc)⁻¹ = 1 :=
    li_M_mul_inv h _
  have key := lm_key h L hc hc0 a b
  rw [← hnM] at key
  have hcoe : li_M (lm_yEl h L hc hc0 a b hab) =
      li_M (uWeylRep 1 h L c hc) * lmX h L (a / c) (-(b / c ^ 2)) *
        li_M (uWeylRep 1 h L c hc)⁻¹ := rfl
  rw [hcoe, key, mul_assoc, hmul, mul_one]

@[expose] noncomputable def lmP (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  lmX h L (-a / h.bar b) (1 / h.bar b) * lmY h L a b * lmX h L (-a / b) (1 / h.bar b)

@[expose] noncomputable def lmQ (h : UnitaryFieldData p f K) (L : Fin r) :
    Matrix (HypIndex r 1) (HypIndex r 1) K :=
  lmX h L 0 1 * lmY h L 0 1 * lmX h L 0 1

theorem lmP_e (h : UnitaryFieldData p f K) (L : Fin r) {a b : K} (hb : b ≠ 0)
    (hbb : b + h.bar b + a * h.bar a = 0) :
    lmP h L a b *ᵥ Pi.single (Sum.inl L : HypIndex r 1) 1 =
      b • Pi.single (Sum.inr (Sum.inr L) : HypIndex r 1) 1 := by
  have hB : h.bar b ≠ 0 := (map_ne_zero h.bar).mpr hb
  unfold lmP
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, map_div₀, map_neg, map_one, h.bar_bar]
  match_scalars
  all_goals (try field_simp)
  all_goals first
    | ring1
    | linear_combination hbb
    | linear_combination (-a) * hbb
    | linear_combination h.bar a * hbb

theorem lmP_z (h : UnitaryFieldData p f K) (L : Fin r) {a b : K} (hb : b ≠ 0)
    (hbb : b + h.bar b + a * h.bar a = 0) :
    lmP h L a b *ᵥ Pi.single (Sum.inr (Sum.inl 0) : HypIndex r 1) 1 =
      (-h.bar b / b) • Pi.single (Sum.inr (Sum.inl 0)) 1 := by
  have hB : h.bar b ≠ 0 := (map_ne_zero h.bar).mpr hb
  unfold lmP
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, lmY_z, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, map_div₀, map_neg, map_one, h.bar_bar]
  match_scalars
  all_goals (try field_simp)
  all_goals first
    | ring1
    | linear_combination hbb
    | linear_combination (-a) * hbb
    | linear_combination h.bar a * hbb

theorem lmP_f (h : UnitaryFieldData p f K) (L : Fin r) {a b : K} (hb : b ≠ 0)
    (hbb : b + h.bar b + a * h.bar a = 0) :
    lmP h L a b *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r 1) 1 =
      (1 / h.bar b) • Pi.single (Sum.inl L) 1 := by
  have hB : h.bar b ≠ 0 := (map_ne_zero h.bar).mpr hb
  unfold lmP
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, lmY_z, lmY_f, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, map_div₀, map_neg, map_one, h.bar_bar]
  match_scalars
  all_goals (try field_simp)
  all_goals first
    | ring1
    | linear_combination hbb
    | linear_combination (-a) * hbb
    | linear_combination h.bar a * hbb

theorem lmP_gen (h : UnitaryFieldData p f K) (L : Fin r) (a b : K) (y : HypIndex r 1)
    (h1 : y ≠ Sum.inl L) (h2 : y ≠ Sum.inr (Sum.inl 0)) (h3 : y ≠ Sum.inr (Sum.inr L)) :
    lmP h L a b *ᵥ Pi.single y 1 = Pi.single y 1 := by
  unfold lmP
  simp only [← Matrix.mulVec_mulVec, lmX_gen h L _ _ y h1 h2 h3, lmY_gen h L _ _ y h1 h2 h3]

theorem lmQ_e (h : UnitaryFieldData p f K) (L : Fin r) (h2 : (2 : K) = 0) :
    lmQ h L *ᵥ Pi.single (Sum.inl L : HypIndex r 1) 1 = Pi.single (Sum.inr (Sum.inr L)) 1 := by
  unfold lmQ
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, lmY_z, lmY_f, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero, map_zero, neg_zero, zero_smul,
    zero_mul, neg_mul, zero_add, add_zero]
  match_scalars
  all_goals first
    | ring1
    | linear_combination h2

theorem lmQ_z (h : UnitaryFieldData p f K) (L : Fin r) :
    lmQ h L *ᵥ Pi.single (Sum.inr (Sum.inl 0) : HypIndex r 1) 1 =
      Pi.single (Sum.inr (Sum.inl 0)) 1 := by
  unfold lmQ
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, lmY_z, lmY_f, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, map_zero, neg_zero, zero_smul, zero_mul, add_zero,
    zero_add]

theorem lmQ_f (h : UnitaryFieldData p f K) (L : Fin r) (h2 : (2 : K) = 0) :
    lmQ h L *ᵥ Pi.single (Sum.inr (Sum.inr L) : HypIndex r 1) 1 = Pi.single (Sum.inl L) 1 := by
  unfold lmQ
  simp only [← Matrix.mulVec_mulVec, lmX_e, lmY_e, lmX_z, lmX_f, lmY_z, lmY_f, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero, map_zero, neg_zero, zero_smul,
    zero_mul, neg_mul, zero_add, add_zero]
  match_scalars
  all_goals first
    | ring1
    | linear_combination h2

theorem lmQ_gen (h : UnitaryFieldData p f K) (L : Fin r) (y : HypIndex r 1)
    (h1 : y ≠ Sum.inl L) (h2 : y ≠ Sum.inr (Sum.inl 0)) (h3 : y ≠ Sum.inr (Sum.inr L)) :
    lmQ h L *ᵥ Pi.single y 1 = Pi.single y 1 := by
  unfold lmQ
  simp only [← Matrix.mulVec_mulVec, lmX_gen h L _ _ y h1 h2 h3, lmY_gen h L _ _ y h1 h2 h3]

theorem lm_parP (h : UnitaryFieldData p f K) {a0 b : K} (hb : b ≠ 0)
    (hbb : b + h.bar b + a0 * h.bar a0 = 0) :
    1 / h.bar b + h.bar (1 / h.bar b) + -a0 / h.bar b * h.bar (-a0 / h.bar b) = 0 ∧
      1 / h.bar b + h.bar (1 / h.bar b) + -a0 / b * h.bar (-a0 / b) = 0 := by
  have hB : h.bar b ≠ 0 := (map_ne_zero h.bar).mpr hb
  simp only [map_div₀, map_neg, map_one, h.bar_bar]
  constructor
  all_goals (try field_simp)
  all_goals first
    | ring1
    | linear_combination hbb
    | linear_combination (-1 : K) * hbb

theorem lm_mat_xEl (h : UnitaryFieldData p f K) (L : Fin r) {a b : K}
    (hab : b + h.bar b + a * h.bar a = 0) : li_M (lm_xEl h L hab) = lmX h L a b := rfl

theorem li_M_mul' (h : UnitaryFieldData p f K) (g k : hypSU h r 1) :
    li_M (g * k) = li_M g * li_M k := rfl

theorem lm_yEl_mem (h : UnitaryFieldData p f K) (L : Fin r) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) (a b : K) (hab : b + h.bar b + a * h.bar a = 0)
    (A : Subgroup (hypSU h r 1)) (hU : hypUnitriangular h r 1 ≤ A)
    (hn : uWeylRep 1 h L c hc ∈ A) : lm_yEl h L hc hc0 a b hab ∈ A := by
  unfold lm_yEl
  exact mul_mem (mul_mem hn (hU (lm_xEl_mem h L (lm_par_conj h hc hc0 hab)))) (inv_mem hn)

theorem lm_PQ (h : UnitaryFieldData p f K) (L : Fin r) (h2 : (2 : K) = 0) {x a0 : K}
    (hx0 : x ≠ 0) (hbb : (h.bar x)⁻¹ + h.bar (h.bar x)⁻¹ + a0 * h.bar a0 = 0)
    (D : HypIndex r 1 → K) (hD1 : D (Sum.inl L) = x)
    (hD2 : D (Sum.inr (Sum.inl 0)) = h.bar x / x) (hD3 : D (Sum.inr (Sum.inr L)) = (h.bar x)⁻¹)
    (hD4 : ∀ y : HypIndex r 1, y ≠ Sum.inl L → y ≠ Sum.inr (Sum.inl 0) →
      y ≠ Sum.inr (Sum.inr L) → D y = 1) :
    lmP h L a0 (h.bar x)⁻¹ * lmQ h L = diagonal D := by
  have hbx0 : h.bar x ≠ 0 := (map_ne_zero h.bar).mpr hx0
  have hb0 : (h.bar x)⁻¹ ≠ 0 := inv_ne_zero hbx0
  have hbarb : h.bar (h.bar x)⁻¹ = x⁻¹ := by rw [map_inv₀, h.bar_bar]
  have hneg : ∀ t : K, -t = t := fun t => by linear_combination (-t) * h2
  have hz : -(h.bar (h.bar x)⁻¹) / (h.bar x)⁻¹ = h.bar x / x := by
    rw [hbarb, div_inv_eq_mul, ← hneg (h.bar x / x)]
    ring
  apply lm_eq_of_mulVec
  intro y
  rw [← Matrix.mulVec_mulVec]
  by_cases hy1 : y = Sum.inl L
  · subst hy1
    rw [lmQ_e h L h2, lmP_f h L hb0 hbb, li_diag_basis, hD1, hbarb, one_div, inv_inv]
  by_cases hy2 : y = Sum.inr (Sum.inl 0)
  · subst hy2
    rw [lmQ_z h L, lmP_z h L hb0 hbb, li_diag_basis, hD2, hz]
  by_cases hy3 : y = Sum.inr (Sum.inr L)
  · subst hy3
    rw [lmQ_f h L h2, lmP_e h L hb0 hbb, li_diag_basis, hD3]
  · rw [lmQ_gen h L y hy1 hy2 hy3, lmP_gen h L _ _ y hy1 hy2 hy3, li_diag_basis,
      hD4 y hy1 hy2 hy3, one_smul]

theorem li_middle_holds : li_middle := by
  unfold li_middle
  intro f K _ h r c hc hc0 A hr hU hn a d ha hd hp
  haveI := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  set L : Fin r := ⟨r - 1, by omega⟩ with hLdef
  have hLv : (L : ℕ) = r - 1 := rfl
  have hL : ¬ ((L : ℕ) + 1 < r) := by omega
  have ha' : ∀ i : Fin r, i ≠ L → (a i : K) = 1 := by
    intro i hi
    have hlt : (i : ℕ) < r - 1 := by
      have h1 : (i : ℕ) ≠ (L : ℕ) := fun h' => hi (Fin.ext h')
      have h3 := i.2
      omega
    rw [ha i hlt, Units.val_one]
  have hx0 : (a L : K) ≠ 0 := (a L).ne_zero
  have hbx0 : h.bar (a L : K) ≠ 0 := (map_ne_zero h.bar).mpr hx0
  have hd0 : (d 0 : K) = h.bar (a L : K) / (a L : K) := by
    have hp' : (∏ i : Fin r, (a i : K) / h.bar (a i)) * ∏ k : Fin 1, (d k : K) = 1 := hp
    rw [Finset.prod_eq_single L (fun i _ hi => by simp [ha' i hi])
      (fun hL' => absurd (Finset.mem_univ L) hL'), Fin.prod_univ_one] at hp'
    have e2 : (d 0 : K) * (a L : K) = h.bar (a L : K) := by
      field_simp at hp'
      linear_combination hp'
    exact (eq_div_iff hx0).mpr e2
  set b : K := (h.bar (a L : K))⁻¹ with hbdef
  have hb0 : b ≠ 0 := inv_ne_zero hbx0
  have hfix : -(b + h.bar b) ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_add, h.bar_bar]
    ring
  obtain ⟨a0, ha0⟩ := h.normHom_surjective ⟨-(b + h.bar b), hfix⟩
  have hn0 : h.norm a0 = -(b + h.bar b) := by
    have := congrArg Subtype.val ha0
    simpa using this
  have hbb : b + h.bar b + a0 * h.bar a0 = 0 := by
    simp only [UnitaryFieldData.norm] at hn0
    linear_combination hn0
  have hP := lm_parP h hb0 hbb
  have hQ : (1 : K) + h.bar 1 + 0 * h.bar 0 = 0 := by
    rw [map_one, zero_mul, add_zero, one_add_one_eq_two, h2]
  have mem1 : lm_xEl h L hP.1 ∈ A := hU (lm_xEl_mem h L hP.1)
  have mem2 : lm_xEl h L hP.2 ∈ A := hU (lm_xEl_mem h L hP.2)
  have memQ : lm_xEl h L hQ ∈ A := hU (lm_xEl_mem h L hQ)
  have memY0 : lm_yEl h L hc hc0 a0 b hbb ∈ A := lm_yEl_mem h L hc hc0 a0 b hbb A hU (hn L)
  have memY1 : lm_yEl h L hc hc0 0 1 hQ ∈ A := lm_yEl_mem h L hc hc0 0 1 hQ A hU (hn L)
  have hD1 : torusEntries h a d (Sum.inl L) = (a L : K) := rfl
  have hD2 : torusEntries h a d (Sum.inr (Sum.inl 0)) = h.bar (a L : K) / (a L : K) := hd0
  have hD3 : torusEntries h a d (Sum.inr (Sum.inr L)) = (h.bar (a L : K))⁻¹ := rfl
  have hD4 : ∀ y : HypIndex r 1, y ≠ Sum.inl L → y ≠ Sum.inr (Sum.inl 0) →
      y ≠ Sum.inr (Sum.inr L) → torusEntries h a d y = 1 := by
    intro y h1 h2' h3
    rcases y with i | k | i
    · have hi : i ≠ L := fun e => h1 (by rw [e])
      exact ha' i hi
    · exact absurd (by rw [Subsingleton.elim k 0]) h2'
    · have hi : i ≠ L := fun e => h3 (by rw [e])
      simp only [torusEntries, ha' i hi, map_one, inv_one]
  refine ⟨lm_xEl h L hP.1 * lm_yEl h L hc hc0 a0 b hbb * lm_xEl h L hP.2 * lm_xEl h L hQ *
    lm_yEl h L hc hc0 0 1 hQ * lm_xEl h L hQ, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem mem1 memY0) mem2) memQ) memY1) memQ
  · have hmat : li_M (lm_xEl h L hP.1 * lm_yEl h L hc hc0 a0 b hbb * lm_xEl h L hP.2 *
        lm_xEl h L hQ * lm_yEl h L hc hc0 0 1 hQ * lm_xEl h L hQ) =
        lmP h L a0 b * lmQ h L := by
      simp only [li_M_mul', lm_mat_xEl, lm_yEl_coe h hL hc hc0]
      unfold lmP lmQ
      simp only [Matrix.mul_assoc]
    exact hmat.trans (lm_PQ h L h2 hx0 hbb (torusEntries h a d) hD1 hD2 hD3 hD4)

theorem psuTorusOvergroup_holds : PSUTorusOvergroup :=
  psuTorusOvergroup_of_middle li_middle_holds

end CFSG.Quasithin.LieOver
