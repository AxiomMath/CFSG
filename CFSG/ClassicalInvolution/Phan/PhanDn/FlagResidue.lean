module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.LieType.CurtisTits.TitsGeometryRetained
import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.LieType.CurtisTits CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} {m : ℕ}

theorem FlagVert.finrank_le (U : FlagVert σ m) : Module.finrank K U.1 ≤ m + 1 :=
  U.2.1.finrank_le

theorem FlagVert.finrank_ne_zero (U : FlagVert σ m) : Module.finrank K U.1 ≠ 0 :=
  fun h => U.2.2.1 (Submodule.finrank_eq_zero.1 h)

theorem FlagVert.finrank_eq_of_flagTyp {U : FlagVert σ m} (h : (flagTyp U : ℕ) + 2 ≤ m) :
    Module.finrank K U.1 = flagTyp U + 1 := by
  have h0 := U.finrank_ne_zero
  unfold flagTyp at h ⊢
  split_ifs at h ⊢ with hs he
  · simp only [Fin.val_last] at h
    omega
  · simp only at h
    omega
  · simp only at h ⊢
    omega

theorem FlagVert.finrank_eq_of_le_flagTyp {U : FlagVert σ m} (h : m ≤ (flagTyp U : ℕ) + 1) :
    Module.finrank K U.1 = m + 1 := by
  have h0 := U.finrank_ne_zero
  have hle := U.finrank_le
  have hm := U.2.2.2
  unfold flagTyp at h
  split_ifs at h with hs he
  · exact hs
  · exact hs
  · simp only at h
    omega

theorem FlagVert.isLagrangian {U : FlagVert σ m} (h : Module.finrank K U.1 = m + 1) :
    (quadPlusForm (m + 1) K).IsLagrangian U.1 :=
  ⟨fun w hw => by rw [quadPlusForm_Q]; exact U.2.1.total w hw, by
    rw [h, finrank_flipSpace]⟩

theorem flagTyp_eq_iff_even (hm : 1 ≤ m) {U W : FlagVert σ m}
    (hU : Module.finrank K U.1 = m + 1) (hW : Module.finrank K W.1 = m + 1) :
    flagTyp U = flagTyp W ↔ Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ W.1)) := by
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm (m + 1) K)
    (finrank_flipSpace (m + 1) K) (FlagVert.isLagrangian hU) (FlagVert.isLagrangian hW)
    (isLagrangian_stdLag (m + 1) K)
  rw [Nat.even_add, Nat.even_add] at hpar
  have hne : (Fin.last m) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  unfold flagTyp
  rw [if_pos hU, if_pos hW]
  split_ifs with h₁ h₂ h₂
  · simp only [true_iff]
    tauto
  · simp only [hne, false_iff]
    tauto
  · simp only [hne.symm, false_iff]
    tauto
  · simp only [true_iff]
    tauto

theorem flagGraph_adj_iff_lt_of_finrank_lt {U W : FlagVert σ m}
    (h : Module.finrank K U.1 < Module.finrank K W.1) :
    (flagGraph σ m).Adj U W ↔ U.1 < W.1 := by
  refine ⟨fun hUW => ?_, fun hlt => Or.inl hlt⟩
  rcases hUW with hlt | hlt | ⟨h₁, h₂, -⟩
  · exact hlt
  · exact absurd (Submodule.finrank_lt_finrank_of_lt hlt) (by omega)
  · omega

theorem flagGraph_adj_of_solids (hm : 1 ≤ m) {U W : FlagVert σ m}
    (hU : Module.finrank K U.1 = m + 1) (hW : Module.finrank K W.1 = m + 1)
    (hne : flagTyp U ≠ flagTyp W) {T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : m - 1 ≤ Module.finrank K T) (hTU : T ≤ U.1) (hTW : T ≤ W.1) :
    (flagGraph σ m).Adj U W := by
  refine Or.inr (Or.inr ⟨hU, hW, ?_⟩)
  have h₁ : Module.finrank K T ≤ Module.finrank K ↥(U.1 ⊓ W.1) :=
    Submodule.finrank_mono (le_inf hTU hTW)
  have h₂ : Module.finrank K ↥(U.1 ⊓ W.1) ≤ Module.finrank K U.1 :=
    Submodule.finrank_mono inf_le_left
  have h₃ := mt (flagTyp_eq_iff_even hm hU hW).2 hne
  rw [Nat.even_iff] at h₃
  omega

theorem finrank_flagChamber (E : QuadExt F K σ) (i : Fin (m + 1)) :
    Module.finrank K (flagChamber E m i).1 = if (i : ℕ) + 1 < m then (i : ℕ) + 1 else m + 1 := by
  rw [coe_flagChamber]
  exact (stdDChamber σ (m + 1)).toFlipFrame.finrank_elt E.isUnitary.invol i

private theorem stdDChamber_sub_succ (σ : K ≃+* K) (m : ℕ) :
    (stdDChamber σ (m + 1)).toFlipFrame.sub (m + 1) = stdLag (m + 1) K := by
  rw [FlipFrame.sub, ← stdDChamber_spanAt_univ σ (m + 1)]
  congr 1
  exact Finset.filter_true_of_mem fun l _ => l.is_lt

theorem coe_flagChamber_of_lt (E : QuadExt F K σ) {i : Fin (m + 1)} (hi : (i : ℕ) + 1 < m) :
    (flagChamber E m i).1 = (stdDChamber σ (m + 1)).toFlipFrame.sub ((i : ℕ) + 1) := by
  rw [coe_flagChamber, FlipFrame.elt, if_neg, if_neg (by omega)]
  intro h
  rw [h, Fin.val_last] at hi
  omega

theorem coe_flagChamber_last (E : QuadExt F K σ) :
    (flagChamber E m (Fin.last m)).1 = stdLag (m + 1) K := by
  rw [coe_flagChamber, FlipFrame.elt, if_pos rfl, stdDChamber_sub_succ]

theorem coe_flagChamber_of_succ_eq (E : QuadExt F K σ) {i : Fin (m + 1)} (hi : (i : ℕ) + 1 = m) :
    (flagChamber E m i).1 = (stdDChamber σ (m + 1)).toFlipFrame.alt := by
  rw [coe_flagChamber, FlipFrame.elt, if_neg, if_pos hi]
  intro h
  rw [h, Fin.val_last] at hi
  omega

theorem flagTyp_flagChamber (E : QuadExt F K σ) (i : Fin (m + 1)) :
    flagTyp (flagChamber E m i) = i := by
  have hfin := finrank_flagChamber E i
  by_cases hi : (i : ℕ) + 1 < m
  · rw [if_pos hi] at hfin
    unfold flagTyp
    rw [if_neg (by omega)]
    ext
    simp only [hfin]
    omega
  · rw [if_neg hi] at hfin
    unfold flagTyp
    rw [if_pos hfin]
    by_cases hlast : i = Fin.last m
    · subst hlast
      rw [if_pos]
      rw [coe_flagChamber_last, inf_idem, finrank_stdLag, Nat.sub_self]
      exact ⟨0, rfl⟩
    · have hi' : (i : ℕ) + 1 = m := by
        have := i.is_lt
        have : (i : ℕ) ≠ m := fun h => hlast (Fin.ext (by simp [h]))
        omega
      rw [if_neg]
      · ext
        simp only
        omega
      · rw [coe_flagChamber_of_succ_eq E hi', ← stdDChamber_spanAt_univ σ (m + 1),
          FlipFrame.alt_inf_spanAt_univ E.isUnitary.invol _, FlipFrame.finrank_sub _ (by omega)]
        rw [show m + 1 - m = 1 by omega]
        decide

theorem flagChamber_adj (E : QuadExt F K σ) {i j : Fin (m + 1)} (hij : i ≠ j) :
    (flagGraph σ m).Adj (flagChamber E m i) (flagChamber E m j) := by
  have hσ := E.isUnitary.invol
  set c := (stdDChamber σ (m + 1)).toFlipFrame with hc
  have hsub : ∀ {a b : ℕ}, a ≤ b → c.sub a ≤ c.sub b := fun hab =>
    c.spanAt_mono fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      omega
  have hsol : ∀ {k : Fin (m + 1)}, ¬ (k : ℕ) + 1 < m → c.sub m ≤ (flagChamber E m k).1 := by
    intro k hk
    by_cases hlast : k = Fin.last m
    · subst hlast
      rw [coe_flagChamber, FlipFrame.elt, if_pos rfl]
      exact hsub (by omega)
    · have hk' : (k : ℕ) + 1 = m := by
        have := k.is_lt
        have : (k : ℕ) ≠ m := fun h => hlast (Fin.ext (by simp [h]))
        omega
      rw [coe_flagChamber_of_succ_eq E hk']
      exact le_sup_left
  have key : ∀ {i j : Fin (m + 1)}, (i : ℕ) < j →
      (flagGraph σ m).Adj (flagChamber E m i) (flagChamber E m j) := by
    intro i j hij
    have hfi := finrank_flagChamber E i
    have hfj := finrank_flagChamber E j
    by_cases hi : (i : ℕ) + 1 < m
    · refine Or.inl (Submodule.lt_of_le_of_finrank_lt_finrank ?_ ?_)
      · rw [coe_flagChamber_of_lt E hi]
        by_cases hj : (j : ℕ) + 1 < m
        · rw [coe_flagChamber_of_lt E hj]
          exact hsub (by omega)
        · exact (hsub (by omega)).trans (hsol hj)
      · rw [hfi, hfj, if_pos hi]
        split_ifs <;> omega
    ·
      have hj : j = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      have hi' : (i : ℕ) + 1 = m := by omega
      subst hj
      rw [if_neg hi] at hfi
      rw [if_neg (by simp only [Fin.val_last]; omega)] at hfj
      refine Or.inr (Or.inr ⟨hfi, hfj, ?_⟩)
      rw [coe_flagChamber_of_succ_eq E hi', coe_flagChamber, inf_comm,
        FlipFrame.elt_last_inf_alt hσ, FlipFrame.finrank_sub _ (by omega)]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact (key h).symm

@[expose] noncomputable def flagResidueChamber (E : QuadExt F K σ) (J : Set (Fin (m + 1)))
    {t : Fin (m + 1)} (ht : t ∉ J) : residueVertex (flagGraph σ m) flagTyp (flagChamber E m) J :=
  ⟨flagChamber E m t, by rw [flagTyp_flagChamber]; exact ht,
    fun j hj => flagChamber_adj E fun h => ht (h ▸ hj)⟩

@[expose] def dLevel (m : ℕ) (t : Fin (m + 1)) : ℕ := min (t : ℕ) (m - 1)

@[expose] def DSep (m : ℕ) (j s t : Fin (m + 1)) : Prop :=
  (j : ℕ) + 2 ≤ m ∧ ((dLevel m s < j ∧ (j : ℕ) < dLevel m t) ∨
    (dLevel m t < j ∧ (j : ℕ) < dLevel m s) ∨
    ((j : ℕ) + 2 = m ∧ m ≤ (s : ℕ) + 1 ∧ m ≤ (t : ℕ) + 1 ∧ s ≠ t))

private theorem flagResidue_lt_of_level (E : QuadExt F K σ) {J : Set (Fin (m + 1))}
    (z : residueVertex (flagGraph σ m) flagTyp (flagChamber E m) J) {j : Fin (m + 1)}
    (hj : j ∈ J) (hjm : (j : ℕ) + 2 ≤ m) :
    (dLevel m (flagTyp z.1) < j → z.1.1 < (flagChamber E m j).1) ∧
      ((j : ℕ) < dLevel m (flagTyp z.1) → (flagChamber E m j).1 < z.1.1) := by
  have hF : Module.finrank K (flagChamber E m j).1 = (j : ℕ) + 1 := by
    rw [finrank_flagChamber, if_pos (by omega)]
  have hadj : (flagGraph σ m).Adj z.1 (flagChamber E m j) := z.2.2 j hj
  unfold dLevel
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · have hz : Module.finrank K z.1.1 = flagTyp z.1 + 1 :=
      FlagVert.finrank_eq_of_flagTyp (by omega)
    exact (flagGraph_adj_iff_lt_of_finrank_lt (by omega)).1 hadj
  · have hz : (j : ℕ) + 1 < Module.finrank K z.1.1 := by
      by_cases ht : (flagTyp z.1 : ℕ) + 2 ≤ m
      · rw [FlagVert.finrank_eq_of_flagTyp ht]
        omega
      · rw [FlagVert.finrank_eq_of_le_flagTyp (by omega)]
        omega
    exact (flagGraph_adj_iff_lt_of_finrank_lt (by omega)).1 hadj.symm

theorem flagResidue_adj_of_sep (E : QuadExt F K σ) {J : Set (Fin (m + 1))}
    {x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m) J} {j : Fin (m + 1)}
    (hj : j ∈ J) (h : DSep m j (flagTyp x.1) (flagTyp y.1)) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Adj x y := by
  change (flagGraph σ m).Adj x.1 y.1
  obtain ⟨hjm, h | h | ⟨hj2, hs, ht, hst⟩⟩ := h
  · exact Or.inl (((flagResidue_lt_of_level E x hj hjm).1 h.1).trans
      ((flagResidue_lt_of_level E y hj hjm).2 h.2))
  · exact Or.inr (Or.inl (((flagResidue_lt_of_level E y hj hjm).1 h.1).trans
      ((flagResidue_lt_of_level E x hj hjm).2 h.2)))
  · have hF : Module.finrank K (flagChamber E m j).1 = (j : ℕ) + 1 := by
      rw [finrank_flagChamber, if_pos (by omega)]
    have hxs := FlagVert.finrank_eq_of_le_flagTyp hs
    have hys := FlagVert.finrank_eq_of_le_flagTyp ht
    have hx : (flagChamber E m j).1 < x.1.1 :=
      (flagGraph_adj_iff_lt_of_finrank_lt (by omega)).1 (x.2.2 j hj).symm
    have hy : (flagChamber E m j).1 < y.1.1 :=
      (flagGraph_adj_iff_lt_of_finrank_lt (by omega)).1 (y.2.2 j hj).symm
    exact flagGraph_adj_of_solids (by omega) hxs hys hst (T := (flagChamber E m j).1)
      (by omega) hx.le hy.le

theorem nonempty_flagResidue_induce_iso (E : QuadExt F K σ) {J C : Set (Fin (m + 1))}
    (hC : C ⊆ Jᶜ) (hsep : ∀ s ∈ C, ∀ t, t ∉ J → t ∉ C → ∃ j ∈ J, DSep m j s t) :
    Nonempty (((residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).induce
        {x | flagTyp x.1 ∈ C}) ≃g residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ) := by
  refine ⟨{
    toFun := fun x => ⟨x.1.1, fun h => h x.2, fun t ht => ?_⟩
    invFun := fun y => ⟨⟨y.1, fun h => hC (not_not.1 y.2.1) h,
      fun j hj => y.2.2 j fun hjC => hC hjC hj⟩, not_not.1 y.2.1⟩
    left_inv := fun x => rfl
    right_inv := fun y => rfl
    map_rel_iff' := Iff.rfl }⟩
  by_cases htJ : t ∈ J
  · exact x.1.2.2 t htJ
  · obtain ⟨j, hj, hjs⟩ := hsep _ x.2 t htJ ht
    have := flagResidue_adj_of_sep E (x := x.1) (y := flagResidueChamber E J htJ) hj
      (by rwa [show flagTyp (flagResidueChamber E J htJ).1 = t from flagTyp_flagChamber E t])
    exact this

end CFSG.ClassicalInvolution.PhanDn
