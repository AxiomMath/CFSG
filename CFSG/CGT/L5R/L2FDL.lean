module

public import CFSG.CGT.L5R.L2SubDL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

@[expose] def z1L : N8 := wv2 dL z1DW

@[expose] def z2L : N8 := wv2 dL z2DW

section D


theorem dCheckL_spec :
    (∀ i : Fin 2, normAll b8List (dT2 i) = true ∧ normAll b8List (thT2 i) = true) ∧
    (∀ z ∈ dListL (mkCtx ()), commT ((mkCtx ()).tab z) (dT2 0) = false ∨
      commT ((mkCtx ()).tab z) (dT2 1) = false ∨ ((mkCtx ()).tab z == idT 16) = true) ∧
    ∀ i : Fin 2, (evT2 dT2 (thDW i) == thT2 i) = true ∧ (evT2 thT2 (thDW i) == dT2 i) = true := by
  have h := Certificates.certificate21196.2.2.2.2.1
  simp only [dCheckL, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun z hz => ?_, h3⟩
  rcases h2 z hz with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem wCheckL_spec :
    (∀ p ∈ relDW, (evT2 dT2 p.1 == evT2 dT2 p.2) = true) ∧ (dT2 0 == idT 16) = false ∧
    (evT2 dT2 sevenW == idT 16) = true ∧
    (∀ i : Fin 3, (evT2 dT2 (aDW i) == idT 16) = false ∧
      (mkCtx ()).isTt (evT2 dT2 (aDW i)) = true) ∧
    (∀ i : Fin 3, (evT2 dT2 (bDW i) == idT 16) = false ∧ isB8 (evT2 dT2 (bDW i)) = true) ∧
    conjIn (wTab nzW10) (evT2 dT2 z1DW) b8List = true ∧
    (mkCtx ()).isTt (evT2 dT2 z2DW) = false ∧
    ((mkCtx ()).commCount (evT2 dT2 z2DW) == 4) = true := by
  have h := Certificates.certificate21196.2.2.2.2.2.1
  simp only [wCheckL, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

variable (hcard : Nat.card N8 = 322560)
include hcard

omit hcard in
theorem isTab_wv2d (w : List (Fin 2)) : IsTab (evT2 dT2 w) (wv2 dL w) :=
  evT2_isTab isTab_dT2 w

theorem dL_mem (i : Fin 2) : dL i ∈ DL :=
  (normB8_iff hcard (isTab_dT2 i)).1 (dCheckL_spec.1 i).1

theorem thL_mem (i : Fin 2) : thL i ∈ DL :=
  (normB8_iff hcard (isTab_thT2 i)).1 (dCheckL_spec.1 i).2

theorem centerL (z : N8) (hz : z ∈ DL) (hc : ∀ i, z * dL i = dL i * z) : z = 1 := by
  obtain ⟨c, hc', rfl⟩ := el_of_mem_DL hcard hz
  have hX := isTab_tab (mem_codes.1 ((mem_dListL_iff hcard).1 hc').1).1
  have hcomm : ∀ i, commT ((mkCtx ()).tab c) (dT2 i) = true :=
    fun i => (hX.commT_iff hcard (isTab_dT2 i)).2 (hc i)
  rcases dCheckL_spec.2.1 c hc' with h | h | h
  · rw [hcomm 0] at h
    exact absurd h (by decide)
  · rw [hcomm 1] at h
    exact absurd h (by decide)
  · exact (hX.beq_iff hcard IsTab.one (tab_size c) idT_size).1 h

theorem theta_wordsL (i : Fin 2) : wv2 dL (thDW i) = thL i ∧ wv2 thL (thDW i) = dL i := by
  obtain ⟨h1, h2⟩ := dCheckL_spec.2.2 i
  exact ⟨((isTab_wv2d _).beq_iff hcard (isTab_thT2 i) (evT2_size _ _) (wTab_size _)).1 h1,
    ((evT2_isTab isTab_thT2 _).beq_iff hcard (isTab_dT2 i) (evT2_size _ _) (wTab_size _)).1 h2⟩

theorem relDW_holds : ∀ p ∈ relDW, wv2 dL p.1 = wv2 dL p.2 := fun p hp =>
  ((isTab_wv2d _).beq_iff hcard (isTab_wv2d _) (evT2_size _ _) (evT2_size _ _)).1
    (wCheckL_spec.1 p hp)

theorem dL_ne_one : dL 0 ≠ 1 := by
  intro h
  have h2 := wCheckL_spec.2.1
  rw [((isTab_dT2 0).beq_iff hcard IsTab.one (wTab_size _) idT_size).2 h] at h2
  exact absurd h2 (by decide)

theorem dL_pow7 : wv2 dL sevenW = 1 :=
  ((isTab_wv2d _).beq_iff hcard IsTab.one (evT2_size _ _) idT_size).1 wCheckL_spec.2.2.1

theorem aDW_spec (i : Fin 3) : wv2 dL (aDW i) ≠ 1 ∧ wv2 dL (aDW i) ∈ T8 := by
  obtain ⟨h1, h2⟩ := wCheckL_spec.2.2.2.1 i
  refine ⟨fun h => ?_, (isTt_iff hcard (isTab_wv2d _) (evT2_size _ _)).1 h2⟩
  rw [((isTab_wv2d _).beq_iff hcard IsTab.one (evT2_size _ _) idT_size).2 h] at h1
  exact absurd h1 (by decide)

theorem bDW_spec (i : Fin 3) : wv2 dL (bDW i) ≠ 1 ∧ wv2 dL (bDW i) ∈ B8L := by
  obtain ⟨h1, h2⟩ := wCheckL_spec.2.2.2.2.1 i
  refine ⟨fun h => ?_, (isB8_iff hcard (isTab_wv2d _) (evT2_size _ _)).1 h2⟩
  rw [((isTab_wv2d _).beq_iff hcard IsTab.one (evT2_size _ _) idT_size).2 h] at h1
  exact absurd h1 (by decide)

theorem z1_conj : nzL * z1L * nzL⁻¹ ∈ B8L :=
  (conjIn_iff hcard (b8_spec hcard).1 (b8_spec hcard).2 isTab_nzW10 (isTab_wv2d _)).1
    wCheckL_spec.2.2.2.2.2.1

theorem z2_notMem : z2L ∉ T8 := by
  intro h
  have h2 := wCheckL_spec.2.2.2.2.2.2.1
  rw [(isTt_iff hcard (isTab_wv2d _) (evT2_size _ _)).2 h] at h2
  exact absurd h2 (by decide)

theorem z2_card : Nat.card ↥(T8 ⊓ Subgroup.centralizer ({z2L} : Set N8)) = 4 := by
  unfold z2L
  rw [← commCount_eq hcard (isTab_wv2d _)]
  exact beq_iff_eq.1 wCheckL_spec.2.2.2.2.2.2.2

theorem z1L_mem : z1L ∈ DL := wv2_mem (dL_mem hcard) _

theorem z2L_mem : z2L ∈ DL := wv2_mem (dL_mem hcard) _

end D

end CFSG.CGT.L5R
