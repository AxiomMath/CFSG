module

public import CFSG.Quasithin.Background.A3Structure314Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.A314

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T B L : Subgroup G}

theorem mathieu_data_F4 (hF : A314Facts_F4) (c : Ctx T B L)
    (hL : IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L)
    (hB : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsBlock2 (B ⊔ T) B ∧ IsLin2Type B 2 := by
  obtain ⟨hs, hl⟩ := hF.desc.mathieu G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  exact ⟨isBlock2_of_short c.hB hs, hl⟩

theorem case2_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C2 B L) : A314Statement T B L := by
  obtain ⟨⟨n, hn⟩, hrk, P, hP, hBP⟩ := h
  obtain ⟨hs, hna⟩ := hF.model.2.1 n _ hn
  have hrad : CFSG.solvableRadical ↥B = CFSG.pCore 2 ↥B :=
    solvableRadical_eq_of_simple (V := CFSG.pCore 2 ↥B) (solvable_pCore_two _) hs hna
  have hA5 : IsAlt 5 (ModO2 B) := isAlt_of_radical_eq hrad c.hA
  subst hBP
  obtain ⟨hF1, hL⟩ := hF.desc.lie G L P hrk hP hA5
  unfold A314Statement
  left
  exact ⟨hF1, hrad.symm, hL, P, hP, rfl⟩

theorem case3_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C3 B L) : A314Statement T B L := by
  obtain ⟨f, hf, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf⟩))))) c.hA).elim

theorem case4_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C4 B L) : A314Statement T B L := by
  obtain ⟨hB3, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _) (Or.inl hB3) c.hA).elim

theorem case5_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C5 B L) : A314Statement T B L := by
  obtain ⟨hB4, -⟩ := h
  exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
    (Or.inr (Or.inl hB4)) c.hA).elim

theorem case6_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C6 B L) : A314Statement T B L := by
  obtain ⟨hB5 | hB3, hL7⟩ := h
  · unfold A314Statement
    refine Or.inr (Or.inl ⟨hB5, hL7, ?_⟩)
    exact hF.desc.alt7 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL7 hB5
  · exact (excl_model_self hF.model (Or.inl hB3) c.hA).elim

theorem case8_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C8 B L) : A314Statement T B L := by
  rcases h with ⟨p, hp, hp3, hBp, hLp⟩ | ⟨hB5, p, hp, hLp, h5, h8⟩
  · obtain ⟨hs, hna, hcard⟩ := hF.model.2.2 p hp hp3 ↥B hBp
    have hB5 : IsAlt 5 ↥B := isAlt_of_simple hs hna c.hA
    have hp5 : p = 5 := p_eq_five_of_div hp hp3 (by rw [← hcard]; exact card_isAlt_five hB5)
    subst hp5
    unfold A314Statement
    exact Or.inr (Or.inr (Or.inl ⟨hB5, Or.inl hLp⟩))
  · unfold A314Statement
    exact Or.inr (Or.inr (Or.inl ⟨hB5, Or.inr ⟨p, hp, h5, h8, hLp⟩⟩))

theorem case9_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C9 B L) : A314Statement T B L := by
  rcases h with ⟨s, p, hp, hp3, hBp, hLp⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · have hp5 : p = 5 := by
      let e : ↥B ⧸ (⊥ : Subgroup ↥B) ≃* ↥B := QuotientGroup.quotientBot
      exact p_eq_five_of_sl2 (V := ⊥) (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
        hp hp3 (IsSL2.of_mulEquiv e.symm hBp) c.hA
    subst hp5
    have hLs : ∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L := ⟨s, hLp⟩
    unfold A314Statement
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hBp, hLs,
      hF.desc.sl3five G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hLs hBp⟩)))
  · exact (excl_alt_self (by norm_num) (by norm_num) hB c.hA).elim
  · exact (excl_hat_self hB hS_alt_six c.hA).elim

theorem case10_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C10 B L) : A314Statement T B L := by
  obtain ⟨p, hp, hp3, hBext, hLp⟩ := h
  have hp5 : p = 5 := by
    obtain ⟨V, hVn, hV, hY⟩ := hBext
    exact p_eq_five_of_sl2 (solvable_of_isElemAbelianOfRank hV) hp hp3 hY c.hA
  subst hp5
  unfold A314Statement
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hBext, hLp,
    hF.desc.l3five G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hLp hBext⟩))))

theorem case12_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C12 B L) : A314Statement T B L := by
  have hPV : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 4 V h
  rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
  · obtain ⟨hbl, hl2⟩ := mathieu_data_F4 hF c (Or.inl hL) hB
    unfold A314Statement
    iterate 5 right
    left
    exact ⟨hB, hbl, hl2, Or.inl hL⟩
  · exact (excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV (fun Y _ hY => hY) c.hA).elim
  · obtain ⟨hbl, hl2⟩ := mathieu_data_F4 hF c (Or.inr (Or.inl hL)) hB
    unfold A314Statement
    iterate 5 right
    left
    exact ⟨hB, hbl, hl2, Or.inr hL⟩
  · exact (excl_hat_ext hB hPV (fun Y _ hY => hY) hS_alt_six c.hA).elim

theorem case13_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C13 B L) : A314Statement T B L := by
  have hPV4 : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 4 V h
  have hPV3 : ∀ (V : Type) [Group V] [Finite V], IsE2 3 V → Group.IsSolvable V :=
    fun V _ _ h => solvable_isE2 3 V h
  obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
  · exact (excl_model_self hF.model (Or.inr (Or.inr (Or.inr (Or.inl hB)))) c.hA).elim
  · exact (excl_model_self hF.model (Or.inr (Or.inr (Or.inl hB))) c.hA).elim
  · exact (excl_alt_ext (n := 7) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) c.hA).elim
  · exact (excl_model_ext hF.model hB hPV4 (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_model_ext hF.model hB hPV3 (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) c.hA).elim
  · obtain ⟨hbl, hl2⟩ := mathieu_data_F4 hF c (Or.inr (Or.inr hL)) hB
    unfold A314Statement
    iterate 6 right
    left
    exact ⟨hB, hbl, hl2, hL⟩

theorem case14_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C14 B L) : A314Statement T B L := by
  obtain ⟨hB | hB | hB | hB, -⟩ := h
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 4 V h)
      (fun Y _ hY => Or.inr (Or.inl hY)) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 6 V h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isExtraspecial2 h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_isE2 6 V h) (fun Y _ hY => hY)
      hS_alt_six c.hA).elim

theorem case15_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C15 B L) : A314Statement T B L := by
  obtain ⟨hB, hL⟩ := h
  have hz := hF.desc.j1 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  unfold A314Statement
  iterate 7 right
  left
  exact ⟨hB, hL, hz⟩

theorem case16_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C16 B L) : A314Statement T B L := by
  obtain ⟨hB, hL⟩ := h
  have hz := hF.desc.j2 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
  unfold A314Statement
  iterate 8 right
  left
  exact ⟨hB, hL, hz⟩

theorem case17_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C17 B L) : A314Statement T B L := by
  obtain ⟨hL, hB | hB | hB | hB | hB | hB⟩ := h
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_of_isExtraspecial2 h) (fun Y _ hY => hY)
      (hS_m22 hF.model) c.hA).elim
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_isE2 11 V h)
      (fun Y _ hY => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hY))))) c.hA).elim
  · have hF' := hF.desc.j4 G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
    unfold A314Statement
    iterate 9 right
    left
    exact ⟨hB, hF', hL⟩
  · exact (excl_hat (V := CFSG.pCore 2 ↥B) (solvable_pCore_two _) hB hS_alt_six c.hA).elim
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inr (Or.inl hB)) c.hA).elim
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inl hB) c.hA).elim

theorem case18_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C18 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, hL⟩ := h
  · have hz := hF.desc.hs G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB
    unfold A314Statement
    iterate 10 right
    left
    exact ⟨hB, hL, hz⟩
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isZ4Cubed h)
      (fun Y _ hY => Or.inl hY) c.hA).elim

theorem case19_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C19 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, -⟩ := h
  · exact (excl_model_ext hF.model hB (fun V _ _ h => solvable_of_isExtraspecial2 h)
      (fun Y _ hY => Or.inl hY) c.hA).elim
  · exact (excl_hat_ext hB (fun V _ _ h => solvable_isE2 6 V h) (fun Y _ hY => hY)
      hS_alt_six c.hA).elim

theorem case20_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312C20 B L) : A314Statement T B L := by
  obtain ⟨hB | hB, h11, hL⟩ := h
  · have hz := hF.desc.ru G L (T ⊓ L) B c.hTL c.hB1 c.hBL.le c.hBL.ne hL hB h11
    unfold A314Statement
    iterate 11 right
    left
    exact ⟨hB, h11, hL, hz⟩
  · exact (excl_model_mod hF.model (CFSG.pCore 2 ↥B) (solvable_pCore_two _)
      (Or.inl hB) c.hA).elim

theorem of_case_F4 (hF : A314Facts_F4) (c : Ctx T B L) (h : A312Case B L) : A314Statement T B L := by
  unfold A312Case at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact case2_F4 hF c h
  · exact case3_F4 hF c h
  · exact case4_F4 hF c h
  · exact case5_F4 hF c h
  · exact case6_F4 hF c h
  · exact case7 c h
  · exact case8_F4 hF c h
  · exact case9_F4 hF c h
  · exact case10_F4 hF c h
  · exact case11 c h
  · exact case12_F4 hF c h
  · exact case13_F4 hF c h
  · exact case14_F4 hF c h
  · exact case15_F4 hF c h
  · exact case16_F4 hF c h
  · exact case17_F4 hF c h
  · exact case18_F4 hF c h
  · exact case19_F4 hF c h
  · exact case20_F4 hF c h

end CFSG.Quasithin.A314
