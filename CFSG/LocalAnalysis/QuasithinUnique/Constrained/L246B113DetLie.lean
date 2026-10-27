module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native
public import CFSG.Quasithin.Background.B1More13Defs

public section

namespace CFSG.QuasithinUnique.Bridge.B113Det

open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem isAlt_of_center_eq_bot {L : Type} [Group L] {n : ℕ} (hc : Subgroup.center L = ⊥)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) : IsAlt n L :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem isLieAltType_of_alt {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (hA7 : Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center L = ⊥)
    {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) :
    IsLieAltType L := by
  have : Group.IsPerfect L := hq.1
  let π : L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := CFSG.QuasithinUnique.Ch1.surjective_comp_mk'_center e
  have hker : π.ker = Subgroup.center L := CFSG.QuasithinUnique.Ch1.ker_comp_mk'_center_eq e
  have hcov := CFSG.SectionRank.alternating_small_odd_cover_bound h5 h8 π hπ hker.le
    (by rw [hker]; exact hodd)
  rw [hker] at hcov
  have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hn with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨5, isAlt_of_center_eq_bot (hcov.1 (Or.inl rfl)) e⟩)
  · rcases hcov.2 (Or.inl rfl) with h1 | h3
    · exact Or.inr (Or.inl ⟨6, isAlt_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ h1) e⟩)
    · exact Or.inr (Or.inr ⟨hq, h3, ⟨e⟩⟩)
  · exact Or.inr (Or.inl ⟨7, isAlt_of_center_eq_bot (hA7 ⟨e⟩) e⟩)
  · exact Or.inr (Or.inl ⟨8, isAlt_of_center_eq_bot (hcov.1 (Or.inr rfl)) e⟩)

theorem isLieAltType_of_native
    {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (hA7 : Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center L = ⊥)
    (h : SQTKCharTwoOrAltNative (L ⧸ Subgroup.center L)) : IsLieAltType L := by
  have hEven : EvenLieType (L ⧸ Subgroup.center L) → IsLieAltType L := fun hE =>
    Or.inl ⟨hq, Or.inl hE⟩
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | h5 | h7 | h9 | hU | h | ⟨n, hn, hm⟩
  · exact isLieAltType_of_alt hq hodd hA7 h5 h8 e
  ·
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h5
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by rw [hF]; norm_num))
    exact isLieAltType_of_alt hq hodd hA7 (n := 5) le_rfl (by norm_num) (e.trans e5)
  ·
    have h32 := CFSG.RankThree.PartTwo.Sec3.statedClassicalModel_psl_three_two_of_seven h7
      (by norm_num)
    exact hEven ⟨.PSL, 3, 1, h32.1, Or.inl ⟨by decide, h32⟩⟩
  ·
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h9
    have : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
    obtain ⟨e6⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism F hcard
    exact isLieAltType_of_alt hq hodd hA7 (n := 6) (by norm_num) (by norm_num)
      ((e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans e6)
  ·
    exact Or.inl ⟨hq, Or.inr hU⟩
  ·
    rcases h with ⟨f, h⟩ | h
    · rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · exact hEven ⟨.PSL, 2, f, h.1, Or.inl ⟨by decide, h⟩⟩
      · exact hEven ⟨.PSL, 3, f, h.1, Or.inl ⟨by decide, h⟩⟩
      · exact hEven ⟨.PSU, 3, f, h.1, Or.inl ⟨by decide, h⟩⟩
      · exact hEven ⟨.PSp, 2, f, h.1, Or.inl ⟨by decide, h⟩⟩
      · exact hEven ⟨.G2, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩
      · exact hEven ⟨.trialityD4, 0, f, h.1, Or.inr (Or.inl ⟨rfl, by decide, h⟩)⟩
      · exact hEven ⟨.twistedF4, 0, f, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩
      · exact hEven ⟨.twistedB2, 0, f, suzukiModel_admissible h,
          Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))⟩
    · exact hEven ⟨.Tits, 0, 1, h.1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))⟩
  ·
    exact hEven ⟨.PSL, n, 1, hm.1, Or.inl ⟨by decide, hm⟩⟩

end CFSG.QuasithinUnique.Bridge.B113Det
