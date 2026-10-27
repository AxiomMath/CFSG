module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.Quasithin.Recognition.CertG2Two
public import CFSG.RankThree.PartOne.KF.ClsExcG2
public import CFSG.LargeExtraspecial.S63BU33
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LargeExtraspecial.AS35COdd
public import CFSG.LargeExtraspecial.AS35CS63E
public import CFSG.LargeExtraspecial.AS35CS63F
public import CFSG.LargeExtraspecial.AS35CS63J2
public import CFSG.LargeExtraspecial.AS35Pre
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Timmesfeld.CorollaryBOutcome

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem statedClassicalModel_of_fU33 {S : Type} [Group S] (h : catalogIs S fU33) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 3 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · exact CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hi e
      · exact hi.elim
    | _ => exact hi.elim

theorem rankBound_u33_three {S : Type} [Group S] [Finite S] (h : catalogIs S fU33) :
    ∀ E T : Subgroup S, IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ 3 := by
  intro E T hE hT2 hT hET
  by_contra hlt
  push Not at hlt
  obtain ⟨E', hE'E, hE'c⟩ := exists_sub_card_pow (n := 2) Nat.prime_three hE
    (sq_le_card_of_lt Nat.prime_three hE hlt)
  have hm := statedClassicalModel_of_fU33 h
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
    (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel S .PSU 3 3 1)
  haveI : Fintype (ZMod 2) := ZMod.fintype 2
  obtain ⟨e2⟩ := CFSG.Quasithin.g2_derived_mulEquiv_PSU3 (ZMod 2) (by simp)
  let φ : S ≃* ↥⁅adjointGroup Tag.G2 (ZMod 2), adjointGroup Tag.G2 (ZMod 2)⁆ := e1.trans e2.symm
  have hle : ⁅adjointGroup Tag.G2 (ZMod 2), adjointGroup Tag.G2 (ZMod 2)⁆ ≤
      adjointGroup Tag.G2 (ZMod 2) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (adjointGroup Tag.G2 (ZMod 2)).mul_mem
      ((adjointGroup Tag.G2 (ZMod 2)).mul_mem
        ((adjointGroup Tag.G2 (ZMod 2)).mul_mem ha hb) ((adjointGroup Tag.G2 (ZMod 2)).inv_mem ha))
      ((adjointGroup Tag.G2 (ZMod 2)).inv_mem hb)
  let ι : S →* ↥(adjointGroup Tag.G2 (ZMod 2)) := (Subgroup.inclusion hle).comp φ.toMonoidHom
  have hι : Function.Injective ι := (Subgroup.inclusion_injective hle).comp φ.injective
  have hEp : ∀ g ∈ E'.map ι, g ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x (hE'E hx), map_one]
  refine CFSG.RankThree.PartOne.KFU.no_plane_G2 (K := ZMod 2) Nat.prime_three (by norm_num)
    (by norm_num) (U := T.map ι) (E := E'.map ι) ?_ (hT2.map ι) ?_ hEp ?_
  · intro hbot
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T hι).1 hbot)
  · exact ((Subgroup.map_mono (hE'E.trans hET)).trans (Subgroup.le_normalizer_map ι))
  · rw [Subgroup.card_map_of_injective hι, hE'c]

theorem kDescFam_u33 (p : ℕ) : KDescFam p fU33 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hm := statedClassicalModel_of_fU33 hc
  have hS : Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
  have hZ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    center_eq_bot_of_simple_nonprime hS (by norm_num)
  have hinj : Function.Injective (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)) :=
    conj_injective_of_center_eq_bot hZ
  have hOutle := CFSG.LargeExtraspecial.S63.card_outer_le_two_of_psu33 hinj
    (Or.inl ⟨by decide, hm⟩)
  have hOut : ¬ p ∣ Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) := by
    intro hd
    have hpos : 0 < Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    have := hp.two_le
    omega
  refine (false_of_rank_bound hp hp2 h hcB (MulEquiv.refl _) hZ
    (inner_of_pow_eq_one_of_not_dvd_outer hp hOut) ?_).elim
  by_cases hp3 : p = 3
  · subst hp3
    exact rankBound_u33_three hc
  · exact rankBound_of_not_sq_dvd hp (by
      rw [hS]
      exact not_sq_dvd_of_dvd_smooth_mul (a := 5) (b := 3) (M := 7) hp hp2 hp3
        (by norm_num : Nat.Prime 7).squarefree (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA
