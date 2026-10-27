module

public import CFSG.CGT.Foote82.T66.BranchASmallMcLShape
public import CFSG.CGT.Foote82.T66.BranchASmallMcLPerfect
public import CFSG.CGT.Foote82.T66.BranchASmallModels
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLOrth
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11 CFSG.ComponentClassification.OutcomeLocal
open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem finrank_tildeV_of_type
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3) :
    (IsAltNaturalModule L 6 ∧ Module.finrank (ZMod 2) (TildeV L) = 4) ∨
      6 ≤ Module.finrank (ZMod 2) (TildeV L) := by
  rcases htype with h | h | h
  · exact Or.inl ⟨h, finrank_tildeV_alt6 h⟩
  · right
    rw [finrank_tildeV_omegaMinus h]
  · right
    rw [finrank_tildeV_omegaMinus h]
    norm_num

theorem card_L_of_type
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3) :
    (IsAltNaturalModule L 6 ∧ Nat.card ↥L = 360) ∨ Nat.card ↥L = 25920 ∨
      Nat.card ↥L = 197406720 := by
  rcases htype with h | h | h
  · obtain ⟨e⟩ := mulEquiv_of_alt6 h hc.faithful
    exact Or.inl ⟨h, (Nat.card_congr e.toEquiv).trans card_alt_six⟩
  · obtain ⟨e⟩ := mulEquiv_of_omegaMinus h hc.faithful
    exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans card_omegaMinusTwo_two))
  · obtain ⟨e⟩ := mulEquiv_of_omegaMinus h hc.faithful
    exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans card_omegaMinusTwo_three))

theorem card_mapGL_L : Nat.card ↥(mapGL L) = Nat.card ↥L :=
  (Nat.card_congr (L.equivMapOfInjective _ (toGL : GLV V ≃* _).injective).toEquiv).symm

theorem false_of_shape
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3)
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1)
    (hzE : z ∉ layerIn G) : False := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hdV := hc.finrank_tildeV_of_type htype
  have hn2 := hc.finrank_tildeV_add_two_le hdim
  have hn6 : 6 ≤ Module.finrank (ZMod 2) V := by
    rcases hdV with ⟨-, h⟩ | h <;> omega
  have htr := isF2Transvection_toGL hc.z_mul_z hc.z_ne_one hdim
  obtain ⟨S, hS, hGS⟩ := hc.genByTransvections_mapGL hdim
  have hidx := hc.relIndex_eq_two hdim hzE
  have hEperf : ⁅mapGL (layerIn G), mapGL (layerIn G)⁆ = mapGL (layerIn G) := by
    rw [← mapGL_commutator, hc.layerIn_perfect]
  have hEne : mapGL (layerIn G) ≠ ⊥ := by
    intro h
    apply hc.layerIn_ne_bot
    apply mapGL_injective
    rw [h]
    exact (Subgroup.map_bot _).symm
  obtain ⟨hE, hcases⟩ := shape_of_perfect_index_two (by omega) (mapGL G) (mapGL (layerIn G))
    ⟨S, hS, hGS⟩ hc.irreducible_mapGL (mapGL_mono (Subgroup.map_subtype_le _)) hidx hEperf hEne
  have hzG' : toGL z ∈ mapGL G := toGL_mem_mapGL hc.z_mem
  have hzE' : toGL z ∉ ⁅mapGL G, mapGL G⁆ := by
    rw [← hE]
    intro h
    exact hzE (by simpa using mem_mapGL.1 h)
  have hcomp := hc.isComponentOf_mapGL
  rw [hE] at hcomp
  have hcardL := hc.card_mapGL_L
  have hcardT := hc.card_L_of_type htype
  rcases hcases with ⟨h4, -⟩ | ⟨Q, hQ, hO⟩ | ⟨heven, hsym⟩
  · omega
  ·
    have hOQ : mapGL G = orthGL Q := hO
    rw [hOQ] at hidx hE hzG' hzE' hcomp
    rw [hE] at hidx
    obtain ⟨k, hk, ⟨Φ⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCent.orthTransvectionCent_holds V Q hQ
        hidx (toGL z) hzG' htr hzE'
    by_cases hk3 : k = 3
    ·
      subst hk3
      rcases hdV with ⟨hA6, -⟩ | h
      · obtain ⟨eL⟩ := mulEquiv_of_alt6 hA6 hc.faithful
        rcases isOmegaModel_of_orth Q hQ (T := mapGL (layerIn G)) hE with ⟨m, hm⟩ | ⟨m, hm⟩
        · have hm3 : m = 3 := by
            obtain ⟨φ, -⟩ := hm
            have := LinearEquiv.finrank_eq φ
            rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_plus] at this
            omega
          subst hm3
          exact hc.conf.std.extremal.not_concl
            (Or.inr (Or.inl ⟨6, 1, le_rfl, le_rfl, ⟨eL⟩, isAltHeartFor_eight_of_plus hm⟩))
        · have hm2 : m = 2 := by
            obtain ⟨φ, -⟩ := hm
            have := LinearEquiv.finrank_eq φ
            rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus] at this
            omega
          subst hm2
          exact hc.conf.std.extremal.not_concl (Or.inr (Or.inr ⟨⟨eL⟩, isOmegaMinusFor_of_model hm⟩))
      · omega
    ·
      have hk4 : 4 ≤ k := by
        rcases hdV with ⟨-, h⟩ | h <;> omega
      obtain ⟨hK, hcardK⟩ := isComponentOf_transfer hcomp Φ
      have : IsSimpleGroup ↥(CFSG.Open.StatedSp (k - 1) (ZMod 2)) :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.isSimpleGroup_statedSp_zmod_two
          (by omega)
      have htop := eq_top_of_isComponentOf_simple hK
      rw [htop, Subgroup.card_top, hcardL] at hcardK
      rcases card_statedSp_cases (r := k - 1) (by omega) with h | h
      · rw [h] at hcardK
        rcases hcardT with ⟨-, h'⟩ | h' | h' <;> omega
      · rw [hcardK] at h
        rcases hcardT with ⟨-, h'⟩ | h' | h' <;> rw [h'] at h <;> norm_num at h
  ·
    obtain ⟨m, hm5, ⟨Ψ⟩, ⟨Φ⟩⟩ :=
      CFSG.HardMathSupport.RichardWeiss.Proving.PLType.symTransvectionCent_holds V (mapGL G) heven
        hsym (by rw [← hE]; exact hEperf) (by rw [← hE]; exact hEne) (toGL z) hzG' htr hzE'
    obtain ⟨hK, hcardK⟩ := isComponentOf_transfer hcomp Φ
    obtain ⟨hm7, hKeq⟩ := eq_alt_of_isComponentOf_perm hK
    rw [hKeq, hcardL] at hcardK
    have h2L := two_mul_card_alt (m - 2) (by omega)
    rw [hcardK] at h2L
    rcases hcardT with ⟨hA6, h'⟩ | h' | h'
    ·
      obtain ⟨eL⟩ := mulEquiv_of_alt6 hA6 hc.faithful
      have hm8 : m - 2 = 6 := by
        rw [h'] at h2L
        exact (Nat.factorial_inj (by omega)).1 (h2L.symm.trans rfl)
      have hcardE : 2 * Nat.card ↥(mapGL (layerIn G)) = Nat.factorial 8 := by
        rw [hE, Nat.card_congr Ψ.toEquiv, two_mul_card_alt m (by omega)]
        congr 1
        omega
      have hmodel : ∃ m', IsAltModel (mapGL (layerIn G)) m' ∧ 5 ≤ m' := by
        rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
        · obtain ⟨j, hj⟩ := heven
          exact ⟨_, isAltModel_of_sumZero (by omega) ⟨j, by omega⟩ β hβ hE, by omega⟩
        · exact ⟨_, isAltModel_of_heart (by omega) β hβ hE, by omega⟩
      obtain ⟨m', hm', hm'5⟩ := hmodel
      have hm'8 : m' = 8 := by
        obtain ⟨-, θ, -⟩ := hm'
        have h1 := two_mul_card_alt m' (by omega)
        rw [← Nat.card_congr θ.toEquiv, hcardE] at h1
        exact ((Nat.factorial_inj (by norm_num)).1 h1).symm
      subst hm'8
      exact hc.conf.std.extremal.not_concl
        (Or.inr (Or.inl ⟨6, 1, le_rfl, le_rfl, ⟨eL⟩, isAltHeartFor_of_model hm'⟩))
    · rw [h'] at h2L
      exact factorial_ne_51840 _ h2L.symm
    · rw [h'] at h2L
      exact factorial_ne_394813440 _ h2L.symm

theorem false_of_transvection
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3)
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1) : False := by
  by_cases hzE : z ∈ layerIn G
  · have hdV := hc.finrank_tildeV_of_type htype
    have hn2 := hc.finrank_tildeV_add_two_le hdim
    exact hc.false_of_perfect hdim hzE (by rcases hdV with ⟨-, h⟩ | h <;> omega)
  · exact hc.false_of_shape htype hdim hzE

end Hyp

end CFSG.CGT.Foote82.BAS
