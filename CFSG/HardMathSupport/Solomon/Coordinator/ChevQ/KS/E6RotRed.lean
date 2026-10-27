module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompSU3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremB

theorem u3_field_data : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) := by
  refine ⟨Nat.prime_two, by norm_num, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [GaloisField.card 2 (2 * 3) (by omega)]

theorem u3_model {Y : Type} [Group Y] (hY : IsLieQuot Y OuterFourInAux.IsU3EightIndex) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 3 F),
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* unitaryPSU h 3) := by
  have hY' : IsLieQuot Y KSF4SU3.IsU3EightIndexTwo := by
    obtain ⟨⟨d, hv⟩, hd, e⟩ := hY
    refine ⟨⟨d, hv⟩, ?_, e⟩
    cases d with
    | twistedA r q =>
      obtain ⟨rfl, hq⟩ := hd
      exact ⟨q, hq, rfl⟩
    | _ => exact hd.elim
  obtain ⟨e⟩ := KSF4SU3.nonempty_equiv_projSU_of_isLieQuot hY'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField 2 (2 * 3), inferInstance, u3_field_data, ⟨(e.trans
    (CFSG.PGLModel.projSUEquivStatedProj 3 2 3)).trans
      (unitaryPSUEquiv u3_field_data (by norm_num)).symm⟩⟩

theorem isSimpleGroup_unitaryPSU {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) :
    IsSimpleGroup (unitaryPSU h 3) := by
  have hF : Nat.card F = (2 ^ 3) ^ 2 := by rw [h.card, ← pow_mul]
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := h.charP
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 3 hF 3 le_rfl
    (by simp)
  exact (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).isSimpleGroup

section Final


theorem normalized_of_u3_component {X : Type} [Group X] [Finite X]
    (hKG : CFSG.Open.IsKGroup X) {B J : Subgroup X} (hB : CFSG.Open.IsElemAbelian 3 B)
    (hrank : CFSG.Open.GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B)
    (hJ : CFSG.Open.GLAPComponent 3 ⊤ J) (hJL : IsLieQuot ↥J OuterFourInAux.IsU3EightIndex) :
    B ≤ Subgroup.normalizer (J : Set X) := by
  have _ := hKG
  obtain ⟨F, _, h, ⟨e⟩⟩ := u3_model hJL
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set N : Subgroup X := CFSG.Open.GLAPPrimeCore 3 X with hNdef
  set ψ : X →* X ⧸ N := QuotientGroup.mk' N with hψdef
  have hNc : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hN : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hp).1 hNc
  have hker : Nat.Coprime 3 (Nat.card ψ.ker) := by
    rwa [hψdef, QuotientGroup.ker_mk']
  have hcore : CFSG.Open.GLAPPrimeCore 3 (X ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBQ : CFSG.Open.IsElemAbelian 3 (B.map ψ) := hB.map ψ
  have hrankQ : CFSG.Open.GLATwoLocalRank 3 (X ⧸ N) ≤ CFSG.Open.pRank 3 (B.map ψ) :=
    ((glaTwoLocalRank_quotient_le hp (by norm_num) N hN).trans hrank).trans
      (i116red_pRank_le hp N hN hB.isPGroup)
  have hLQ : CFSG.Open.GLAPComponent 3 (⊤ : Subgroup (X ⧸ N)) (J.map ψ) :=
    i116red_map_component hp ψ (QuotientGroup.mk'_surjective N) hker hJ
  have hqb : CFSG.Open.IsQuasisimple ↥(J.map ψ) := i116e_isQuasisimple hcore hLQ
  have hperf : commutator ↥J = ⊤ :=
    (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)).commutator_eq_top
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    ⟨hperf, by haveI := isSimpleGroup_unitaryPSU h; exact e.isSimpleGroup⟩
  have hnJ : ¬ J ≤ N := by
    intro hJN
    have hbot : J.map ψ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨j, hj, rfl⟩
      exact (QuotientGroup.eq_one_iff j).2 (hJN hj)
    haveI := hqb.2
    haveI : Subsingleton ↥(J.map ψ) := by rw [hbot]; infer_instance
    exact not_subsingleton (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ))
      (Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _))
  have hW : (N.subgroupOf J) ≠ ⊤ := fun h1 => hnJ (Subgroup.subgroupOf_eq_top.1 h1)
  haveI : (N.subgroupOf J).Normal := inferInstance
  have hkerJ : (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
    refine le_trans (le_of_eq ?_)
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.l119_normal_le_center hJq hW)
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hj
      have := congrArg Subtype.val hj
      exact (QuotientGroup.eq_one_iff (j : X)).1 this
    · intro hj
      exact Subtype.ext ((QuotientGroup.eq_one_iff (j : X)).2 hj)
  obtain ⟨e1⟩ := LieComp.nonempty_centralQuotient_mulEquiv hperf (ψ.subgroupMap J)
    (MonoidHom.subgroupMap_surjective ψ J) hkerJ
  have hmain := normalized_of_u3_component_reduced hcore hBQ hrankQ hLQ h (e1.symm.trans e)
  intro y hy
  rw [mem_normalizer_iff_gLBConj_eq]
  have hker' : Nat.Coprime 3 (Nat.card ↥((⊤ : Subgroup X) ⊓ ψ.ker)) := by
    rwa [top_inf_eq]
  have hcomp : CFSG.Open.GLAPComponent 3 ⊤ (CFSG.Open.GLBConj y J) := by
    have := glaPComponent_gLBConj hJ y
    rwa [i116red_gLBConj_top] at this
  refine i116red_unique hp ψ hker' hcomp hJ ?_
  rw [i116red_map_gLBConj]
  exact mem_normalizer_iff_gLBConj_eq.1 (hmain ⟨y, hy, rfl⟩)

end Final

end KSFourU
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
