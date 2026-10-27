module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.HardMathSupport.Dickson.Sec6.I923

variable {p f : ℕ} {K : Type} [Field K]

theorem nonempty_projImage_slPi_true_equiv [Fact p.Prime] (hK : PiField true p f K) :
    Nonempty (projImage (slPi true 3 (p ^ f) K) ≃* projSL 3 (GaloisField p f)) := by
  have hf := hK.one_le
  have hcard : Nat.card K = p ^ f := hK.card
  have : Finite K := hK.finite
  let φ : K ≃+* GaloisField p f :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hcard
  rw [Sec13.projSL_eq]
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
    (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL φ 3)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩

theorem nonempty_projImage_slPi_false_equiv [Fact p.Prime] (hK : PiField false p f K) :
    Nonempty (projImage (slPi false 3 (p ^ f) K) ≃* projSU 3 p f) := by
  have hf := hK.one_le
  have hcard : Nat.card K = p ^ (2 * f) := by
    rw [hK.card]
    simp only [Sec4.piCard, Bool.cond_false]
    rw [← pow_mul, mul_comm]
  have : Finite K := hK.finite
  let φ : K ≃+* GaloisField p (2 * f) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega) hcard
  rw [Sec13.projSU_eq]
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
    (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩

theorem exists_noncomm_projImage_slPi {π : Bool} (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    ∃ a b : ↥(projImage (slPi π 3 (p ^ f) K)), a * b ≠ b * a := by
  have : Finite K := hK.finite
  haveI := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hperf := Sec13.isPerfect_projImage_slPi hK hq2
  by_contra hcon
  push Not at hcon
  have hc : commutator ↥(projImage (slPi π 3 (p ^ f) K)) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcon y x
  rw [hperf.commutator_eq_top] at hc
  exact top_ne_bot hc

theorem center_projImage_slPi_eq_bot {π : Bool} (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    Subgroup.center ↥(projImage (slPi π 3 (p ^ f) K)) = ⊥ := by
  have : Finite K := hK.finite
  haveI := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  exact center_eq_bot_of_simple (exists_noncomm_projImage_slPi hK hq2)

theorem not_typeL2_projImage_slPi_true [Fact p.Prime] (hK : PiField true p f K) (hq2 : 2 < p ^ f)
    {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (projImage (slPi true 3 (p ^ f) K)) := by
  obtain ⟨e⟩ := nonempty_projImage_slPi_true_equiv hK
  have hf := hK.one_le
  have hadm : StatedLieAdmissible .PSL 3 p f :=
    ⟨hK.prime, hf, by norm_num, fun h => by
      have := (Prod.mk.inj h).2
      omega, fun h => by
      have := (Prod.mk.inj h).1
      omega⟩
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
  have hGF : Nat.card (GaloisField p f) = p ^ f :=
    GaloisField.card p f (by omega)
  rw [hGF] at hc
  refine not_typeL2_of_order hadm (by decide) (by simp) ?_ (center_projImage_slPi_eq_bot hK hq2) hr
  rw [Nat.card_congr e.toEquiv]
  simp only [lieOrderNumerator, lieOrderDivisor]
  rw [hc]
  simp [Finset.prod_Icc_succ_top]

theorem not_typeL2_projImage_slPi_false [Fact p.Prime] (hK : PiField false p f K)
    (hq2 : 2 < p ^ f) {r : ℕ} (hr : 10 ≤ r) : ¬ IsTypeL2 r (projImage (slPi false 3 (p ^ f) K)) := by
  obtain ⟨e⟩ := nonempty_projImage_slPi_false_equiv hK
  have hf := hK.one_le
  have hadm : StatedLieAdmissible .PSU 3 p f :=
    ⟨hK.prime, hf, le_rfl, fun h => by
      have := (Prod.mk.inj h).2
      omega⟩
  have hc := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  refine not_typeL2_of_order hadm (by decide) (by simp) ?_ (center_projImage_slPi_eq_bot hK hq2) hr
  rw [Nat.card_congr e.toEquiv]
  simp only [lieOrderNumerator, lieOrderDivisor]
  rw [hc]
  simp [Finset.prod_Icc_succ_top, Nat.even_iff]

theorem noL2Layer_of_equiv_projImage [Fact p.Prime] {π : Bool} (hK : PiField π p f K)
    (hq2 : 2 < p ^ f) {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (e : ↥(fixSubgroup δ) ≃* ↥(projImage (glPi π 3 (p ^ f) K)))
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥(projImage (slPi π 3 (p ^ f) K))) :
    NoL2Layer δ := by
  have : Finite K := hK.finite
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hSc := Sec13.commutator_projImage_glPi hK hq2
  set S : Subgroup ↥(projImage (glPi π 3 (p ^ f) K)) :=
    (projImage (slPi π 3 (p ^ f) K)).subgroupOf (projImage (glPi π 3 (p ^ f) K)) with hS
  haveI hSn : S.Normal := by
    have h : (commutator ↥(projImage (glPi π 3 (p ^ f) K))).Normal := inferInstance
    rwa [hSc] at h
  have hsol : Group.IsSolvable (↥(projImage (glPi π 3 (p ^ f) K)) ⧸ S) := by
    refine isSolvable_quotient_of_eq' hSc ?_
    exact (inferInstance : Group.IsSolvable
      (Abelianization ↥(projImage (glPi π 3 (p ^ f) K))))
  have eS : ↥S ≃* ↥(projImage (slPi π 3 (p ^ f) K)) := Subgroup.subgroupOfEquivOfLe hSP
  haveI hs0 := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hnab0 := exists_noncomm_projImage_slPi hK hq2
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab0
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩
  exact noL2Layer_of_equiv_normal_simple δ e S hsol hs hnab fun r hr hT =>
    hL2 r hr (l2fld_isTypeL2_of_mulEquiv eS hT)

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
