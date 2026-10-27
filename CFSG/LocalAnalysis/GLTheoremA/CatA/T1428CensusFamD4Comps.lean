module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamD4Tools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.CatDistinct CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec4 CFSG.PGLModel
  CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false


private theorem card_quot_center_eq_of_center_bot {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center G = ⊥) : Nat.card (G ⧸ Subgroup.center G) = Nat.card G := by
  have h1 : Nat.card ↥(Subgroup.center G) = 1 := by
    rw [hZ]
    exact Subgroup.card_bot
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
  rw [h1, mul_one] at h
  exact h.symm

private theorem notL2_of_card_two_pow_even {G : Type} [Group G] [Finite G] {a O r : ℕ} (hO : Odd O)
    (ha : Even a) (hr : Odd r) (hZ : Subgroup.center G = ⊥) (hcard : Nat.card G = 2 ^ a * O) :
    NotL2 r G := by
  intro hL
  have h1 := catalogIs_isL2n_card_of_odd hr hL
  rw [card_quot_center_eq_of_center_bot hZ, hcard] at h1
  obtain ⟨hre, -⟩ := two_pow_mul_odd_inj (A := (2 ^ r) ^ 2 - 1) (B := O)
    (odd_pow_two_pow_sub_one hr.pos (by norm_num)) hO h1.symm
  rw [hre] at hr
  exact (Nat.not_even_iff_odd.2 hr) ha

private theorem compsWith_notL2_adjointGroup_G2 {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) {r : ℕ} (hr : Odd r) :
    CompsWith (NotL2 r) ↥(adjointGroup Tag.G2 F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  by_cases h2 : Nat.card F = 2
  · obtain ⟨hDs, hDcard⟩ := ExcCopy.g2Two_derived_exc h2
    haveI := hDs
    have hnc := KD264Lie.exists_ne_comm_commutator_adjointGroup_G2_two h2
    have hZ : Subgroup.center ↥(commutator ↥(adjointGroup .G2 F)) = ⊥ := b3Lie_center_eq_bot hnc
    refine compsWith_of_commutator (LieSemisimple.isQuasisimple_of_isSimpleGroup hDs hnc) ?_
    intro hL
    have h1 := catalogIs_isL2n_card_of_odd hr hL
    rw [card_quot_center_eq_of_center_bot hZ, hDcard] at h1
    obtain ⟨hre, hAB⟩ := two_pow_mul_odd_inj (u := r) (v := 5) (A := (2 ^ r) ^ 2 - 1) (B := 189)
      (odd_pow_two_pow_sub_one hr.pos (by norm_num)) (by decide) (by rw [← h1]; norm_num)
    subst hre
    norm_num at hAB
  · have hF3 : 3 ≤ Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    have hperf := ExcCopy.isPerfect_adjointGroup .G2 F (fun _ => hF3)
    obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .G2 F hperf
    haveI := hs
    refine compsWith_of_simple (isComponentProperty_notL2 r) hnc ?_
    have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
    let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf⟩
    have hqcard : Nat.card F = q.card := by
      rw [hF, TauCeti.PrimePower.card_def]
    have hq3 : 3 ≤ q.card := by rw [← hqcard]; exact hF3
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hq3, by simp⟩
    obtain ⟨eq⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F hqcard
    let eX : ↥(adjointGroup .G2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eq
    have hcard : Nat.card ↥(adjointGroup .G2 F) = orderG2 q.card :=
      CatDistinct.ctx_holds.bridge ⟨.G2 q, hv⟩ _ ⟨eX⟩
    obtain ⟨O, hO, hOc⟩ := orderG2_two_pow hf
    refine notL2_of_card_two_pow_even (a := f * 6) hO ⟨f * 3, by ring⟩ hr hZ ?_
    rw [hcard, TauCeti.PrimePower.card_def]
    exact hOc


private theorem notL2_projImage_slPi {π : Bool} {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Sec4.PiField π 2 f K) (hq2 : 2 < 2 ^ f) {r : ℕ} (hr : Odd r) :
    NotL2 r ↥(projImage (Sec4.slPi π 3 (2 ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨hK.prime⟩
  have hf1 : 1 ≤ f := hK.one_le
  let g₀ : ↥(Sec4.slPi π 3 (2 ^ f) K) →* ↥(projImage (Sec4.slPi π 3 (2 ^ f) K)) :=
    (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _).subgroupMap (Sec4.slPi π 3 (2 ^ f) K)
  have hg₀ : Function.Surjective g₀ := MonoidHom.subgroupMap_surjective _ _
  have hg₀k := ker_subgroupMap_mk_le_center (Sec4.slPi π 3 (2 ^ f) K)
  intro hL
  cases π
  · have hKcard : Nat.card K = (2 ^ f) ^ 2 := hK.card
    have hKcard' : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hKcard
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hKcard', ← pow_mul, mul_comm])
    have hmq : ((2 : ℕ) + 1, 2 ^ f) ≠ ((3 : ℕ), 2) := fun h => by
      have := (Prod.mk.inj h).2
      omega
    have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2)
      (f := f) hKcard (by omega : 3 ≤ 2 + 1) hmq
    exact false_of_SU_centerQuot_isL2n (E := K) (r := 2) (t := f) le_rfl hf1 hmq hKcard
      hQ.1.1.commutator_eq_top g₀ hg₀ hg₀k hr hL
  · have hKcard : Nat.card K = 2 ^ f := hK.card
    let eSL : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(Sec4.slPi true 3 (2 ^ f) K) :=
      (MonoidHom.ofInjective
        (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := K))).trans
        (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 K).symm)
    exact false_of_SL_three_centerQuot_isL2n (E := K) hf1 hKcard
      (slFactorFacts_holds K 3 (by norm_num) (fun h => absurd h (by norm_num))).perfect
      (g₀.comp eSL.toMonoidHom) (hg₀.comp eSL.surjective) (by
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hg₀k).trans
          (Subgroup.comap_center_le_center (f := eSL.toMonoidHom) eSL.injective)) hr hL

private theorem compsWith_notL2_projImage_glPi {π : Bool} {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Sec4.PiField π 2 f K) (hπ2 : π = true → 2 < 2 ^ f) {r : ℕ} (hr : Odd r) :
    CompsWith (NotL2 r) ↥(projImage (Sec4.glPi π 3 (2 ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hp := hK.prime
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  intro J hJ
  by_cases hq2 : 2 < 2 ^ f
  · haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _)
        (QuotientGroup.mk'_surjective _)
    haveI : Finite ↥(projImage (Sec4.glPi π 3 (2 ^ f) K)) := Subtype.finite
    have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
    have hR := Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hK hq2
    have hSP : projImage (Sec4.slPi π 3 (2 ^ f) K) ≤ projImage (Sec4.glPi π 3 (2 ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    let eR : ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (2 ^ f) K))) ≃*
        ↥(projImage (Sec4.slPi π 3 (2 ^ f) K)) :=
      (MulEquiv.subgroupCongr hR).trans (Subgroup.subgroupOfEquivOfLe hSP)
    have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (2 ^ f) K)) :=
      Sec13.isPerfect_projImage_slPi hK hq2
    have hsS := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
    haveI := hsS
    have hqS : CFSG.IsQuasisimple ↥(projImage (Sec4.slPi π 3 (2 ^ f) K)) :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
        (Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperfS)).1
    have hqR : CFSG.IsQuasisimple
        ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (2 ^ f) K))) :=
      CFSG.IsQuasisimple.of_mulEquiv eR hqS
    have hPJ : NotL2 r ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (2 ^ f) K))) :=
      (isComponentProperty_notL2 r).of_mulEquiv eR.symm (notL2_projImage_slPi hK hq2 hr)
    exact compsWith_of_perfectResidual hqR hPJ J hJ
  · have h2 : 2 ^ f = 2 := by
      have := hp.two_le
      have h3 : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := hK.one_le; omega) 2
      omega
    cases π
    · haveI := Sec13.isSolvable_projImage_glPi_two hK h2
      exfalso
      obtain ⟨hp', hs⟩ := hJ.2.2
      haveI := hs.toNontrivial
      haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
      exact absurd hp' (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J))
    · exact absurd (hπ2 rfl) hq2

theorem compsWith_notL2_triality_outer {f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hr : Odd r) {K₃ : Type}
    [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsWith (NotL2 r) ↥(fixSubgroup φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact compsWith_triality_outer (ℓ := 2) (f := f) (isComponentProperty_notL2 r)
    (fun h5 _ _ _ _ _ _ _ _ _ _ _ => absurd h5 (by norm_num))
    (fun hF => compsWith_notL2_adjointGroup_G2 hf hF hr)
    (fun π hπ hF => compsWith_notL2_projImage_glPi (π := π) (f := f)
      ⟨Nat.prime_two, hf, hF⟩ hπ hr)
    (by norm_num) hf hK₃ Fr hFr φ hφ3 hφ

end CFSG.LocalAnalysis.GLTheoremA.T1428
