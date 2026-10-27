module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)
open CFSG.HardMathSupport.Dickson.Sec6 (FamTriD4 blueprintLieModel_trialityD4)

theorem card_u42_lt_g2Order {Q : ℕ} (hQ : 4 ≤ Q) : 25920 < Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
  have h1 : 4096 ≤ Q ^ 6 :=
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
  have h2 : 16 ≤ Q ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  calc 25920 < 4096 * 4095 * 15 := by norm_num
    _ ≤ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)

theorem checkSL_u4two_triD4 : ∀ q < 30, 2 ≤ q → q ^ 3 ∣ 25920 →
    25920 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_u4two_triD4 : ∀ q < 30, 2 ≤ q → q ^ 3 ∣ 25920 →
    25920 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

section Layer


theorem u42Layer_fieldActor_two_all {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    U42Layer (fieldActor (t := TwistTag.D4) σ σ) False := by
  haveI := finite_graphFixedRootGroup_D4 σ
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    refine u42Layer_of_card_dvd _ (N := 12096) ?_ (by norm_num)
    rw [card_fixSubgroup_fieldActor Nat.prime_two le_rfl hK σ hσ]
    norm_num [lieOrderNumerator]
  · obtain ⟨hs, hnab⟩ := simple_fixSubgroup_fieldActor_two h hK σ hσ
    refine u42Layer_of_fixed_equiv _ (MulEquiv.refl _) hs hnab fun hT => ?_
    have h1 := CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
    rw [card_fixSubgroup_fieldActor Nat.prime_two (by omega) hK σ hσ] at h1
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
    have := card_u42_lt_g2Order h4
    simp only [lieOrderNumerator] at h1
    omega

theorem u42Layer_of_equiv_projImage {p f : ℕ} {K : Type} [Field K] [Fact p.Prime] {π : Bool}
    (hK : PiField π p f K) (hq2 : 2 < p ^ f) {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (e : ↥(fixSubgroup δ) ≃* ↥(projImage (glPi π 3 (p ^ f) K))) {G : Prop}
    (hG : catalogIs ↥(projImage (slPi π 3 (p ^ f) K)) S9.isU4two → G) : U42Layer δ G := by
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
  exact u42Layer_of_equiv_normal_simple δ e S hsol hs hnab fun hT =>
    hG (catalogIs_of_mulEquiv eS hT)

theorem not_catalogIs_u4two_projImage_slPi_true {f : ℕ} {K : Type} [Field K]
    (hK : PiField true 2 f K) :
    ¬ catalogIs ↥(projImage (slPi true 3 (2 ^ f) K)) S9.isU4two := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_true_equiv hK
  exact (KFacts.KS14.isEmpty_mulEquiv_projSL_three_of_card
    (CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two h)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_u4two_triD4)
    (GaloisField 2 f)).false e

theorem not_catalogIs_u4two_projImage_slPi_false {f : ℕ} {K : Type} [Field K]
    (hK : PiField false 2 f K) :
    ¬ catalogIs ↥(projImage (slPi false 3 (2 ^ f) K)) S9.isU4two := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_false_equiv hK
  exact (KFacts.KS14.isEmpty_mulEquiv_projSU_three_of_card
    (CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two h)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_u4two_triD4) 2 f
    hK.one_le).false e

theorem u42Layer_of_autFix_equiv_even {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {P : Type} [Group P] [Finite P] (φ : MulAut P)
    (ef : ↥(fixSubgroup φ) ≃*
      ↥(Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ))) :
    U42Layer φ False := by
  obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
  have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
  have hf2 : 2 ≤ f := by
    obtain ⟨k, hk⟩ := hfe
    omega
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact u42Layer_of_equiv_projImage hPi hq2 φ (ef.trans e₃) fun hT =>
    (not_catalogIs_u4two_projImage_slPi_true hPi hT).elim

theorem u42Layer_of_autFix_equiv_odd {f : ℕ} (hf : 1 ≤ f) (hfo : Odd f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {P : Type} [Group P] [Finite P] (φ : MulAut P)
    (ef : ↥(fixSubgroup φ) ≃*
      ↥(Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ))) :
    U42Layer φ False := by
  obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K σ hK hσ
  have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hf1 : f = 1
  · subst hf1
    refine u42Layer_of_card_dvd φ (N := 216) ?_ (by norm_num)
    have h1 := card_projImage_glPi_three hPi
    rw [Nat.card_congr (ef.trans e₃).toEquiv, h1]
    norm_num
  · have hf3 : 3 ≤ f := by
      obtain ⟨k, hk⟩ := hfo
      omega
    have hq2 : 2 < 2 ^ f :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
    exact u42Layer_of_equiv_projImage hPi hq2 φ (ef.trans e₃) fun hT =>
      (not_catalogIs_u4two_projImage_slPi_false hPi hT).elim

theorem u42Layer_three_D4_outer_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    U42Layer φ False := by
  haveI := finite_graphFixedRootGroup_D4 σ
  have hG2 : U42Layer (fieldActor (t := TwistTag.D4) σ σ) False :=
    u42Layer_fieldActor_two_all hf hK σ hσ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hφ3
    (by exact hφ) with ⟨β, hβ | hβ⟩ | ⟨⟨e₂⟩⟩
  · rw [hβ]
    exact u42Layer_conj β hG2
  · rw [hβ]
    exact u42Layer_conj β ((u42Layer_inv_iff _ _).2 hG2)
  · have hfix : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    have ef := (MulEquiv.subgroupCongr hfix).trans e₂
    rcases Nat.even_or_odd f with hfe | hfo
    · exact u42Layer_of_autFix_equiv_even hf hfe hK σ hσ φ ef
    · exact u42Layer_of_autFix_equiv_odd hf hfo hK σ hσ φ ef

end Layer

section Family


theorem u42Out_triD4 : U42OuterAt FamTriD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | trialityD4 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_trialityD4 q hv e
    have hexc : ChevalleyExceptionalModel S .trialityD4 q.p q.exponent := by
      rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
      · exact absurd hcl (by decide)
      · exact hexc
      · exact absurd hree (by decide)
      · exact absurd h (by decide)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ := exists_graphFixed_of_chevalleyExceptional hexc
    rw [hq2] at hK hσ
    haveI := finite_graphFixedRootGroup_D4 σ
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβ : MulAut.congr e' α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rintro ⟨c, hc'⟩
      refine not_mem_range_conj_of_not_mem_innAutDerived hα
        ⟨e'.symm c, (MulAut.congr e').injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hc'
    exact hp.apply (u42Layer_congr e'
      (u42Layer_three_D4_outer_two q.exponent_pos hK σ hσ _ hβ3 hβ))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
