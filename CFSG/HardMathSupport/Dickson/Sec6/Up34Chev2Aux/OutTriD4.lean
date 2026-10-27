module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerTransport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.ComponentClassification.CatLeaf
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)
open Up34Chev2

set_option linter.unusedSectionVars false

namespace Up34Chev2

theorem twenty160_lt_g2Order {Q : ℕ} (hQ : 4 ≤ Q) : 20160 < Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
  have h1 : 4096 ≤ Q ^ 6 :=
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
  have h2 : 16 ≤ Q ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  calc 20160 < 4096 * 4095 * 15 := by norm_num
    _ ≤ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)

section Layer


theorem noL34Layer_fieldActor_two_all {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    NoL34Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := finite_graphFixedRootGroup_D4 σ
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    refine noL34Layer_of_card_dvd _ (N := 12096) ?_ (by norm_num)
    rw [card_fixSubgroup_fieldActor Nat.prime_two le_rfl hK σ hσ]
    norm_num [lieOrderNumerator]
  · obtain ⟨hs, hnab⟩ := simple_fixSubgroup_fieldActor_two h hK σ hσ
    refine noL34Layer_of_fixed_equiv _ (MulEquiv.refl _) hs hnab fun hT => ?_
    have h1 := card_eq_of_isLThreeFour hT
    rw [card_fixSubgroup_fieldActor Nat.prime_two (by omega) hK σ hσ] at h1
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
    have := twenty160_lt_g2Order h4
    simp only [lieOrderNumerator] at h1
    omega

theorem noL34Layer_of_equiv_projImage {p f : ℕ} {K : Type} [Field K] [Fact p.Prime] {π : Bool}
    (hK : PiField π p f K) (hq2 : 2 < p ^ f) {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (e : ↥(fixSubgroup δ) ≃* ↥(projImage (glPi π 3 (p ^ f) K)))
    (hL34 : ¬ IsLThreeFour ↥(projImage (slPi π 3 (p ^ f) K))) : NoL34Layer δ := by
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
  exact noL34Layer_of_equiv_normal_simple δ e S hsol hs hnab fun hT =>
    hL34 (IsLThreeFour.of_mulEquiv eS hT)

theorem eq_two_of_isLThreeFour_projImage_slPi_true {f : ℕ} {K : Type} [Field K]
    (hK : PiField true 2 f K) (hfe : Even f)
    (h : IsLThreeFour ↥(projImage (slPi true 3 (2 ^ f) K))) : f = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_true_equiv hK
  have hf1 := hK.one_le
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
  rw [GaloisField.card 2 f (by omega), ← Nat.card_congr e.toEquiv, card_eq_of_isLThreeFour h] at hc
  by_contra hne
  have hf4 : 4 ≤ f := by
    obtain ⟨k, hk⟩ := hfe
    omega
  have hQ : 16 ≤ 2 ^ f :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
  have hgcd : Nat.gcd 3 (2 ^ f - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  generalize 2 ^ f = Q at hQ hc hgcd
  have h1 : 4096 ≤ Q ^ 3 :=
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h2 : 255 ≤ Q ^ 2 - 1 := by
    have : 256 ≤ Q ^ 2 :=
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    omega
  have h3 : 4095 ≤ Q ^ 3 - 1 := by omega
  have h4 : 4096 * (255 * 4095) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have h5 : 20160 * Nat.gcd 3 (Q - 1) ≤ 20160 * 3 := Nat.mul_le_mul_left _ hgcd
  omega

theorem not_isLThreeFour_projImage_slPi_false {f : ℕ} {K : Type} [Field K]
    (hK : PiField false 2 f K) (hf3 : 3 ≤ f)
    (h : IsLThreeFour ↥(projImage (slPi false 3 (2 ^ f) K))) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_projImage_slPi_false_equiv hK
  have hf1 := hK.one_le
  have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 f hf1
  rw [← Nat.card_congr e.toEquiv, card_eq_of_isLThreeFour h] at hc
  have hQ : 8 ≤ 2 ^ f :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hgcd : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  generalize 2 ^ f = Q at hQ hc hgcd
  have h1 : 512 ≤ Q ^ 3 :=
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h2 : 63 ≤ Q ^ 2 - 1 := by
    have : 64 ≤ Q ^ 2 :=
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    omega
  have h3 : 513 ≤ Q ^ 3 + 1 := by omega
  have h4 : 512 * (63 * 513) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have h5 : 20160 * Nat.gcd 3 (Q + 1) ≤ 20160 * 3 := Nat.mul_le_mul_left _ hgcd
  omega

theorem noL34Layer_three_D4_outer_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    f = 2 ∨ NoL34Layer φ := by
  haveI := finite_graphFixedRootGroup_D4 σ
  have hG2 : NoL34Layer (fieldActor (t := TwistTag.D4) σ σ) :=
    noL34Layer_fieldActor_two_all hf hK σ hσ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hφ3
    (by exact hφ) with ⟨β, hβ | hβ⟩ | he₂
  · right
    rw [hβ]
    exact noL34Layer_conj β hG2
  · right
    rw [hβ]
    exact noL34Layer_conj β ((noL34Layer_inv_iff _).2 hG2)
  · obtain ⟨e₂⟩ := he₂
    have hfix : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfix
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
      have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have hq2 : 2 < 2 ^ f :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      by_cases hf22 : f = 2
      · exact Or.inl hf22
      · right
        exact noL34Layer_of_equiv_projImage hPi hq2 φ (ef.trans (e₂.trans e₃)) fun hT =>
          hf22 (eq_two_of_isLThreeFour_projImage_slPi_true hPi hfe hT)
    · right
      obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K σ hK hσ
      have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      by_cases hf1 : f = 1
      · subst hf1
        refine noL34Layer_of_card_dvd φ (N := 216) ?_ (by norm_num)
        have h1 := card_projImage_glPi_three hPi
        rw [Nat.card_congr (ef.trans (e₂.trans e₃)).toEquiv, h1]
        norm_num
      · have hf3 : 3 ≤ f := by
          obtain ⟨k, hk⟩ := hfo
          omega
        have hq2 : 2 < 2 ^ f :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
        exact noL34Layer_of_equiv_projImage hPi hq2 φ (ef.trans (e₂.trans e₃)) fun hT =>
          not_isLThreeFour_projImage_slPi_false hPi hf3 hT

end Layer

end Up34Chev2

section Family


theorem up34C2Out_triD4 : Up34Chev2Out FamTriD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | trialityD4 q =>
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
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
    have hβ : MulAut.congr e' α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rintro ⟨c, hc'⟩
      apply hα
      refine ⟨e'.symm c, (MulAut.congr e').injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hc'
    rcases noL34Layer_three_D4_outer_two q.exponent_pos hK σ hσ _ hβ3 hβ with h2 | hno
    · exact Or.inr (Or.inl ⟨hq2, h2⟩)
    · exact absurd (noL34Layer_congr e' hno) ((up34Pumpup_iff α).1 hp).2.2
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
