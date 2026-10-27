module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Up34Chev2

section Entrywise


theorem noL34Layer_entrywise {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥(adjointGroup τ (fixSubfield σ))) :
    NoL34Layer (entrywiseAdjointAut τ σ) := by
  obtain ⟨-, hinj, -, hJΓ, -, hJnorm, hquot⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  let S : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
  let e : ↥S ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans eJ.symm
  haveI : IsSimpleGroup ↥S := e.isSimpleGroup
  refine noL34_of_simple_normal_comm _ S ?_ ?_ inferInstance ?_ ?_
  · rw [I923.fixSubgroup_entrywiseAdjointAut]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  · rw [I923.fixSubgroup_entrywiseAdjointAut]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    let N : Subgroup ↥(entrywiseFixedGroup τ σ) :=
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
    have hcN : ∀ x y : ↥(entrywiseFixedGroup τ σ), ⁅x, y⁆ ∈ N := by
      intro x y
      have h : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hquot _ _)
      exact (QuotientGroup.eq_one_iff _).1 h
    have h1 := hcN ⟨(a : ModGL τ K), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : ModGL τ K), Subgroup.mem_subgroupOf.1 hb⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    simpa [commutatorElement_def] using h1
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  · exact fun h => hL34 (IsLThreeFour.of_mulEquiv e h)

theorem not_isLThreeFour_of_lieModel_two
    {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hX : Blueprint.LieModel X t n 2 f) (ht : t ≠ .PSL)
    (h : IsLThreeFour X) : False := by
  have h34 : Blueprint.LieModel X .PSL 3 2 2 := isL34Type_of_isLThreeFour h
  exact ht (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) h34 hX).1

end Entrywise

end Up34Chev2

open Up34Chev2

section Exceptional


theorem Up34Chev2.noL34Layer_entrywise_exc {τ : Tag} {t : StatedLieTag} (ht : t ≠ .PSL) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ}
    (hX : Blueprint.LieModel ↥(adjointGroup τ (fixSubfield σ)) t 0 2 d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥) :
    NoL34Layer (entrywiseAdjointAut τ σ) :=
  noL34Layer_entrywise σ hs (I923.exists_noncomm_of_center_bot hZ)
    fun h => not_isLThreeFour_of_lieModel_two hX ht h

theorem up34C2Out_g2 : Up34Chev2Out FamG2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | G2 q =>
    exfalso
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hq3 : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hr
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hm := blueprintLieModel_G2 q hv e
    have hU : UntwistedChevalleyModel S .G2 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := I923.exists_equiv_adjointGroup_of_untwisted hU
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.G2 F) := fun hin =>
      hα ((I923.congr_mem_inner_iff_of_equiv θ α).mp hin)
    obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ :=
      I923.G2_descent q.prime_p hf hq3 F hFcard _ hβ3 hβinn
    have hd : 1 ≤ d := by omega
    haveI : Finite ↥(fixSubfield T) := Subtype.finite
    have hNo : NoL34Layer (entrywiseAdjointAut Tag.G2 T) := by
      by_cases h3 : 3 ≤ q.p ^ d
      · have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) .G2 q.p d :=
          ⟨⟨q.prime_p, hd, rfl, h3⟩, I923.untwisted_adjointGroup hTc⟩
        obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ q.p d hM
        have hZ : Subgroup.center ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) = ⊥ :=
          center_adjointGroup_eq_bot
        have hq2 : q.p = 2 := hc
        rw [hq2] at hM
        exact noL34Layer_entrywise_exc (t := .G2) (by decide) T
          (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp hZ
      · have h2 : q.p ^ d = 2 := by
          have : 2 ≤ q.p ^ d := le_trans q.prime_p.two_le (Nat.le_self_pow (by omega) q.p)
          omega
        refine noL34Layer_of_card_dvd _ (N := 12096) ?_ (by norm_num)
        have hfix : Nat.card ↥(fixSubgroup (entrywiseAdjointAut Tag.G2 T)) =
            Nat.card ↥(entrywiseFixedGroup Tag.G2 T) := by
          rw [I923.fixSubgroup_entrywiseAdjointAut]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
        rw [hfix, card_entrywiseFixedGroup_G2 T (hTc.trans h2)]
        simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
    have h1 : NoL34Layer (MulAut.congr θ α) :=
      noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) hNo
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

theorem up34C2Out_f4 : Up34Chev2Out FamF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | F4 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hm := blueprintLieModel_F4 q hv e
    have hU : UntwistedChevalleyModel S .F4 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := I923.exists_equiv_adjointGroup_of_untwisted hU
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup Tag.F4 F) := fun hin =>
      hα ((I923.congr_mem_inner_iff_of_equiv θ α).mp hin)
    obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := I923.F4_descent hf F hFcard _ hβ3 hβinn
    have hd : 1 ≤ d := by omega
    haveI : Finite ↥(fixSubfield T) := Subtype.finite
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    rw [hq2] at hM
    have hNo : NoL34Layer (entrywiseAdjointAut Tag.F4 T) :=
      noL34Layer_entrywise_exc (t := .F4) (by decide) T
        (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp hZ
    have h1 : NoL34Layer (MulAut.congr θ α) :=
      noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) hNo
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

theorem up34C2Out_e7 : Up34Chev2Out FamE7 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E7 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hm := blueprintLieModel_E7 q hv e
    have hU : UntwistedChevalleyModel S .E7 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := I923.exists_equiv_adjointGroup_of_untwisted hU
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup Tag.E7 F) := fun hin =>
      hα ((I923.congr_mem_inner_iff_of_equiv θ α).mp hin)
    have hdet : ¬ 3 ∣ Tag.E7.cartan.det.natAbs := by
      rw [det_cartan_E7]
      decide
    obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E7 (Or.inr (Or.inl rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hd : 1 ≤ d := by omega
    haveI : Finite ↥(fixSubfield T) := Subtype.finite
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) .E7 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    rw [hq2] at hM
    have hNo : NoL34Layer (entrywiseAdjointAut Tag.E7 T) :=
      noL34Layer_entrywise_exc (t := .E7) (by decide) T
        (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp hZ
    have h1 : NoL34Layer (MulAut.congr θ α) := noL34Layer_of_conj_pow hrj hδ hNo
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

theorem up34C2Out_e8 : Up34Chev2Out FamE8 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E8 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hm := blueprintLieModel_E8 q hv e
    have hU : UntwistedChevalleyModel S .E8 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := I923.exists_equiv_adjointGroup_of_untwisted hU
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup Tag.E8 F) := fun hin =>
      hα ((I923.congr_mem_inner_iff_of_equiv θ α).mp hin)
    have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
      rw [det_cartan_E8]
      decide
    obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hd : 1 ≤ d := by omega
    haveI : Finite ↥(fixSubfield T) := Subtype.finite
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    rw [hq2] at hM
    have hNo : NoL34Layer (entrywiseAdjointAut Tag.E8 T) :=
      noL34Layer_entrywise_exc (t := .E8) (by decide) T
        (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp hZ
    have h1 : NoL34Layer (MulAut.congr θ α) := noL34Layer_of_conj_pow hrj hδ hNo
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

end Exceptional

end CFSG.HardMathSupport.Dickson.Sec6
