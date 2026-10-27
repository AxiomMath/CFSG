module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutEntrywise
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnExcRank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem UpD42Pumpup.conj {S : Type} [Group S] [Finite S] (γ : MulAut S) {α : MulAut S}
    (h : UpD42Pumpup S α) : UpD42Pumpup S (γ * α * γ⁻¹) := by
  have := h.congr (γ : S ≃* S)
  convert this using 1
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply]

theorem UpD42Pumpup.of_conj_pow {S : Type} [Group S] [Finite S] {β η δ : MulAut S} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : UpD42Pumpup S β) :
    UpD42Pumpup S η := by
  obtain ⟨hβ3, hβ1, I, hI, hD⟩ := h
  have hbr3 : (β ^ r) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm r 3, pow_mul, hβ3, one_pow]
  have hbr1 : β ^ r ≠ 1 := by
    intro h1
    exact hβ1 (by rw [← hrj, h1, one_pow])
  have hI' : GLAPComponent 3 (fixSubgroup (β ^ r)) I := by
    rwa [Up34Chev2.fixSubgroup_pow_eq_of_pow_pow_up34 hrj]
  have h := UpD42Pumpup.conj δ ⟨hbr3, hbr1, I, hI', hD⟩
  rwa [hδ] at h

private theorem ordG2_two_pow_ne_174182400 {d : ℕ} (hd : 2 ≤ d) :
    ordG2 (2 ^ d) ≠ 174182400 := by
  intro h
  have h12 : (174182400 : ℕ) = 2 ^ 12 * 42525 := by norm_num
  rw [h12] at h
  by_cases hd2 : d = 2
  · subst hd2
    norm_num [ordG2] at h
  · exact (CFSG.Timmesfeld.Orders.profile_ordG2 (by omega)).ne_of_ne (r := 42525)
      (by norm_num) (by omega) h

private theorem ordF4_two_pow_ne_174182400 {d : ℕ} (hd : 1 ≤ d) :
    ordF4 (2 ^ d) ≠ 174182400 := by
  intro h
  have h12 : (174182400 : ℕ) = 2 ^ 12 * 42525 := by norm_num
  rw [h12] at h
  exact (CFSG.Timmesfeld.Orders.profile_ordF4 hd).ne_of_ne (r := 42525)
    (by norm_num) (by omega) h

private theorem ordE7_two_pow_ne_174182400 {d : ℕ} (hd : 1 ≤ d) :
    ordE7 (2 ^ d) ≠ 174182400 := by
  intro h
  have h12 : (174182400 : ℕ) = 2 ^ 12 * 42525 := by norm_num
  rw [h12] at h
  exact (CFSG.Timmesfeld.Orders.profile_ordE7 hd).ne_of_ne (r := 42525)
    (by norm_num) (by omega) h

private theorem ordE8_two_pow_ne_174182400 {d : ℕ} (hd : 1 ≤ d) :
    ordE8 (2 ^ d) ≠ 174182400 := by
  intro h
  have h12 : (174182400 : ℕ) = 2 ^ 12 * 42525 := by norm_num
  rw [h12] at h
  exact (CFSG.Timmesfeld.Orders.profile_ordE8 hd).ne_of_ne (r := 42525)
    (by norm_num) (by omega) h

theorem upD42Chev2Out_of_rank {F : TauCeti.LieTypeIndex → Prop}
    (hrank : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), F d.1 →
      IsCharTwoLieIndex d.1 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
        CFSG.LieType.SeitzGeneration.RankLE2 3 S) :
    UpD42Chev2Out F := by
  intro S _ _ hs hnab d hd hc he α hα hp
  obtain ⟨E, hE, hcard⟩ := hp.exists_elemAbelian_81
  have h9 := hrank S d hd hc he E hE
  rw [hcard] at h9
  norm_num at h9

section Exceptional


theorem upD42Chev2Out_g2 : UpD42Chev2Out FamG2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | G2 q =>
    exfalso
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hq3 : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hr
    have : Fact q.p.Prime := ⟨q.prime_p⟩
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
    have hβinn : MulAut.congr θ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup Tag.G2 F) := fun hin =>
      hα ((I923.congr_mem_inner_iff_of_equiv θ α).mp hin)
    obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ :=
      I923.G2_descent q.prime_p hf hq3 F hFcard _ hβ3 hβinn
    have hd : 1 ≤ d := by omega
    have : Finite ↥(fixSubfield T) := Subtype.finite
    have hPump : UpD42Pumpup ↥(adjointGroup Tag.G2 F) (entrywiseAdjointAut Tag.G2 T) :=
      UpD42Pumpup.of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) (hp.congr θ)
    by_cases h3 : 3 ≤ q.p ^ d
    · have hq2 : q.p = 2 := hc
      have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) .G2 q.p d :=
        ⟨⟨q.prime_p, hd, rfl, h3⟩, I923.untwisted_adjointGroup hTc⟩
      obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ q.p d hM
      have hZ : Subgroup.center ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) = ⊥ :=
        center_adjointGroup_eq_bot
      have hd2 : 2 ≤ d := by
        by_contra hlt
        have h1 : d = 1 := by omega
        subst h1
        norm_num [hq2] at h3
      have hcard : Nat.card ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) ≠ 174182400 := by
        rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hTc, hq2]
        exact ordG2_two_pow_ne_174182400 hd2
      exact hcard (card_of_isD42Type (UpD42Pumpup.isD42_fixSubfield_of_entrywise T hsimp
        (I923.exists_noncomm_of_center_bot hZ) hPump))
    · have h2 : q.p ^ d = 2 := by
        have : 2 ≤ q.p ^ d := le_trans q.prime_p.two_le (Nat.le_self_pow (by omega) q.p)
        omega
      have hdvd := hPump.card_d42_dvd_fixed
      have hfix : Nat.card ↥(fixSubgroup (entrywiseAdjointAut Tag.G2 T)) =
          Nat.card ↥(entrywiseFixedGroup Tag.G2 T) := by
        rw [I923.fixSubgroup_entrywiseAdjointAut]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [hfix, card_entrywiseFixedGroup_G2 T (hTc.trans h2)] at hdvd
      norm_num [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at hdvd
  | _ => exact hF.elim

theorem upD42Chev2Out_f4 : UpD42Chev2Out FamF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | F4 q =>
    exfalso
    have : Fact q.p.Prime := ⟨q.prime_p⟩
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
    have : Finite ↥(fixSubfield T) := Subtype.finite
    have hPump : UpD42Pumpup ↥(adjointGroup Tag.F4 F) (entrywiseAdjointAut Tag.F4 T) :=
      UpD42Pumpup.of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) (hp.congr θ)
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    have hcard : Nat.card ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) ≠ 174182400 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hTc, hq2]
      exact ordF4_two_pow_ne_174182400 hd
    exact hcard (card_of_isD42Type (UpD42Pumpup.isD42_fixSubfield_of_entrywise T hsimp
        (I923.exists_noncomm_of_center_bot hZ) hPump))
  | _ => exact hF.elim

theorem upD42Chev2Out_e7 : UpD42Chev2Out FamE7 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E7 q =>
    exfalso
    have : Fact q.p.Prime := ⟨q.prime_p⟩
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
    have : Finite ↥(fixSubfield T) := Subtype.finite
    have hPump : UpD42Pumpup ↥(adjointGroup Tag.E7 F) (entrywiseAdjointAut Tag.E7 T) :=
      UpD42Pumpup.of_conj_pow hrj (by simpa using hδ) (hp.congr θ)
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) .E7 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    have hcard : Nat.card ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) ≠ 174182400 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hTc, hq2]
      exact ordE7_two_pow_ne_174182400 hd
    exact hcard (card_of_isD42Type (UpD42Pumpup.isD42_fixSubfield_of_entrywise T hsimp
        (I923.exists_noncomm_of_center_bot hZ) hPump))
  | _ => exact hF.elim

theorem upD42Chev2Out_e8 : UpD42Chev2Out FamE8 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E8 q =>
    exfalso
    have : Fact q.p.Prime := ⟨q.prime_p⟩
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
    have : Finite ↥(fixSubfield T) := Subtype.finite
    have hPump : UpD42Pumpup ↥(adjointGroup Tag.E8 F) (entrywiseAdjointAut Tag.E8 T) :=
      UpD42Pumpup.of_conj_pow hrj (by simpa using hδ) (hp.congr θ)
    have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 q.p d :=
      ⟨⟨q.prime_p, hd, rfl⟩, I923.untwisted_adjointGroup hTc⟩
    obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ q.p d hM
    have hZ : Subgroup.center ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hq2 : q.p = 2 := hc
    have hcard : Nat.card ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) ≠ 174182400 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hTc, hq2]
      exact ordE8_two_pow_ne_174182400 hd
    exact hcard (card_of_isD42Type (UpD42Pumpup.isD42_fixSubfield_of_entrywise T hsimp
        (I923.exists_noncomm_of_center_bot hZ) hPump))
  | _ => exact hF.elim

theorem upD42Chev2Out_reeF4 : UpD42Chev2Out FamReeF4 := by
  refine upD42Chev2Out_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | reeF4 m =>
    exact CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)
  | _ => exact hF.elim

theorem upD42Chev2Out_tits :
    UpD42Chev2Out FamTits := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | tits =>
    have hadm : StatedLieAdmissible .Tits 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
    have hm := blueprintLieModel_tits hv e
    obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
      .Tits 0 2 1 hadm hm
    have h7 : 7 ∣ Nat.card S := (by norm_num : 7 ∣ 174182400).trans hp.card_dvd
    have : Nat.card S = 17971200 := by
      simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hord
    rw [this] at h7
    exact absurd h7 (by norm_num)
  | _ => exact hF.elim

theorem upD42Chev2Out_exc_holds :
    UpD42Chev2Out (fun d => FamG2 d ∨ FamF4 d ∨ FamE7 d ∨ FamE8 d) := by
  have h := ((upD42Chev2Out_g2.union upD42Chev2Out_f4).union upD42Chev2Out_e7).union
    upD42Chev2Out_e8
  refine UpD42Chev2Out.mono ?_ h
  intro d hd
  rcases hd with h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h2))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

end Exceptional

end CFSG.HardMathSupport.Dickson.Sec6

end
