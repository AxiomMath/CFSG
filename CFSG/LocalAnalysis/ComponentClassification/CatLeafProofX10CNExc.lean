module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
public import CFSG.GH74.Generic.GKFTables
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10CNE

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

theorem odd_two_pow_sub_one {f : ℕ} (hf : f ≠ 0) : Odd (2 ^ f - 1) := by
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem odd_orders_psl_two_two {f : ℕ} (hf0 : f ≠ 0) (hf2 : f ≠ 2) :
    Odd (Multiplier.genericOrders .PSL 2 2 f).1 ∧ Odd (Multiplier.genericOrders .PSL 2 2 f).2 ∧
      Odd (Multiplier.exceptionalOrders .PSL 2 2 f).1 ∧
      Odd (Multiplier.exceptionalOrders .PSL 2 2 f).2 := by
  have hexc : Multiplier.exceptionalOrders .PSL 2 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  refine ⟨?_, odd_one, by rw [hexc]; exact odd_one, by rw [hexc]; exact odd_one⟩
  change Odd (Nat.gcd 2 (2 ^ f - 1))
  exact Odd.of_dvd_nat (odd_two_pow_sub_one hf0) (Nat.gcd_dvd_right 2 _)

theorem odd_orders_psu_three_two_two :
    Odd (Multiplier.genericOrders .PSU 3 2 2).1 ∧ Odd (Multiplier.genericOrders .PSU 3 2 2).2 ∧
      Odd (Multiplier.exceptionalOrders .PSU 3 2 2).1 ∧
      Odd (Multiplier.exceptionalOrders .PSU 3 2 2).2 := by
  have hexc : Multiplier.exceptionalOrders .PSU 3 2 2 = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  refine ⟨?_, odd_one, by rw [hexc]; exact odd_one, by rw [hexc]; exact odd_one⟩
  change Odd (Nat.gcd 3 (2 ^ 2 + 1))
  norm_num

theorem lieModel_psl_two_five_of_four {X : Type} [Group X]
    (h : LieModel X .PSL 2 2 2) : LieModel X .PSL 2 5 1 := by
  rcases h with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  obtain ⟨eA⟩ := ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl (by rw [hF]; norm_num))
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  obtain ⟨e5⟩ := ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 5 1) (Or.inr (by rw [hK, pow_one]))
  have hadm : StatedLieAdmissible .PSL 2 5 1 := ⟨by norm_num, le_rfl, by decide⟩
  exact Or.inl ⟨by decide, hadm, GaloisField 5 1, inferInstance, inferInstance, hK,
    ⟨(e.trans eA).trans e5.symm⟩⟩

theorem cfTwoNilpSL2_conclusion_of_exc
    (hGA : TBLit.GriessMultipliersAllModels) {M : Type} [Group M] [Finite M]
    (hq : IsQuasisimple M) (hO : pPrimeCore 2 M = ⊥) (hz : ∃ z ∈ center M, orderOf z = 2)
    (hexc : (∃ p f : ℕ, LieModel (M ⧸ center M) .PSL 2 p f) ∨
      (∃ p f : ℕ, SuzukiModel (M ⧸ center M) p f) ∨ LieModel (M ⧸ center M) .PSL 3 2 2 ∨
      LieModel (M ⧸ center M) .PSU 3 2 2 ∨ Nonempty ((M ⧸ center M) ≃* alternatingGroup (Fin 7))) :
    (∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) K')) ∨
      GH74.GLS.IsDoubleCoverOfAlt M 7 ∨ LieModel (M ⧸ center M) .PSL 3 2 2 ∨
      ¬ 3 ∣ Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzZ, hz2⟩ := hz
  have hZ : IsPGroup 2 (center M) := TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot hO
  have hZ1 : center M ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hzZ
    rw [hzZ, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hnone : ∀ {t : StatedLieTag} {n p f : ℕ}, n ≠ 0 → LieModel (M ⧸ center M) t n p f →
      Odd (Multiplier.genericOrders t n p f).1 → Odd (Multiplier.genericOrders t n p f).2 →
      Odd (Multiplier.exceptionalOrders t n p f).1 →
      Odd (Multiplier.exceptionalOrders t n p f).2 → False := by
    intro t n p f hn hm h1 h2 h3 h4
    have hN := GH74.Generic.noTwoCover_of_griess hGA
      (GH74.Generic.models_of_blueprint_of_ne_zero hn hm) h1 h2 h3 h4
    exact hZ1 (hN M hq hZ ⟨MulEquiv.refl _⟩)
  have hsl : ∀ {p f : ℕ}, p.Prime → p ≠ 2 → LieModel (M ⧸ center M) .PSL 2 p f →
      ∃ (K' : Type) (_ : Field K') (_ : Finite K') (r m : ℕ), r.Prime ∧ r ≠ 2 ∧ 1 ≤ m ∧
        Nat.card K' = r ^ m ∧ 5 ≤ r ^ m ∧
        Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) K') := by
    intro p f hp hp2 hm
    obtain ⟨hf, hfact, ⟨e⟩⟩ := TBLit.psl_two_double_cover hGA
      Milestones.cl_lit_griess_schur_multipliers_central_covers hq hZ hZ1 hp hp2 hm
    obtain ⟨-, h5⟩ := TBLit.lieModel_psl_two_params hm hp2
    exact ⟨GaloisField p f, inferInstance, inferInstance, p, f, hp, hp2, hf,
      GaloisField.card p f hf.ne', h5, ⟨e⟩⟩
  rcases hexc with ⟨p, f, hm⟩ | ⟨p, f, hm⟩ | hm | hm | he
  ·
    have hadm : StatedLieAdmissible .PSL 2 p f := by
      rcases hm with ⟨-, hadm, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact hadm
      all_goals exact absurd h0 (by norm_num)
    obtain ⟨hp, hf, -, h22, -⟩ := hadm
    by_cases hp2 : p = 2
    · subst hp2
      by_cases hf2 : f = 2
      · subst hf2
        exact Or.inl (hsl (by norm_num) (by norm_num) (lieModel_psl_two_five_of_four hm))
      · obtain ⟨h1, h2, h3, h4⟩ := odd_orders_psl_two_two (by omega) hf2
        exact (hnone (by norm_num) hm h1 h2 h3 h4).elim
    · exact Or.inl (hsl hp hp2 hm)
  ·
    refine Or.inr (Or.inr (Or.inr fun h3M => ?_))
    have h3S := RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hm
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (center M), hn] at h3M
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3M with h | h
    · exact h3S h
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  ·
    exact Or.inr (Or.inr (Or.inl hm))
  ·
    obtain ⟨h1, h2, h3, h4⟩ := odd_orders_psu_three_two_two
    exact (hnone (by norm_num) hm h1 h2 h3 h4).elim
  ·
    obtain ⟨e⟩ := he
    refine Or.inr (Or.inl ⟨hq, ?_, ⟨e⟩⟩)
    have : Group.IsPerfect M := hq.1
    set q : M →* alternatingGroup (Fin 7) := e.toMonoidHom.comp (QuotientGroup.mk' (center M))
      with hqdef
    have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hqk : q.ker = center M := by
      ext x
      rw [MonoidHom.mem_ker, hqdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hdvd := card_dvd_of_surjective
      (RankThree.PerfectCover.hopfMultiplierToKer q hqs hqk.le)
      (RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hqk.le)
    rw [(Alternating.Multipliers.schurAlternatingMultiplierInput 7 (by norm_num)).2, hqk]
      at hdvd
    have h6 : Nat.card (center M) ∣ 6 := by simpa using hdvd
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hZ1 (eq_bot_of_card_eq _ hn)
    rw [hn] at h6 ⊢
    have hn1 : n = 1 := by
      by_contra hn1
      have h4 : 2 ^ 2 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
      have := h4.trans h6
      norm_num at this
    rw [hn1, pow_one]

end CFSG.ComponentClassification.CatLeafProof.X10CNE
