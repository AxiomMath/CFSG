module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank

section Certificate

private theorem card_hopfMultiplier_adjointGroup_E6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(adjointGroup .E6 F)) =
      Nat.gcd 3 (Nat.card F - 1) := by
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF
  let χ : AdjointQuotient .E6 F ≃* adjointGroup .E6 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .E6) (K := F))).trans
      QuotientGroup.quotientBot
  have hgriess : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 F)) =
      Nat.gcd 3 (Nat.card F - 1) := by
    have h54 : 5 ≤ Nat.card F ∨ Nat.card F = 4 := by
      rcases eq_or_lt_of_le hn with h | h
      · right
        rw [hF, ← h]
        norm_num
      · left
        rw [hF]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases h54 with h5 | h4
    · obtain ⟨-, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier h5
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    · obtain ⟨-, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.FieldFour.e6_four_hopfMultiplier h4
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [Nat.card_congr ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.trans
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr χ.symm)).toEquiv, hgriess]

theorem exists_cover_e6_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .E6) (hn : 2 ≤ lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (π : ↥(e6Data_valid.minGroup F) →* K),
      Nat.card F = 2 ^ lab.n ∧ Function.Surjective π ∧
        π.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F) := by
  obtain ⟨hQ, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n :=
    lieModel_of_markedModel_E6 ht hM
  obtain ⟨-, F, hField, hFinite, hCard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hField
  letI : Finite F := hFinite
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hCard
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  have hperfK : Group.IsPerfect K := hQ.1
  have hperfS : Group.IsPerfect ↥(e6Data_valid.minGroup F) := CFSG.LieType.CurtisTits.isPerfect_e6 F
  let χ : AdjointQuotient .E6 F ≃* adjointGroup .E6 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .E6) (K := F))).trans
      QuotientGroup.quotientBot
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E6 F := φ.trans χ
  let p₀ : ↥(e6Data_valid.minGroup F) →* ↥(adjointGroup .E6 F) := e6Isogeny F
  have hp₀ : Function.Surjective p₀ := e6Isogeny_surjective F
  have hker₀ : p₀.ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
  have hmult : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(adjointGroup .E6 F)) =
      Nat.card p₀.ker * 1 := by
    rw [mul_one, hker₀, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1,
      card_hopfMultiplier_adjointGroup_E6 hn hCard]
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 1 := by simp
  obtain ⟨α, hα, hαcomp⟩ :=
    exists_surjective_of_hopfMultiplier_card hperfS hperfK p₀ hp₀ (le_of_eq hker₀) θ hcop
      hmult
  refine ⟨F, hField, hFinite, α, hCard, hα, ?_⟩
  intro x hx
  have h1 : p₀ x = 1 := by
    have h2 := DFunLike.congr_fun hαcomp x
    rw [MonoidHom.mem_ker] at hx
    simp only [MonoidHom.comp_apply] at h2
    rw [hx, map_one] at h2
    simpa using h2.symm
  rw [← hker₀]
  exact h1

theorem exists_cover_twE6_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (θ : k →+* k),
      Nat.card k = (2 ^ lab.n) ^ 2 ∧ (∀ c, θ c = c ^ (2 ^ lab.n)) ∧
      ∃ (π : ↥(fixedGroup k θ) →* K), Function.Surjective π ∧
        π.ker ≤ Subgroup.center ↥(fixedGroup k θ) := by
  obtain ⟨hQ, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n :=
    lieModel_of_markedModel_twE6 ht hM
  obtain ⟨-, -, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM'
  obtain ⟨k, hkfield, hkfin, hkcard, θ, hθ, ⟨e⟩⟩ := hT
  letI : Field k := hkfield
  letI : Finite k := hkfin
  letI : Fintype k := Fintype.ofFinite k
  letI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  haveI : Finite ↥(fixedGroup k θ) := Subtype.finite
  have hk2 : Nat.card k = (2 ^ lab.n) ^ 2 := by
    rw [hkcard]
    rfl
  have hθ2 : ∀ c, θ (θ c) = c := by
    intro c
    have hpow : c ^ Nat.card k = c := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [hθ, hθ, ← pow_mul,
      show 2 ^ lab.n * 2 ^ lab.n = Nat.card k by rw [hk2, pow_two]]
    exact hpow
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk2, pow_two]
    calc 4 ≤ (2 ^ 2) * 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n * 2 ^ lab.n :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hn)
          (Nat.pow_le_pow_right (by norm_num) hn)
  have hperfK : Group.IsPerfect K := hQ.1
  have hperfS : Group.IsPerfect ↥(fixedGroup k θ) :=
    CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card θ hθ2 hk4
  have hZt : Subgroup.center
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot
      (σ := θ) Nat.prime_two (by omega) hk2 hθ
  let θm : K ⧸ Subgroup.center K ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) :=
    e.trans (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv θ hZt)
  let p₀ : ↥(fixedGroup k θ) →*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog θ hθ2 hk4
  have hp₀ : Function.Surjective p₀ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog_surjective θ hθ2 hk4
  have hker₀ : p₀.ker = Subgroup.center ↥(fixedGroup k θ) := by
    refine le_antisymm
      (fun x hx => CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one
        θ hθ2 hk4 hx) ?_
    intro x hx
    rw [MonoidHom.mem_ker]
    have hc : p₀ x ∈ Subgroup.center
        ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := hp₀ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rwa [hZt, Subgroup.mem_bot] at hc
  have hZcard : Nat.card (Subgroup.center ↥(fixedGroup k θ)) =
      Nat.gcd 3 (2 ^ lab.n + 1) :=
    (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (q := 2 ^ lab.n) hk2 hθ).1
  have hMcardF : Nat.card (CFSG.Open.griessHopfMultiplier
      (DerivedCentralQuotient (twistedFixedGroup .E6 k θ))) =
      Nat.gcd 3 (2 ^ lab.n + 1) :=
    CFSG.LocalAnalysis.GLTheoremA.card_griessHopfMultiplier_twE6 (q := 2 ^ lab.n)
      (by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn)
      hk2 hθ
  have hhopf : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ)) =
      Nat.gcd 3 (2 ^ lab.n + 1) := by
    rw [Nat.card_congr ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.trans
      (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv θ hZt).symm)).toEquiv,
      hMcardF]
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ)) =
      Nat.card p₀.ker * 1 := by
    rw [mul_one, hker₀, hhopf, hZcard]
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 1 := by simp
  obtain ⟨α, hα, hαcomp⟩ :=
    exists_surjective_of_hopfMultiplier_card hperfS hperfK p₀ hp₀ (le_of_eq hker₀) θm hcop
      hcard
  refine ⟨k, hkfield, hkfin, θ, hkcard, hθ, α, hα, ?_⟩
  intro x hx
  have h1 : p₀ x = 1 := by
    have h2 := DFunLike.congr_fun hαcomp x
    rw [MonoidHom.mem_ker] at hx
    simp only [MonoidHom.comp_apply] at h2
    rw [hx, map_one] at h2
    simpa using h2.symm
  rw [← hker₀]
  exact h1

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
