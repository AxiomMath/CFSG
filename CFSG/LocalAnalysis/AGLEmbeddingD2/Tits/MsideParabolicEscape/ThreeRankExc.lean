module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTwE6
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.TauCetiBridge CFSG.TauCetiBridge.Even

set_option linter.unusedSectionVars false


theorem pRank_three_eq_zero_of_coprime {S : Type} [Group S] [Finite S]
    (h : Nat.Coprime 3 (Nat.card S)) : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 0 := by
  refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_)
  have hE1 : E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h3 : x ^ 3 = 1 := hE.2 x hx
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2 : orderOf x ∣ Nat.card S := orderOf_dvd_natCard x
    have : orderOf x ∣ Nat.gcd 3 (Nat.card S) := Nat.dvd_gcd h1 h2
    rw [h] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  rw [hE1]
  simp

theorem exists_untwisted_model {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid)
    {S : Type} [Group S] (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nonempty (S ≃* AdjointQuotient τ K) := by
  have hF := card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (fieldOf q 1) hF
  exact ⟨fieldOf q 1, inferInstance, inferInstance, ⟨e.trans φ.symm⟩⟩

theorem pRank_three_ne_one_f4 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.f4 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .F4) (Or.inl rfl) (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem pRank_three_ne_one_e6 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E6 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e6 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E6) (Or.inr (Or.inl rfl)) (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem pRank_three_ne_one_e7 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E7 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e7 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
    (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem pRank_three_ne_one_e8 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.E8 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.e8 q hv e
  have := four_le_pRank_three_adjointQuotient_any (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
    (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem pRank_three_ne_one_g2 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨K, _, _, ⟨φ⟩⟩ := exists_untwisted_model chevalleyBridgesAll.g2 q hv e
  have := two_le_pRank_three_adjointQuotient_G2 (K := K)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at this
  omega

theorem involutive_of_card_sq {k : Type} [Field k] [Finite k] {θ : k →+* k} {q : ℕ}
    (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) : ∀ c, θ (θ c) = c := by
  intro c
  have := Fintype.ofFinite k
  rw [hθq, hθq, ← pow_mul, ← sq, ← hk, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem pRank_three_ne_one_twistedE6 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  have hm : 0 < TwistTag.E6.order := by decide
  have hF := card_fieldOf q hm
  obtain ⟨φ⟩ := chevalleyBridgesAll.twistedE6 q hv (fieldOf q TwistTag.E6.order) hF
    (frobOf q TwistTag.E6.order) (frobOf_apply q TwistTag.E6.order)
  have hk : Nat.card (fieldOf q TwistTag.E6.order) = q.card ^ 2 := hF
  have hθq : ∀ c, (frobOf q TwistTag.E6.order) c = c ^ q.card := frobOf_apply q _
  have hq2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    calc 2 ≤ q.p := q.prime_p.two_le
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have hK4 : 4 ≤ Nat.card (fieldOf q TwistTag.E6.order) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q.card ^ 2 := Nat.pow_le_pow_left hq2 2
  have := two_le_pRank_three_twistedE6 (involutive_of_card_sq hk hθq) hK4 (e.trans φ.symm)
  omega

theorem pRank_three_ne_one_reeG2 {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.reeG2 m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  have hmod := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmod
  omega

theorem pRank_three_ne_one_suzuki {S : Type} [Group S] [Finite S] (m : ℕ)
    (hv : (LieTypeIndex.suzuki m).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  have hc := CFSG.LieType.SeitzGeneration.card_cat_suzuki_coprime_three hv
  have hc' : Nat.Coprime 3 (Nat.card S) := by rw [Nat.card_congr e.toEquiv]; exact hc
  rw [pRank_three_eq_zero_of_coprime hc']
  omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
