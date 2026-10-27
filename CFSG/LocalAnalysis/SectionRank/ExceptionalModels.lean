module

public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LieType.Chevalley.CharTwoTwistRank
public import CFSG.LieType.BorelTits.Twisted

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem three_mul_le_pRank_adjointQuotient_G2
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] (hK : Nat.card K = p ^ f) :
    3 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup (AdjointQuotient .G2 K)) := by
  have : CharP K p := charP_of_natCard_eq_pow hK
  have hc := Holds.coprime_card_center (holds_adjointGroup_tag .G2 K p)
  rw [pRank_quotient_eq _ fun h => by
    have := Nat.Coprime.coprime_dvd_left h hc
    exact hp.out.one_lt.ne' ((Nat.coprime_self p).1 this)]
  exact three_mul_le_pRank_G2 hK

theorem pRank_twistedDerivedQuotient
    {t : TwistTag} {K : Type} [Field K] [Finite K]
    (σ : K →+* K) {p : ℕ} [Fact p.Prime] [CharP K p] (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ)
    [Finite (DerivedCentralQuotient (twistedFixedGroup t K σ))] :
    CFSG.Open.pRank p (⊤ : Subgroup (DerivedCentralQuotient (twistedFixedGroup t K σ))) =
      CFSG.Open.pRank p (⊤ : Subgroup (commutator (twistFixed t K σ))) := by
  obtain ⟨S, hS⟩ := exists_sylow_le_commutator_twistFixed t K σ p hσ hU
  exact pRank_derivedCentralQuotient_eq _ (twistedFixedGroupEquiv t K σ)
    (holds_twistFixed t K σ p hσ) S hS

theorem twistedModel_data
    {S : Type} [Group S] {t : TwistTag} {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (σ : K →+* K),
      Nat.card K = p ^ (f * t.order) ∧ Function.Surjective σ ∧
      (∀ c, σ c = c ^ p ^ f) ∧ (∀ c : K, c ^ Nat.card K = c) ∧
      (∃ u : Kˣ, (u : K) ^ 2 ≠ 1) ∧
      Nonempty (S ≃* DerivedCentralQuotient (twistedFixedGroup t K σ)) := by
  obtain ⟨K, _, _, hK, σ, hσc, he⟩ := h
  have := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ (f * t.order) := by rw [hK, pow_mul]
  have : CharP K p := charP_of_natCard_eq_pow hcard
  have hq : 2 ≤ p ^ f := (Nat.Prime.two_le hp.out).trans (Nat.le_self_pow (by omega) p)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hm : 2 ≤ t.order := by cases t <;> decide
    calc 4 = 2 ^ 2 := rfl
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ (p ^ f) ^ t.order := Nat.pow_le_pow_right (by omega) hm
  refine ⟨K, inferInstance, inferInstance, this, σ, hcard, surjective_ringHom_of_finite K σ,
    hσc, fun c => ?_, exists_units_sq_ne_one h4, he⟩
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem four_le_pRank_of_twistedE6Model
    {S : Type} [Group S] [Finite S] {p f : ℕ}
    [hp : Fact p.Prime] (hf : 1 ≤ f) (h : TwistedChevalleyModel S .E6 (p ^ f)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    rw [hσc, hσc, ← pow_mul, show p ^ f * p ^ f = Nat.card K by
      rw [hK]; change _ = p ^ (f * 2); ring, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt e,
    pRank_twistedDerivedQuotient σ hσ (e6_U_le_twistDerived hσ hσ2 hu)]
  exact four_le_pRank_commutator_twistFixed_E6 σ hσ hσ2 hu

theorem four_le_pRank_of_trialityD4Model
    {S : Type} [Group S] [Finite S] {p f : ℕ}
    [hp : Fact p.Prime] (hf : 1 ≤ f) (h : TwistedChevalleyModel S .D4 (p ^ f)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul, show p ^ f * (p ^ f * p ^ f) = Nat.card K by
      rw [hK]; change _ = p ^ (f * 3); ring, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt e,
    pRank_twistedDerivedQuotient σ hσ (d4_U_le_twistDerived hσ hσ3 hu)]
  have := le_pRank_commutator_twistFixed_D4 σ hK hσ hσ3 hu
  change f * 3 + 1 ≤ _ at this
  omega

theorem four_le_pRank_three_of_twistedE6Model_two
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S .E6 (2 ^ f)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    rw [hσc, hσc, ← pow_mul, show 2 ^ f * 2 ^ f = Nat.card K by
      rw [hK]; change _ = 2 ^ (f * 2); ring, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [pRank_top_eq_of_mulEquiv (by norm_num)
    (e.trans (derivedCentralQuotientEquiv _ (twistedFixedGroupEquiv .E6 K σ)))]
  exact four_le_pRank_three_commutator_center_E6 σ hσ hσ2 hu

theorem four_mul_le_pRank_of_untwistedModel
    {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} [hp : Fact p.Prime]
    (h : UntwistedChevalleyModel S τ (p ^ f)) :
    4 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt e]
  exact four_mul_le_pRank_adjointQuotient hτ hK

theorem three_mul_le_pRank_of_G2Model
    {S : Type} [Group S] [Finite S] {p f : ℕ}
    [hp : Fact p.Prime] (h : UntwistedChevalleyModel S .G2 (p ^ f)) :
    3 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt e]
  exact three_mul_le_pRank_adjointQuotient_G2 hK

theorem four_le_pRank_three_of_untwistedModel_two
    {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (h : UntwistedChevalleyModel S τ (2 ^ f)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_of_natCard_eq_pow hK
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact four_le_pRank_three_adjointQuotient hτ

theorem sqt_exceptional_restriction
    {S : Type} [Group S] [Finite S]
    (hSQT : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2)
    (h : ExceptionalRep S) :
    (∃ f, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
      (∃ f, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      (∃ f, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨ ReeTitsModel S .Tits 2 1 ∨
      (∃ f, Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f) := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hfalse : ∀ r, r.Prime → r ≠ 2 → 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) → False :=
    fun r hr hr2 hrk => by have := hSQT r hr hr2; omega
  rcases h with ⟨t, p, f, ht, hmod⟩ | ⟨t, p, f, ht, hmod⟩ | ⟨p, f, hmod⟩
  · have hmod' := hmod
    obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := hmod
    have : Fact p.Prime := ⟨hp⟩
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    by_cases hp2 : p = 2
    · subst hp2
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inl ⟨f, ?_, hmod'⟩
        obtain ⟨-, h32⟩ := hadm
        by_contra hlt
        obtain rfl : f = 1 := by omega
        norm_num at h32
      all_goals first
        | exact (hfalse 3 h3 (by norm_num) (le_trans (by norm_num)
            (four_le_pRank_three_of_untwistedModel_two (by simp) hm))).elim
        | exact (hfalse 3 h3 (by norm_num) (le_trans (by norm_num)
            (four_le_pRank_three_of_twistedE6Model_two hf hm))).elim
        | exact Or.inr (Or.inl ⟨f, hf, hmod'⟩)
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hfalse p hp hp2 (le_trans (by omega) (three_mul_le_pRank_of_G2Model hm))).elim
      all_goals first
        | exact (hfalse p hp hp2 (le_trans (by omega)
            (four_mul_le_pRank_of_untwistedModel (by simp) hm))).elim
        | exact (hfalse p hp hp2 (le_trans (by norm_num)
            (four_le_pRank_of_twistedE6Model hf hm))).elim
        | exact (hfalse p hp hp2 (le_trans (by norm_num)
            (four_le_pRank_of_trialityD4Model hf hm))).elim
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨-, hf3, hrk⟩ := smallReeModel_rank hmod
      exact (hfalse 3 h3 (by norm_num) (le_trans (by omega) hrk)).elim
    · obtain ⟨-, -, -, hp, hodd, hf3⟩ := hmod.1
      subst hp
      exact Or.inr (Or.inr (Or.inl ⟨f, hodd, hf3, hmod⟩))
    · obtain ⟨-, -, -, hp, hf1⟩ := hmod.1
      subst hp hf1
      exact Or.inr (Or.inr (Or.inr (Or.inl hmod)))
  · have hmod' := hmod
    obtain ⟨hp, a, ha, K, _, _, hf, -⟩ := hmod'
    subst hp
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f, ⟨a, hf⟩, by omega, hmod⟩)))

theorem higher_exceptional_even_central_quotient_exclusion
    {G : Type} [Group G] [Finite G]
    (hSQT : IsStronglyQuasithin G) (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    {t : StatedLieTag} {f : ℕ} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) :
    ¬ ChevalleyExceptionalModel (G ⧸ A) t 2 f := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := pRank_quotient_le_three (by norm_num)
    (isStronglyQuasithin_iff.1 hSQT 3 Nat.prime_three (by norm_num)) A hAZ
  obtain ⟨⟨-, hf, -⟩, hm⟩ := h
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ A)) := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact four_le_pRank_three_of_untwistedModel_two (by simp) hm
    · exact four_le_pRank_three_of_untwistedModel_two (by simp) hm
    · exact four_le_pRank_three_of_untwistedModel_two (by simp) hm
    · exact four_le_pRank_three_of_untwistedModel_two (by simp) hm
    · exact four_le_pRank_three_of_twistedE6Model_two hf hm
  omega

end CFSG.SectionRank
