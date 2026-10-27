module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalThree
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

theorem outLift_adjoint_G2_ne_three
    {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [Finite (adjointGroup Tag.G2 K)] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    OutLift p (adjointGroup Tag.G2 K) := by
  haveI := finite_ringAut K
  obtain ⟨hsurj, hstar⟩ := CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4
  exact outLift_of_hom_surj hp (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K) hstar hsurj

theorem outLift_adjoint_G2_three
    {p : ℕ} (hp : p.Prime) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.G2.prime] [Finite (adjointGroup Tag.G2 K)]
    (hK : Nat.card K = 3 ^ f) : OutLift p (adjointGroup Tag.G2 K) := by
  haveI : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨hord, -, ⟨Θ, hΘ, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  refine outLift_of_cyclic hp (n := 2 * f) Θ (CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K)
    (by rw [← hord]; exact pow_orderOf_eq_one _) ?_ hker
  have h := hΘ (CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K) 1 1 (by simp)
  rw [Nat.cast_one] at h
  exact h

theorem outLift_adjoint_F4_odd
    {ℓ : ℕ} (hℓ : ℓ.Prime) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] [Finite (adjointGroup Tag.F4 K)] (hK : Nat.card K = p ^ f) :
    OutLift ℓ (adjointGroup Tag.F4 K) := by
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .F4 (Or.inl rfl)
  refine outLift_of_section_ker hℓ Θ (entrywiseAdjointAutHom (τ := Tag.F4) (K := K))
    (fun σ => hΘ _ 1 σ fun h => ?_) hker
  simp [entrywiseAdjointAutHom, coe_entrywiseAdjointAut]

theorem outLift_adjoint_F4_two
    {ℓ : ℕ} (hℓ : ℓ.Prime) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] [Finite (adjointGroup Tag.F4 K)]
    (hK : Nat.card K = 2 ^ f) : OutLift ℓ (adjointGroup Tag.F4 K) := by
  haveI : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨hord, -, ⟨Θ, hΘ, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  refine outLift_of_cyclic hℓ (n := 2 * f) Θ (CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K)
    (by rw [← hord]; exact pow_orderOf_eq_one _) ?_ hker
  have h := hΘ (CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K) 1 1 (by simp)
  rw [Nat.cast_one] at h
  exact h

theorem outLift_trialityD4
    {ℓ : ℕ} (hℓ : ℓ.Prime) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    [Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)] :
    OutLift ℓ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact outLift_of_section_ker hℓ Θ (fieldActorHom (t := TwistTag.D4) σ)
      (fun δ => hΘ _ 1 δ (by rw [map_one, one_mul]; rfl)) hker
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    exact outLift_of_section_ker hℓ Θ (fieldActorHom (t := TwistTag.D4) σ)
      (fun δ => hΘ _ 1 δ (by rw [map_one, one_mul]; rfl)) hker

theorem outLift_twistedE6
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (p ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) [Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)] :
    OutLift ℓ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  refine outLift_of_section hℓ Θ (fieldActorHom (t := TwistTag.E6) σ)
    (fun δ => hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul]; rfl)) (hker ▸ le_sup_left) ?_
  rw [hker]
  exact GL83.I713.not_dvd_card_of_pow_eq_one hℓ Nat.prime_three hℓ3 hcube

theorem outLift_adjoint_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : τ = .E6 → ℓ ≠ 3) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] [Finite (adjointGroup τ K)] (hK : Nat.card K = p ^ f) :
    OutLift ℓ (adjointGroup τ K) := by
  haveI := finite_ringAut K
  obtain ⟨Θ, -, hΘ, hkerΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  have hΘφ : ∀ σ : RingAut K, Θ (entrywiseAdjointAutHom (τ := τ) (K := K) σ) =
      (σ, Multiplicative.ofAdd ((0 : ℕ) : ZMod (exactE τ))) := fun σ =>
    hΘ _ 1 1 σ ⟨0, exactE_pos τ⟩ fun h => by
      rw [show entrywiseAdjointAutHom (τ := τ) (K := K) σ = entrywiseAdjointAut τ σ from rfl,
        coe_entrywiseAdjointAut, rootDiagUnit_one]
      change _ = _ * _ * exactQ τ K 0 * _ * (exactQ τ K 0)⁻¹ * _ * _
      rw [exactQ_zero]
      simp
  refine outLift_of_hom hℓ (entrywiseAdjointAutHom (τ := τ) (K := K)) ?_ ?_
  · intro σ hσ
    obtain ⟨g, hg⟩ := hσ
    have h1 : Θ (MulAut.conj g) = 1 := by
      rw [← MonoidHom.mem_ker, hkerΘ]
      exact ⟨g, 1, fun h => by simp [rootDiagUnit_one]⟩
    rw [hg, hΘφ] at h1
    exact (Prod.mk.inj h1).1
  · have hcardR : Nat.card (RingAut K) = f := (card_ringAut_and_isCyclic hp K hK).1
    have key : ∀ d e : ℕ, 0 < d → 0 < e → ¬ ℓ ∣ d * e →
        Nat.card (Outer (adjointGroup τ K)) ∣ d * e * f →
        (Nat.card (Outer (adjointGroup τ K))).factorization ℓ ≤ f.factorization ℓ := by
      intro d e hd he hde h
      have hfpos : f ≠ 0 := by omega
      have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (Nat.mul_ne_zero (Nat.mul_pos hd he).ne' hfpos)).2 h ℓ
      rwa [Nat.factorization_mul (Nat.mul_pos hd he).ne' hfpos, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hde, zero_add] at h1
    rw [hcardR]
    rcases hτ with rfl | rfl | rfl
    · obtain ⟨hdvd, -⟩ := ordinary_E_outer_order_Cartan_divisor Tag.E6 (Or.inl rfl) hp hf K hK 3 2
        (Or.inl ⟨rfl, rfl, rfl⟩)
      refine key 3 2 (by norm_num) (by norm_num) ?_ hdvd
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
      · exact hℓ3 rfl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h)
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · obtain ⟨hdvd, -⟩ := ordinary_E_outer_order_Cartan_divisor Tag.E7 (Or.inr (Or.inl rfl)) hp hf
        K hK 2 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      refine key 2 1 (by norm_num) (by norm_num) ?_ hdvd
      intro h
      rw [mul_one] at h
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · obtain ⟨hdvd, -⟩ := ordinary_E_outer_order_Cartan_divisor Tag.E8 (Or.inr (Or.inr rfl)) hp hf
        K hK 1 1 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      refine key 1 1 (by norm_num) (by norm_num) ?_ hdvd
      intro h
      exact hℓ.not_dvd_one (by simpa using h)

theorem liftClause_chevalleyExceptional
    {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) :
    FamilyLift fun S _ => ChevalleyExceptionalModel S t p f := by
  intro S _ _ _ _ h ℓ hℓ hℓ2 hSℓ
  obtain ⟨⟨hpp, hf, hadm⟩, hm⟩ := h
  cases t
  case G2 =>
    have h3 : 3 ≤ p ^ f := hadm.2
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    haveI : Finite (adjointGroup Tag.G2 K) := Finite.of_equiv S e.toEquiv
    refine OutLift.of_mulEquiv e ?_
    by_cases hp3 : p = 3
    · subst hp3
      haveI : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
      haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := inferInstanceAs (CharP K 3)
      exact outLift_adjoint_G2_three hℓ hf hK
    · haveI : CharP K p := finite_field_prime_power_characteristic hpp hf hK
      refine outLift_adjoint_G2_ne_three hℓ (by rw [ringChar.eq K p]; exact hp3) ?_
      rw [hK]
      by_contra hlt
      have h3' : p ^ f = 3 := by omega
      have : p ∣ 3 := h3' ▸ dvd_pow_self p (by omega)
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 this)
  case F4 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    haveI : Finite (adjointGroup Tag.F4 K) := Finite.of_equiv S e.toEquiv
    refine OutLift.of_mulEquiv e ?_
    by_cases hp2 : p = 2
    · subst hp2
      haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
      haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
      exact outLift_adjoint_F4_two hℓ hf hK
    · exact outLift_adjoint_F4_odd hℓ hpp hp2 hf hK
  case E6 =>
    have hm' : UntwistedChevalleyModel S .E6 (p ^ f) := hm
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl
      have := GL83.I713.four_le_pRank_three_of_untwistedModel_E6 hm'
      omega
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm'
    haveI : Finite (adjointGroup Tag.E6 K) := Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e
      (outLift_adjoint_E (Or.inl rfl) hℓ hℓ2 (fun _ => hℓ3) hpp hf hK)
  case E7 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    haveI : Finite (adjointGroup Tag.E7 K) := Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e (outLift_adjoint_E (Or.inr (Or.inl rfl)) hℓ hℓ2
      (fun h => absurd h (by decide)) hpp hf hK)
  case E8 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    haveI : Finite (adjointGroup Tag.E8 K) := Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e (outLift_adjoint_E (Or.inr (Or.inr rfl)) hℓ hℓ2
      (fun h => absurd h (by decide)) hpp hf hK)
  case twistedE6 =>
    have hm' : TwistedChevalleyModel S .E6 (p ^ f) := hm
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl
      have := GL83.I713.two_le_pRank_three_of_twistedE6Model hpp hf hm'
      omega
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hpp hf hm'
    have hK' : Nat.card K = (p ^ f) ^ 2 := hK
    haveI : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e (outLift_twistedE6 hℓ hℓ3 hpp hf σ hK' hσ)
  case trialityD4 =>
    have hm' : TwistedChevalleyModel S .D4 (p ^ f) := hm
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hpp hf hm'
    have hK' : Nat.card K = (p ^ f) ^ 3 := hK
    haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e (outLift_trialityD4 hℓ hpp hf σ hK' hσ)
  all_goals exact absurd ht (by simp [chevalleyExceptionalTags])

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
