module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveRegular

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem two_mul_trace_restrict_eigenspace_neg_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {f g : Module.End ℂ W} (hf : f ^ 2 = 1) (hfg : Commute f g)
    (h : ∀ v ∈ f.eigenspace (-1), g v ∈ f.eigenspace (-1)) :
    2 * LinearMap.trace ℂ (f.eigenspace (-1)) (g.restrict h) =
      LinearMap.trace ℂ W g - LinearMap.trace ℂ W (g * f) := by
  have hN := EigenCalculus.isInternal_eigenspaces_involution hf
  have h0 := EigenCalculus.trace_mul_pow_eq_sum_of_isInternal hfg ![1, -1] hN 0
  have h1 := EigenCalculus.trace_mul_pow_eq_sum_of_isInternal hfg ![1, -1] hN 1
  rw [Fin.sum_univ_two] at h0 h1
  simp only [pow_zero, pow_one, mul_one, one_mul] at h0 h1
  change LinearMap.trace ℂ W g =
    LinearMap.trace ℂ (f.eigenspace 1) (g.restrict (EigenCalculus.mapsTo_eigenspace hfg 1)) +
      LinearMap.trace ℂ (f.eigenspace (-1)) (g.restrict h) at h0
  change LinearMap.trace ℂ W (g * f) =
    1 * LinearMap.trace ℂ (f.eigenspace 1) (g.restrict (EigenCalculus.mapsTo_eigenspace hfg 1)) +
      (-1) * LinearMap.trace ℂ (f.eigenspace (-1)) (g.restrict h) at h1
  linear_combination h1 - h0

theorem injective_of_oddCore_of_conj_mul {C : Type*} [Group C] [Finite C] {X : Type*}
    [Monoid X] (σ : C →* X) {t : C} (ht : σ t ≠ 1)
    (hconj : ∀ v : C, orderOf v = 2 → v ≠ t → ∃ d : C, d * v * d⁻¹ = t * v)
    (hN : ∀ u ∈ CFSG.pPrimeCore 2 C, σ u = 1 → u = 1) : Function.Injective σ := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hK : σ.ker.Normal := MonoidHom.normal_ker σ
  have hodd : ¬ 2 ∣ Nat.card σ.ker := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := σ.ker) 2 h2
    have hv2 : orderOf (v : C) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
    have hσv : σ v = 1 := MonoidHom.mem_ker.mp v.2
    have hvt : (v : C) ≠ t := by
      intro h
      apply ht
      rw [← h]
      exact hσv
    obtain ⟨d, hd⟩ := hconj v hv2 hvt
    apply ht
    have htv : σ (t * v) = 1 := by
      rw [← hd, map_mul, map_mul, hσv, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, hσv, mul_one] at htv
    exact htv
  have hle : σ.ker ≤ CFSG.pPrimeCore 2 C :=
    le_sSup ⟨hK, Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))⟩
  exact hN c (hle hc) hc

theorem exists_conj_eq_tInC_mul {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (v : C t) (hv : orderOf v = 2) (hvt : v ≠ tInC t) :
    ∃ d : C t, d * v * d⁻¹ = tInC t * v := by
  obtain ⟨⟨-, F, hF, hFfin, A, a, hcard, hAodd, -, -, -, -, -, haF, -, -, -, hdata⟩, hnorm⟩ :=
    ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action n hn S fS hG t ht
      hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, hz, hu, -, -, -, -, -⟩ := hdata v hv hvt
  obtain ⟨⟨x, y, hxy⟩, hND⟩ := hnorm F A _ _ v hv hvt Psi hz hu hcard hAodd haF
  obtain ⟨d, -, -, hds, -⟩ := (hND x y hxy).actual_lift_and_action
  exact ⟨d, hds⟩

theorem card_dvd_of_faithful_rational_degree_eight {C : Type} [Group C] [Finite C]
    (τ : FiniteComplexRepresentation.{0, 0} C) (hfaith : Function.Injective τ.representation)
    (hrat : ∀ c, ∃ q : ℚ, τ.character c = q) (hdeg : Module.finrank ℂ τ.vector = 8)
    (N : Subgroup C) (hNodd : Odd (Nat.card N)) (hC : Nat.card C = 240 * Nat.card N) :
    Nat.card N ∣ 3 ^ 4 * 5 * 7 := by
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hfac : ∀ p : ℕ, (Nat.card C).factorization p =
      (240 : ℕ).factorization p + (Nat.card N).factorization p := by
    intro p
    rw [hC, Nat.factorization_mul (by norm_num) hN0, Finsupp.add_apply]
  have hsyl : ∀ (p : ℕ) [Fact p.Prime], p ^ (Nat.card C).factorization p ∣
      p ^ (8 / (p - 1)) * (8 / (p - 1)).factorial := by
    intro p _
    obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
    have h := CFSG.LyonsUnitaryFour.sylow_card_dvd_of_faithful_rational_character τ hfaith
      hrat P
    rw [hdeg, Sylow.card_eq_multiplicity] at h
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h3 : (Nat.card C).factorization 3 ≤ 5 := by
    have h := hsyl 3
    rw [show 8 / (3 - 1) = 4 from rfl, show Nat.factorial 4 = 24 from rfl] at h
    by_contra hc
    push Not at hc
    have : 3 ^ 6 ∣ 3 ^ 4 * 24 := (pow_dvd_pow 3 hc).trans h
    norm_num at this
  have h5 : (Nat.card C).factorization 5 ≤ 2 := by
    have h := hsyl 5
    rw [show 8 / (5 - 1) = 2 from rfl, show Nat.factorial 2 = 2 from rfl] at h
    by_contra hc
    push Not at hc
    have : 5 ^ 3 ∣ 5 ^ 2 * 2 := (pow_dvd_pow 5 hc).trans h
    norm_num at this
  have h7 : (Nat.card C).factorization 7 ≤ 1 := by
    have h := hsyl 7
    rw [show 8 / (7 - 1) = 1 from rfl, show Nat.factorial 1 = 1 from rfl] at h
    by_contra hc
    push Not at hc
    have : 7 ^ 2 ∣ 7 ^ 1 * 1 := (pow_dvd_pow 7 hc).trans h
    norm_num at this
  have h240 : (240 : ℕ).factorization =
      Finsupp.single 2 4 + Finsupp.single 3 1 + Finsupp.single 5 1 := by
    rw [show (240 : ℕ) = 2 ^ 4 * 3 * 5 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three,
      Nat.Prime.factorization (by norm_num : Nat.Prime 5)]
  have h2835 : (3 ^ 4 * 5 * 7 : ℕ).factorization =
      Finsupp.single 3 4 + Finsupp.single 5 1 + Finsupp.single 7 1 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_three,
      Nat.Prime.factorization (by norm_num : Nat.Prime 5),
      Nat.Prime.factorization (by norm_num : Nat.Prime 7)]
  have hN3 : (Nat.card N).factorization 3 ≤ 4 := by
    have h := hfac 3
    rw [h240] at h
    simp at h
    omega
  have hN5 : (Nat.card N).factorization 5 ≤ 1 := by
    have h := hfac 5
    rw [h240] at h
    simp at h
    omega
  have hN7 : (Nat.card N).factorization 7 ≤ 1 := by
    have h := hfac 7
    rw [h240] at h
    simp at h
    omega
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card N → p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp hdvd
    have hpC : p ∣ Nat.card C := hC ▸ dvd_mul_of_dvd_right hdvd 240
    have hp9 := CFSG.LyonsUnitaryFour.prime_le_of_faithful_rational_character τ hfaith hrat hp
      hpC
    rw [hdeg] at hp9
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
    interval_cases p <;> first | omega | (exfalso; revert hp; decide)
  rw [← Nat.factorization_le_iff_dvd hN0 (by norm_num)]
  refine Finsupp.le_def.mpr fun p => ?_
  by_cases hp : p.Prime
  · by_cases hdvd : p ∣ Nat.card N
    · rw [h2835]
      rcases hprime p hp hdvd with rfl | rfl | rfl
      · simpa [Finsupp.single_apply] using hN3
      · simpa [Finsupp.single_apply] using hN5
      · simpa [Finsupp.single_apply] using hN7
    · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem negative_eigenspace_degree_eight {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {t : G} (ht2 : orderOf t = 2)
    (hconj : ∀ v : C t, orderOf v = 2 → v ≠ tInC t → ∃ d : C t, d * v * d⁻¹ = tInC t * v)
    (hC : Nat.card (C t) = 240 * Nat.card (N t))
    (θ : G → ℂ) (hrat : ∀ g, ∃ q : ℚ, θ g = q) (h1 : θ 1 = 21) (htθ : θ t = 5)
    (hNθ : ∀ u : C t, u ∈ N t → θ (t * u) = 5) :
    let η : C t → ℂ := fun c => (θ c - θ (t * c)) / 2
    ∀ V : FiniteComplexRepresentation.{0, 0} G, V.character = θ →
      let ρC : Representation ℂ (C t) V.vector := V.representation.comp (C t).subtype
      let E : Submodule ℂ V.vector := Module.End.eigenspace (ρC (tInC t)) (-1)
      ∃ hE : ∀ c : C t, E ≤ E.comap (ρC c),
        (ρC.subrepresentation E hE).character = η ∧ η 1 = 8 ∧ Module.finrank ℂ E = 8 ∧
        Function.Injective (ρC.subrepresentation E hE) ∧
        (∀ c : C t, ∃ q : ℚ, η c = q) ∧
        (∀ u : C t, u ∈ N t → ρC.subrepresentation E hE u = 1 → u = 1) ∧
        (∀ u : C t, u ∈ N t → ∃ q : ℚ, η u = q) ∧
        (∀ c u : C t, u ∈ N t → η (c * u * c⁻¹) = η u) ∧
        Nat.card (N t) ∣ 3 ^ 4 * 5 * 7 := by
  intro η V hV ρC E
  have hdimV : (Module.finrank ℂ V.vector : ℂ) = 21 := by
    rw [← h1, ← hV]
    change _ = LinearMap.trace ℂ V.vector (V.representation 1)
    rw [map_one, LinearMap.trace_one]
  have hVfaith : Function.Injective V.representation := by
    rcases (MonoidHom.normal_ker V.representation).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have htker : t ∈ MonoidHom.ker V.representation := h ▸ trivial
      have h' : V.character t = V.character 1 := by
        change LinearMap.trace ℂ _ (V.representation t) =
          LinearMap.trace ℂ _ (V.representation 1)
        rw [MonoidHom.mem_ker.mp htker, V.representation.map_one]
      rw [hV, htθ, h1] at h'
      norm_num at h'
  have htC2 : orderOf (tInC t) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
  have hT2 : ρC (tInC t) ^ 2 = 1 := by
    rw [← map_pow, ← htC2, pow_orderOf_eq_one, map_one]
  have hcomm : ∀ c : C t, Commute (ρC (tInC t)) (ρC c) := fun c => by
    change ρC (tInC t) * ρC c = ρC c * ρC (tInC t)
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (tInC_central t) c]
  have hE : ∀ c : C t, E ≤ E.comap (ρC c) := fun c v hv =>
    EigenCalculus.mapsTo_eigenspace (hcomm c) (-1) v hv
  refine ⟨hE, ?_⟩
  have hchar : ∀ c : C t, (ρC.subrepresentation E hE).character c = η c := by
    intro c
    have h := two_mul_trace_restrict_eigenspace_neg_one hT2 (hcomm c) (fun v hv => hE c hv)
    have hc1 : LinearMap.trace ℂ V.vector (ρC c) = θ c := by
      rw [← hV]
      rfl
    have hc2 : LinearMap.trace ℂ V.vector (ρC c * ρC (tInC t)) = θ (t * c) := by
      rw [← map_mul, ← hV]
      change V.character ((c : G) * t) = _
      rw [(Subgroup.mem_centralizer_singleton_iff.mp c.2)]
    change LinearMap.trace ℂ E ((ρC c).restrict (fun x hx => hE c hx)) = (θ c - θ (t * c)) / 2
    rw [hc1, hc2] at h
    linear_combination h / 2
  have hchar' : (ρC.subrepresentation E hE).character = η := funext hchar
  have hη1 : η 1 = 8 := by
    change (θ ((1 : C t) : G) - θ (t * ((1 : C t) : G))) / 2 = 8
    rw [OneMemClass.coe_one, mul_one, h1, htθ]
    norm_num
  have hdimE : Module.finrank ℂ E = 8 := by
    have h := hchar 1
    rw [hη1] at h
    have h' : (ρC.subrepresentation E hE).character 1 = (Module.finrank ℂ E : ℂ) := by
      change LinearMap.trace ℂ E ((ρC.subrepresentation E hE) 1) = _
      rw [map_one, LinearMap.trace_one]
    rw [h'] at h
    exact_mod_cast h
  have hratη : ∀ c : C t, ∃ q : ℚ, η c = q := by
    intro c
    obtain ⟨q₁, hq₁⟩ := hrat c
    obtain ⟨q₂, hq₂⟩ := hrat (t * c)
    refine ⟨(q₁ - q₂) / 2, ?_⟩
    change (θ c - θ (t * c)) / 2 = _
    rw [hq₁, hq₂]
    push_cast
    ring
  have hfaithN : ∀ u : C t, u ∈ N t → ρC.subrepresentation E hE u = 1 → u = 1 := by
    intro u hu h1u
    have htr : η u = 8 := by
      rw [← hchar]
      change LinearMap.trace ℂ E ((ρC.subrepresentation E hE) u) = 8
      rw [h1u, LinearMap.trace_one, hdimE]
      norm_num
    have hθu : θ u = 21 := by
      have h' : (θ u - θ (t * u)) / 2 = 8 := htr
      rw [hNθ u hu] at h'
      linear_combination 2 * h'
    have hVu : V.representation u = 1 := by
      apply CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (V.representation u)
        (orderOf_pos (u : G)).ne'
      · rw [← map_pow, pow_orderOf_eq_one, map_one]
      · change V.character u = _
        rw [hV, hθu, hdimV]
    apply Subtype.ext
    exact hVfaith (by rw [hVu, OneMemClass.coe_one, map_one])
  have htE : ρC.subrepresentation E hE (tInC t) ≠ 1 := by
    intro h
    have htr : η (tInC t) = 8 := by
      rw [← hchar]
      change LinearMap.trace ℂ E ((ρC.subrepresentation E hE) (tInC t)) = 8
      rw [h, LinearMap.trace_one, hdimE]
      norm_num
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    change (θ t - θ (t * t)) / 2 = 8 at htr
    rw [htt, htθ, h1] at htr
    norm_num at htr
  have hfaithC : Function.Injective (ρC.subrepresentation E hE) :=
    injective_of_oddCore_of_conj_mul _ htE hconj hfaithN
  have hinv : ∀ c u : C t, u ∈ N t → η (c * u * c⁻¹) = η u := by
    intro c u _
    rw [← hchar, ← hchar]
    exact Representation.char_conj _ u c
  let τC : FiniteComplexRepresentation.{0, 0} (C t) :=
    { vector := E
      representation := ρC.subrepresentation E hE }
  have hdvd := card_dvd_of_faithful_rational_degree_eight τC hfaithC
    (fun c => by
      obtain ⟨q, hq⟩ := hratη c
      exact ⟨q, by rw [← hq]; exact hchar c⟩)
    hdimE (N t) (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) hC
  exact ⟨hchar', hη1, hdimE, hfaithC, hratη, hfaithN, fun u _ => hratη u, hinv, hdvd⟩

theorem local_parameter_five_degree_eight_of_family
    {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (q : ℕ) (hq : q = 5) (e : ℤ) (he : e = if q % 4 = 1 then 1 else -1) (φ : C t → ℂ)
    (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₂ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index)
    (hfam : ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal q e
      (2 ^ (n - 3)) φ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν)
    (hdeg : ActualPrincipalDegreeRelations basis q δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄)
    (hOF : ActualPrincipalOrderFormulas G t (fS (s n) : G) q e δ₁ δ₂
      (Module.finrank ℂ (basis.representation χ₁).vector)
      (Module.finrank ℂ (basis.representation χ₂).vector)) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    ∃ χ ψ : basis.index, χ ≠ ψ ∧ χ ∈ B ∧ ψ ∈ B ∧
      (basis.representation χ).IsIrreducible ∧ (basis.representation ψ).IsIrreducible ∧
      Function.Injective (basis.representation χ).representation ∧
      Function.Injective (basis.representation ψ).representation ∧
      (∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
      (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) ∧
      (basis.representation χ).character 1 = 21 ∧ (basis.representation ψ).character 1 = 20 ∧
      (basis.representation χ).character t = 5 ∧ (basis.representation ψ).character t = -4 ∧
      (∀ u : C t, u ∈ N t → (basis.representation χ).character (t * u) = 5 ∧
        (basis.representation ψ).character (t * u) = -4) ∧
      (∀ x : G, Odd (orderOf x) →
        (basis.representation ψ).character x = (basis.representation χ).character x - 1) ∧
      (let η : C t → ℂ := fun c =>
          ((basis.representation χ).character c - (basis.representation χ).character (t * c)) / 2
        ∀ V : FiniteComplexRepresentation.{0, 0} G,
          V.character = (basis.representation χ).character →
          let ρC : Representation ℂ (C t) V.vector := V.representation.comp (C t).subtype
          let E : Submodule ℂ V.vector := Module.End.eigenspace (ρC (tInC t)) (-1)
          ∃ hE : ∀ c : C t, E ≤ E.comap (ρC c),
            (ρC.subrepresentation E hE).character = η ∧ η 1 = 8 ∧ Module.finrank ℂ E = 8 ∧
            Function.Injective (ρC.subrepresentation E hE) ∧
            (∀ c : C t, ∃ q : ℚ, η c = q) ∧
            (∀ u : C t, u ∈ N t → ρC.subrepresentation E hE u = 1 → u = 1) ∧
            (∀ u : C t, u ∈ N t → ∃ q : ℚ, η u = q) ∧
            (∀ c u : C t, u ∈ N t → η (c * u * c⁻¹) = η u)) ∧
      Nat.card (N t) ∣ 3 ^ 4 * 5 * 7 ∧
      B.val.map (fun c => Module.finrank ℂ (basis.representation c).vector) =
        {1, 125, 21, 105, 20, 126, 126, 126} := by
  intro B
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨hn4, hCt, -, hrows⟩ := local_parameter_five_rows_of_family n hn S fS t ht hnonab
    hcentral hnc hmodel basis ideal principal hprincipal localBasis localPrincipal q hq e he φ δ₁
    δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg hOF
  obtain ⟨-, -, -, hGc, -⟩ := simple_local_parameter_five_is_regular_with_exact_order hGnonab n
    hn S fS t ht hnonab hcentral hnc hmodel
  have hne : ∀ K a b : ℕ, Nat.card G = K * a * b ^ 3 → Nat.card G = 126000 * a * b ^ 3 →
      0 < a → 0 < b → K ≠ 126000 → False := by
    intro K a b h1 h2 ha hb hK
    apply hK
    have h' : K * (a * b ^ 3) = 126000 * (a * b ^ 3) := by
      rw [← mul_assoc, ← h1, h2, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h'
  rcases hrows with ⟨-, -, -, -, -, -, hX⟩ | ⟨hδ₁, hδ₂, hδ₃, hf₁, hf₂, hf₃, -⟩ |
    ⟨-, -, -, -, -, -, hX⟩
  · exact (hne 68400 _ _ (congrArg Prod.fst hX) hGc Nat.card_pos
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (by norm_num)).elim
  rotate_left
  · exact (hne 85680 _ _ (congrArg Prod.fst hX) hGc Nat.card_pos
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (by norm_num)).elim
  have hCN : Nat.card (C t) = 240 * Nat.card (N t) := by
    rw [hCt, mul_assoc, Subgroup.card_mul_index]
  subst hq
  have he1 : e = 1 := by rw [he]; rfl
  subst he1 hδ₁ hδ₂ hδ₃ hn4
  obtain ⟨hlφ, -, -, -, -, hnd, -, hνinj, hψx, hνx, hνψ, hB, -, -, hsec, hrel⟩ := hfam
  obtain ⟨-, -, -, -, -, hδ₄, hf₄, -, -⟩ := hdeg
  have hδ₄' : δ₄ = 1 := by rw [hδ₄]; norm_num
  subst hδ₄'
  obtain ⟨lφ, -, -, hφchar, hφdeg, hφker⟩ := hlφ
  have hφN : ∀ y : C t, y ∈ N t → φ y = 5 := by
    intro y hy
    have hyker : y ∈ MonoidHom.ker (localBasis.representation lφ).representation := by
      rw [hφker]
      exact Subgroup.mem_sup_left hy
    have hρ : (localBasis.representation lφ).representation y =
        (localBasis.representation lφ).representation 1 := by
      rw [MonoidHom.mem_ker.mp hyker, map_one]
    rw [← hφchar]
    change LinearMap.trace ℂ _ ((localBasis.representation lφ).representation y) = 5
    rw [hρ]
    change (localBasis.representation lφ).character 1 = 5
    rw [(basis_character_one localBasis lφ).1, hφdeg]
    norm_num
  have hNodd : ∀ y : C t, y ∈ N t → Odd (orderOf y) := by
    intro y hy
    have hcop : Nat.Coprime 2 (Nat.card (N t)) := CFSG.pPrimeCore_coprime_card
    have hdvd : orderOf (⟨y, hy⟩ : N t) ∣ Nat.card (N t) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by
        rw [Nat.coprime_two_left]; exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))))
  have hχ₂N : ∀ u : C t, u ∈ N t → (basis.representation χ₂).character (t * u) = 5 := by
    intro u hu
    rw [(hsec u (hNodd u hu)).2.1, hφN u hu]
    norm_num
  have hχ₄N : ∀ u : C t, u ∈ N t → (basis.representation χ₄).character (t * u) = -4 := by
    intro u hu
    rw [(hsec u (hNodd u hu)).2.2.2.1, hφN u hu]
    norm_num
  have hχ₂t : (basis.representation χ₂).character t = 5 := by
    have h := hχ₂N 1 (one_mem _)
    rwa [OneMemClass.coe_one, mul_one] at h
  have hχ₄t : (basis.representation χ₄).character t = -4 := by
    have h := hχ₄N 1 (one_mem _)
    rwa [OneMemClass.coe_one, mul_one] at h
  have hoddrel : ∀ x : G, Odd (orderOf x) →
      (basis.representation χ₄).character x = (basis.representation χ₂).character x - 1 := by
    intro x hx
    have h := (hrel x hx).2.2.2
    push_cast at h
    linear_combination h
  have hdeg1 : ∀ c : basis.index, (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) :=
    fun c => (basis_character_one basis c).1
  have hf₄' : Module.finrank ℂ (basis.representation χ₄).vector = 20 := by
    have h : (Module.finrank ℂ (basis.representation χ₄).vector : ℤ) = 20 := by
      rw [hf₄, hf₂]
      norm_num
    exact_mod_cast h
  have hf₀ : Module.finrank ℂ (basis.representation principal).vector = 1 := by
    have h := hdeg1 principal
    rw [hprincipal] at h
    have h' : (Module.finrank ℂ (basis.representation principal).vector : ℂ) = 1 := by
      rw [← h]
      rfl
    exact_mod_cast h'
  have hχ₁1 : (basis.representation χ₁).character 1 = 125 := by rw [hdeg1, hf₁]; norm_num
  have hχ₂1 : (basis.representation χ₂).character 1 = 21 := by rw [hdeg1, hf₂]; norm_num
  have hχ₃1 : (basis.representation χ₃).character 1 = 105 := by rw [hdeg1, hf₃]; norm_num
  have hχ₄1 : (basis.representation χ₄).character 1 = 20 := by rw [hdeg1, hf₄']; norm_num
  obtain ⟨hψ1, hν1, -, -⟩ := hrel 1 (by rw [orderOf_one]; exact odd_one)
  have hψdeg : ∀ j ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1),
      (basis.representation (ψ j)).character 1 = 126 := by
    intro j hj
    rw [hψ1 j hj, hχ₁1]
    norm_num
  have hνdeg : ∀ i ∈ Finset.range (2 ^ (4 - 3)),
      (basis.representation (ν i)).character 1 = 126 := by
    intro i hi
    rw [hν1 i hi, hχ₁1]
    norm_num
  have hmem : ∀ c ∈ ({principal, χ₁, χ₂, χ₃, χ₄} : Finset basis.index), c ∈ B := by
    intro c hc
    change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    rw [hB]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
  have hχ₂B : χ₂ ∈ B := hmem χ₂ (by simp)
  have hχ₄B : χ₄ ∈ B := hmem χ₄ (by simp)
  have hiso : ∀ (a : basis.index) (d : ℂ), (basis.representation a).character 1 = d →
      d ≠ 1 → d ≠ 125 → d ≠ 105 → d ≠ 126 →
      (d = 21 → a = χ₂) → (d = 20 → a = χ₄) → (d = 21 ∨ d = 20) →
      ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (∀ x ∈ ({1} : Set G), (basis.representation b).character x =
          (basis.representation a).character x) → b = a := by
    intro a d ha d1 d125 d105 d126 h21 h20 hd b hb hbval
    have hb1 := hbval 1 (Set.mem_singleton 1)
    rw [ha] at hb1
    rw [hB] at hb
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at hb
    rcases hb with ((h | h | h | h | h) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [h, hprincipal] at hb1
      exact absurd hb1.symm d1
    · rw [h, hχ₁1] at hb1
      exact absurd hb1.symm d125
    · rw [h, hχ₂1] at hb1
      rw [h]
      exact (h21 hb1.symm).symm
    · rw [h, hχ₃1] at hb1
      exact absurd hb1.symm d105
    · rw [h, hχ₄1] at hb1
      rw [h]
      exact (h20 hb1.symm).symm
    · rw [hψdeg j hj] at hb1
      exact absurd hb1.symm d126
    · rw [hνdeg i hi] at hb1
      exact absurd hb1.symm d126
  have hrat₂ : ∀ g, ∃ q : ℚ, (basis.representation χ₂).character g = q :=
    CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal hχ₂B
      {1} (fun x hx => ⟨21, by rw [Set.mem_singleton_iff.mp hx, hχ₂1]; norm_num⟩)
      (hiso χ₂ 21 hχ₂1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => rfl)
        (fun h => absurd h (by norm_num)) (Or.inl rfl))
  have hrat₄ : ∀ g, ∃ q : ℚ, (basis.representation χ₄).character g = q :=
    CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal hprincipal hχ₄B
      {1} (fun x hx => ⟨20, by rw [Set.mem_singleton_iff.mp hx, hχ₄1]; norm_num⟩)
      (hiso χ₄ 20 hχ₄1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun _ => rfl) (Or.inr rfl))
  have hfaith : ∀ c : basis.index, (basis.representation c).character t ≠
      (basis.representation c).character 1 →
      Function.Injective (basis.representation c).representation := by
    intro c hc
    rcases (MonoidHom.normal_ker (basis.representation c).representation).eq_bot_or_eq_top
      with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have htker : t ∈ MonoidHom.ker (basis.representation c).representation := h ▸ trivial
      apply hc
      change LinearMap.trace ℂ _ ((basis.representation c).representation t) =
        LinearMap.trace ℂ _ ((basis.representation c).representation 1)
      rw [MonoidHom.mem_ker.mp htker, (basis.representation c).representation.map_one]
  have hfaith₂ := hfaith χ₂ (by rw [hχ₂t, hχ₂1]; norm_num)
  have hfaith₄ := hfaith χ₄ (by rw [hχ₄t, hχ₄1]; norm_num)
  have hconj : ∀ v : C t, orderOf v = 2 → v ≠ tInC t → ∃ d : C t, d * v * d⁻¹ = tInC t * v :=
    fun v hv hvt => exists_conj_eq_tInC_mul 4 hn S fS hG t ht2 hnonab hcentral hnc 5 1
      (by norm_num) (by decide) le_rfl hmodel v hv hvt
  have hη := negative_eigenspace_degree_eight (G := G) ht2 hconj hCN _ hrat₂ hχ₂1 hχ₂t hχ₂N
  have hNdvd : Nat.card (N t) ∣ 3 ^ 4 * 5 * 7 := by
    have h' := hη (basis.representation χ₂) rfl
    obtain ⟨_, _, _, _, _, _, _, _, _, hdvd⟩ := h'
    exact hdvd
  have hIcc : Finset.Icc 1 (2 ^ (4 - 3) - 1) = ({1} : Finset ℕ) := by decide
  have hrange : Finset.range (2 ^ (4 - 3)) = ({0, 1} : Finset ℕ) := by decide
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (2 ^ (4 - 3) - 1) := by rw [hIcc]; simp
  have h0r : (0 : ℕ) ∈ Finset.range (2 ^ (4 - 3)) := by rw [hrange]; simp
  have h1r : (1 : ℕ) ∈ Finset.range (2 ^ (4 - 3)) := by rw [hrange]; simp
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true] at hnd'
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hnd'
  obtain ⟨hψ0, hψ1', hψ2, hψ3, hψ4⟩ := hψx 1 h1mem
  obtain ⟨hν00, hν01, hν02, hν03, hν04⟩ := hνx 0 h0r
  obtain ⟨hν10, hν11, hν12, hν13, hν14⟩ := hνx 1 h1r
  have hν0ψ := hνψ 0 h0r 1 h1mem
  have hν1ψ := hνψ 1 h1r 1 h1mem
  have hν01' : ν 0 ≠ ν 1 := fun h => by
    have := hνinj (Finset.mem_coe.mpr h0r) (Finset.mem_coe.mpr h1r) h
    omega
  have hBval : B.val = {principal, χ₁, χ₂, χ₃, χ₄, ψ 1, ν 0, ν 1} := by
    apply (Multiset.Nodup.ext B.nodup ?_).mpr
    · intro c
      rw [Finset.mem_val]
      change c ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔ _
      rw [hB, hIcc, hrange, Finset.image_singleton, Finset.image_insert, Finset.image_singleton]
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_assoc]
    · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
        Multiset.mem_singleton, not_or, Multiset.nodup_singleton, and_true]
      exact ⟨⟨h01, h02, h03, h04, hψ0.symm, hν00.symm, hν10.symm⟩,
        ⟨h12, h13, h14, hψ1'.symm, hν01.symm, hν11.symm⟩, ⟨h23, h24, hψ2.symm, hν02.symm,
          hν12.symm⟩, ⟨h34, hψ3.symm, hν03.symm, hν13.symm⟩, ⟨hψ4.symm, hν04.symm, hν14.symm⟩,
        ⟨hν0ψ.symm, hν1ψ.symm⟩, hν01'⟩
  have hdegN : ∀ c : basis.index, (basis.representation c).character 1 = 126 →
      Module.finrank ℂ (basis.representation c).vector = 126 := by
    intro c hc
    rw [hdeg1] at hc
    exact_mod_cast hc
  have hmap : B.val.map (fun c => Module.finrank ℂ (basis.representation c).vector) =
      {1, 125, 21, 105, 20, 126, 126, 126} := by
    rw [hBval]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [hf₀, hf₁, hf₂, hf₃, hf₄', hdegN _ (hψdeg 1 h1mem), hdegN _ (hνdeg 0 h0r),
      hdegN _ (hνdeg 1 h1r)]
  refine ⟨χ₂, χ₄, fun h => by rw [h, hχ₄1] at hχ₂1; norm_num at hχ₂1, hχ₂B, hχ₄B,
    basis.irreducible χ₂, basis.irreducible χ₄, hfaith₂, hfaith₄, hrat₂, hrat₄, hχ₂1, hχ₄1,
    hχ₂t, hχ₄t, fun u hu => ⟨hχ₂N u hu, hχ₄N u hu⟩, hoddrel, ?_, hNdvd, hmap⟩
  intro η V hV ρC E
  obtain ⟨hE, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hη V hV
  exact ⟨hE, h1, h2, h3, h4, h5, h6, h7, h8⟩

end CFSG.Semidihedral.Principal
