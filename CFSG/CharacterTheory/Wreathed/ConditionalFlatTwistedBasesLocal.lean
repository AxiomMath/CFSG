module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamilies
public import CFSG.CharacterTheory.Wreathed.FullDefectBlockLabels

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatTwistedBases

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CompatibleFamilies
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.BrauerWong

variable {G : Type} [Group G]

theorem eq_of_orderOf_eq_two_of_mem_zpowers [Finite G] {u y z : G}
    (hy : y ∈ Subgroup.zpowers u) (hz : z ∈ Subgroup.zpowers u) (hy2 : orderOf y = 2)
    (hz2 : orderOf z = 2) : y = z := by
  have hle : Subgroup.zpowers (⟨y, hy⟩ : Subgroup.zpowers u) ≤
      Subgroup.zpowers (⟨z, hz⟩ : Subgroup.zpowers u) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hy2, hz2]
  have hmem := hle (Subgroup.mem_zpowers _)
  rw [mem_zpowers_iff_mem_range_orderOf, Subgroup.orderOf_mk, hz2] at hmem
  obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hmem
  have hiy' : z ^ i = y := congrArg Subtype.val hiy
  rw [Finset.mem_range] at hi
  interval_cases i
  · rw [pow_zero] at hiy'
    rw [← hiy', orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  · rw [pow_one] at hiy'
    exact hiy'.symm

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem centralizer_zpowers_le_involutionCentralizer {u : G}
    (hxu : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers u) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) ≤ involutionCentralizer n S e :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxu)

omit [Group G] in
theorem centralizer_zpowers_eq_singleton [Group G] (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer {u} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem closure_half_eq (hn : 2 ≤ n) :
    Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} =
      Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} :=
  (BaseFourCentralizerStructure.modelT_eq_actual_generated n S e).symm.trans
    (modelT_eq_closure S e (by omega))

include e in
theorem normalizer_eq_mul_centralizer [Finite G] (hn : 2 ≤ n) :
    ∀ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), ∃ q ∈ (S : Subgroup G),
      ∃ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), x = q * c := by
  intro x hx
  obtain ⟨d, hd⟩ :=
    (BaseFourCentralizerStructure.sylow_and_base_four_group_centralizer_structure n hn S
      e).normalizer_direct
  refine ⟨(d.symm ⟨x, hx⟩).1, (d.symm ⟨x, hx⟩).1.2, (d.symm ⟨x, hx⟩).2,
    BaseFourCentralizerStructure.ambientOddCore_le _ (d.symm ⟨x, hx⟩).2.2, ?_⟩
  have hdx := hd (d.symm ⟨x, hx⟩)
  rw [MulEquiv.apply_symm_apply] at hdx
  exact hdx

variable [Fintype G] [IsSimpleGroup G]

theorem exists_flat_extension (hnonab : ∃ a b : G, a * b ≠ b * a) (hn : 2 ≤ n) {η : G}
    (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (χ : BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)) → ℂ)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * y →
        θt c = χ y)
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ) :
    ∃ lam : involutionCentralizer n S e →* ℂˣ,
      (∀ (v : involutionCentralizer n S e) (y : BaseFourCentralizerStructure.ambientOddCore
          (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (v : G) = y → (lam v : ℂ) = χ y) ∧
      (∀ v : involutionCentralizer n S e, (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
      ∀ c c' : involutionCentralizer n S e,
        (c : G) ∈ Subgroup.centralizer (Subgroup.closure
          {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
            wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) →
        (c' : G) = η⁻¹ * c * η → lam c' = lam c := by
  obtain ⟨lam, h1, h2, h3⟩ := exists_extension_of_family hnonab S e hn hη
    (BaseFourCentralizerStructure.ambientOddCore_le _) χ θt
    (fun c y hcy => hθt c 1 y (Subgroup.one_mem _) (by rw [one_mul]; exact hcy)) hψ
  refine ⟨lam, h1, h2, fun c c' hc hc' => h3 c c' ?_ hc'⟩
  rwa [← closure_half_eq S e hn]

theorem flat_local_block (hnonab : ∃ a b : G, a * b ≠ b * a) (hn : 2 ≤ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θ : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θ θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (θt : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (hθt : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      z ∈ Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) → (c : G) = z * y →
        θt c = (eb.representation θ).character y)
    {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    (lam : involutionCentralizer n S e →* ℂˣ)
    (h1 : ∀ (v : involutionCentralizer n S e) (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      (v : G) = y → (lam v : ℂ) = (eb.representation θ).character y)
    (h2 : ∀ v : involutionCentralizer n S e, (v : G) ∈ (S : Subgroup G) → lam v = 1)
    (h3 : ∀ c c' : involutionCentralizer n S e,
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure
        {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
          wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c)
    (u : G) (hu : IsPGroup 2 (Subgroup.zpowers u))
    (hxu : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers u) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) = Subgroup.centralizer {u} ∧
    ∀ (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers u : Set G))),
      (∃ ℓ : localBasis.index, ∀ c, (localBasis.representation ℓ).character c =
        lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) ∧
      ∀ ℓ principal : localBasis.index,
        (∀ c, (localBasis.representation ℓ).character c =
          lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) →
        (localBasis.representation principal).character = 1 →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu
            (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis ℓ =
          centralCharacterResidueHom basis ideal B ∧
        (∀ β, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hu
            (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) localBasis β =
              centralCharacterResidueHom basis ideal B →
          sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β ℓ) ∧
        ∀ θ', θ' ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ ↔
          ∃ χ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) principal,
            ∀ c, (localBasis.representation θ').character c =
              (lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c) :
                ℂ) * (localBasis.representation χ).character c := by
  set J := wreathModelHom S e (Original.x (2 ^ n)) with hJ
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n)) with hJ₁
  have hle := centralizer_zpowers_le_involutionCentralizer S e hxu
  have h3' : ∀ c c' : Subgroup.centralizer {J},
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c := by
    intro c c' hc hc'
    rw [← closure_half_eq S e hn] at hc
    exact h3 c c' hc hc'
  have hlam := isInvariant S e hn hη hord h2 h3'
  have cfg := localConfig S e hnonab hn hη hord
  obtain ⟨ψ, hψ⟩ := cfg.exists_isSpecialFamily (lam := lam)
  have hθt' : ∀ (c : Subgroup.centralizer ((S : Subgroup G) : Set G)) (z : G)
      (y : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
      z ∈ modelCenter S e → (c : G) = z * y → θt c = (eb.representation θ).character y := by
    intro c z y hz hc
    rw [modelCenter_eq_zpowers] at hz
    exact hθt c z y hz hc
  have hfam : CompatibleCentralizerFamily 2 (S : Subgroup G) θt ψ :=
    compatible_of_isSpecialFamily S e hn cfg hlam hψ (isSpecial_sylow S e hn)
      (sylow_le_centralizer_x S e hn) (eb.representation θ).character h1 h2 θt hθt'
  have hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (nb.representation θhat).character x = ψ S c := by
    intro x q c hq hx
    obtain ⟨z, hz, y, hzy⟩ := exists_center_mul_oddCore S e hn c
    rw [hfam.2.2.2 c, hθt' c z y hz hzy]
    have hqz : q * z ∈ (S : Subgroup G) := Subgroup.mul_mem _ hq (modelCenter_le_sylow S e hz)
    have h := hθ ⟨q * z, hqz⟩ y
    convert h using 2
    apply Subtype.ext
    change (x : G) = q * z * y
    rw [hx, hzy, mul_assoc]
  have hS1 : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hJS : J ∈ (S : Subgroup G) := wreathModelHom_mem S e _
    rw [hbot, Subgroup.mem_bot] at hJS
    exact cfg.ne_one hJS
  have hmain := compatible_family_unique_local_blocks basis ideal 2 S hS1
    (normalizer_eq_mul_centralizer S e hn) θt ψ hfam nb θhat hlambda B hB
  have hQ1 : Subgroup.zpowers u ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxu
    exact cfg.ne_one hxu
  have hJC : J ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxu
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hk]
    exact ((Commute.refl u).zpow_zpow l k).eq
  have hsp : IsSpecial J (Subgroup.closure {J, J₁}) (Subgroup.zpowers u) := by
    refine Or.inl ⟨⟨hxu, hJC⟩, fun y hy hy2 => ?_⟩
    exact eq_of_orderOf_eq_two_of_mem_zpowers hy.1 hxu hy2 cfg.orderOf_eq
  have hψQ : ∀ c : Subgroup.centralizer (Subgroup.zpowers u : Set G),
      ψ (Subgroup.zpowers u) c = lam (Subgroup.inclusion hle c) := by
    intro c
    rw [cfg.apply_eq_of_isSpecial hlam hψ hu hQ1 hsp c]
    exact extend_of_mem (hle c.2)
  obtain ⟨-, -, -, -, hcyclic⟩ := hmain
  obtain ⟨-, hlocal⟩ := hcyclic (Subgroup.zpowers u) hu hQ1 inferInstance
  refine ⟨centralizer_zpowers_eq_singleton u, fun localBasis => ⟨?_, ?_⟩⟩
  · exact CompatibleFamily.exists_linear_label localBasis (lam.comp (Subgroup.inclusion hle))
  · intro ℓ principal hℓ hprincipal
    have hℓψ : ∀ c, (localBasis.representation ℓ).character c = ψ (Subgroup.zpowers u) c := by
      intro c
      rw [hℓ, hψQ]
    obtain ⟨hbrauer, hunique, htwist⟩ := hlocal localBasis ℓ principal hℓψ hprincipal
    refine ⟨hbrauer, hunique, fun θ' => ?_⟩
    rw [htwist θ']
    simp only [hψQ]

end CFSG.Wreathed.FlatTwistedBases
