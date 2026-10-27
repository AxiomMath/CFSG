module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Interface
public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.FixedPair
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicTwE6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

theorem mem_zpowers_of_pow_three {G : Type*} [Group G] [Finite G] [IsCyclic G] {σ δ : G}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hδ3 : δ ^ 3 = 1) : δ ∈ Subgroup.zpowers σ := by
  classical
  have := Fintype.ofFinite G
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  by_contra hδ
  set S : Finset G := Finset.univ.filter fun a : G => a ^ 3 = 1 with hS
  have hsub : insert δ ((Finset.range 3).image (σ ^ ·)) ⊆ S := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | ⟨k, -, rfl⟩
    · exact hδ3
    · rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  have hinj : Set.InjOn (σ ^ ·) (Finset.range 3 : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < orderOf σ := by rw [hord]; exact Finset.mem_range.1 hi
    have hj' : j < orderOf σ := by rw [hord]; exact Finset.mem_range.1 hj
    exact pow_injOn_Iio_orderOf hi' hj' hij
  have hnot : δ ∉ (Finset.range 3).image (σ ^ ·) := by
    rw [Finset.mem_image]
    rintro ⟨k, -, rfl⟩
    exact hδ (Subgroup.npow_mem_zpowers σ k)
  have hcard : (insert δ ((Finset.range 3).image (σ ^ ·))).card = 4 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj, Finset.card_range]
  have := Finset.card_le_card hsub
  omega

theorem int_independent_of_nat {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h : ∀ i j : ℕ, a ^ i * b ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    ∀ i j : ℤ, a ^ i * b ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
  intro i j hij
  have ha' : a ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, ha]
  have hb' : b ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hb]
  rw [zpow_eq_zpow_emod i ha', zpow_eq_zpow_emod j hb'] at hij
  have hi0 : 0 ≤ i % 3 := Int.emod_nonneg _ (by norm_num)
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
  have hi3 : i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hj3 : j % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  rw [← Int.toNat_of_nonneg hi0, ← Int.toNat_of_nonneg hj0, zpow_natCast, zpow_natCast] at hij
  obtain ⟨h1, h2⟩ := h _ _ hij
  refine ⟨Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero ?_⟩ <;> omega

theorem ne_one_of_card_cube {Q : ℕ} (hQ : 1 < Q) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Q ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ Q) : σ ≠ 1 := by
  classical
  intro h
  have := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ Q - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hQ), Polynomial.IsRoot,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← hσ, h]
    exact sub_self _
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hQ, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hK] at hle
  have hlt : Q ^ 1 < Q ^ 3 := Nat.pow_lt_pow_right hQ (by norm_num)
  rw [pow_one] at hlt
  omega


theorem fixedThreePair {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    ∃ a b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, Commute a b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      (∀ i j : ℤ, a ^ i * b ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) ∧
      fieldActor σ σ a = a ∧ fieldActor σ σ b = b := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  obtain ⟨ι, η, hι, hη, hcomm⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2
      (fixSubfield σ) (fixSubfieldRestrict σ σ) (fixSubfieldRestrict_pow_eq_one σ hσ)
  have hJC := CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_le σ
  let φ : graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (fixSubfieldRestrict σ σ).toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    MonoidHom.codRestrict ((baseChangeGL (fixSubfield σ).subtype).comp
      (graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
        (fixSubfieldRestrict σ σ).toRingHom).subtype) _ fun g => hJC ⟨g, g.2, rfl⟩
  have hφinj : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective (fixSubfield σ).subtype (congrArg Subtype.val h))
  have hfix : ∀ g, fieldActor σ σ (φ g) = φ g := fun g =>
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ hσ3 (φ g)).1
      ⟨g, g.2, rfl⟩
  have hk : ∀ {F₁ : Type} [Field F₁]
      (R : Matrix.SpecialLinearGroup (Fin 2) F₁ →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Function.Injective R → ∀ g ∈ R.ker, ∃ l : F₁, (g : Matrix (Fin 2) (Fin 2) F₁) = l • 1 := by
    intro F₁ _ R hR g hg
    refine ⟨1, ?_⟩
    rw [hR (show R g = R 1 by rw [MonoidHom.mem_ker.1 hg, map_one])]
    simp
  have hind := CFSG.LocalAnalysis.RankThreeTheoremC.independent_of_commuting_sl2 (φ.comp ι)
    (φ.comp η) (fun A B => by
      show φ (ι A) * φ (η B) = φ (η B) * φ (ι A)
      rw [← map_mul, ← map_mul, hcomm])
    (hk _ (hφinj.comp hι)) (hk _ (hφinj.comp hη))
  simp only [MonoidHom.comp_apply] at hind
  have hι3 : φ (ι (CFSG.LocalAnalysis.RankThreeTheoremC.sl2OrderThree _)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, CFSG.LocalAnalysis.RankThreeTheoremC.sl2OrderThree_pow_three,
      map_one, map_one]
  have hη3 : φ (η (CFSG.LocalAnalysis.RankThreeTheoremC.sl2OrderThree _)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, CFSG.LocalAnalysis.RankThreeTheoremC.sl2OrderThree_pow_three,
      map_one, map_one]
  refine ⟨_, _, ?_, hι3, hη3, int_independent_of_nat hι3 hη3 hind, hfix _, hfix _⟩
  show φ (ι _) * φ (η _) = φ (η _) * φ (ι _)
  rw [← map_mul, ← map_mul, hcomm]

theorem false_of_outer_three_of_normalForm {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hNF : ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃! gδ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
        α = MulAut.conj gδ.1 * fieldActor σ gδ.2)
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ)
    (hcyc : IsCyclic (K ≃+* K)) (hcardAut : Nat.card (K ≃+* K) = 3 * f)
    (hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥)
    (E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hE : IsElemAbelian 3 E)
    (hout : ¬ E ≤ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hs : NarrowScope 3 E) : False := by
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    conj_injective_of_center_eq_bot hZ
  obtain ⟨ψ, hψE, hψ⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  obtain ⟨⟨g, δ⟩, hψgδ, -⟩ := hNF ψ
  simp only at hψgδ
  have hfX : fieldActor (t := TwistTag.D4) σ δ ∈
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ⊔ E := by
    have e : fieldActor (t := TwistTag.D4) σ δ = (MulAut.conj g)⁻¹ * ψ := by
      rw [hψgδ, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left ⟨g, rfl⟩)) (Subgroup.mem_sup_right hψE)
  have hδ3 : δ ^ 3 = 1 := by
    have h3 := congrArg Θ (hE.2 ψ hψE)
    rwa [map_pow, map_one, hΘ ψ g δ hψgδ] at h3
  have hf3 : fieldActor (t := TwistTag.D4) σ δ ^ 3 = 1 := by
    rw [← fieldActorHom_apply, ← map_pow, hδ3, map_one]
  have hfout : ∀ x, fieldActor (t := TwistTag.D4) σ δ ≠ MulAut.conj x := by
    intro x hx
    exact hψ ⟨g * x, by rw [hψgδ, hx, map_mul]⟩
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := ne_one_of_card_cube (Nat.one_lt_pow (by omega) hℓ.one_lt) hK σ hσ
  have := hcyc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_three hσ3 hσ1 hδ3)
  obtain ⟨a, b, hab, ha, hb, hind, hfa, hfb⟩ := fixedThreePair σ hσ3
  have hδ_eq : fieldActor (t := TwistTag.D4) σ δ = fieldActor (t := TwistTag.D4) σ σ ^ k := by
    rw [← hk]
    exact map_zpow (fieldActorHom (t := TwistTag.D4) σ) σ k
  have hpow : ∀ x, fieldActor (t := TwistTag.D4) σ σ x = x →
      ∀ n : ℕ, (fieldActor (t := TwistTag.D4) σ σ ^ n) x = x := fun x hx n => by
    induction n with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hx]
  have hfix : ∀ x, fieldActor (t := TwistTag.D4) σ σ x = x →
      fieldActor (t := TwistTag.D4) σ δ x = x := fun x hx => by
    rw [hδ_eq]
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast, hpow x hx n]
    · rw [zpow_neg, zpow_natCast, MulAut.inv_apply, MulEquiv.symm_apply_eq, hpow x hx n]
  exact false_of_fixed_pair_sup Nat.prime_three hinj hs hfX hf3 hfout hab ha hb hind
    (hfix a hfa) (hfix b hfb)

theorem outerModelGen_three : OuterModelGen (· = 3) := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ p hp hp2 hpℓ hp3 E hE hcard hout hs
  subst hp3
  exfalso
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcardAut, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  exact false_of_outer_three_of_normalForm hℓ hf hK σ hσ hNF Θ hΘ hcyc hcardAut hZ E hE hout hs

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
