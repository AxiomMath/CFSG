module

public import Certificates.Certificate214102
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.Steinberg.Adjoint

theorem twA2Plane_exists
    (x y z : Fin Tag.E6.rank → ZMod 3)
    (hreg : ∀ α, IsRoot Tag.E6 α → triPairing x α = 0 → triPairing y α = 0 →
      triPairing z α ≠ 0) :
    ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
      IsRoot Tag.E6 (β₁ + β₂) ∧ triPairing x (β₁ - β₂) = 0 ∧ triPairing y (β₁ - β₂) = 0 ∧
      triPairing z (β₁ - β₂) = 0 ∧
      ∃ δ : Fin Tag.E6.rank → ℤ, triPairing x δ = 0 ∧ triPairing y δ = 0 ∧
        triPairing z δ = 0 ∧ ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂) :=
  Certificates.certificate214102 x y z hreg

private theorem twNeg_three_mul_card_le {G : Type*} [Group G] {E H H' : Subgroup G}
    (hE : Nat.card E = 3 ^ 3) (hH'E : H' ≤ E) (hHH' : H < H') :
    3 * Nat.card H ≤ Nat.card H' := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  haveI : Finite H' :=
    Finite.of_injective (Subgroup.inclusion hH'E) (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hHH'
  have h3 : Nat.card H' ∣ 3 ^ 3 := hE ▸ Subgroup.card_dvd_of_le hH'E
  have h2 : Nat.card H ∣ 3 ^ 3 := (Subgroup.card_dvd_of_le hHH'.le).trans h3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [hk, hj] at h1 ⊢
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  calc 3 * 3 ^ j = 3 ^ (j + 1) := by ring
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hjk

private theorem twNeg_step {G : Type*} [Group G] {E H : Subgroup G} (hE : Nat.card E = 3 ^ 3)
    (hHE : H ≤ E) :
    ∃ x ∈ E, min (3 * Nat.card H) (3 ^ 3) ≤ Nat.card ↥(H ⊔ Subgroup.closure {x}) := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  by_cases h : E ≤ H
  · refine ⟨1, E.one_mem, ?_⟩
    have hle' : H ⊔ Subgroup.closure {(1 : G)} ≤ E :=
      sup_le hHE ((Subgroup.closure_le E).2 (Set.singleton_subset_iff.2 E.one_mem))
    haveI : Finite ↥(H ⊔ Subgroup.closure {(1 : G)}) :=
      Finite.of_injective (Subgroup.inclusion hle') (Subgroup.inclusion_injective _)
    calc min (3 * Nat.card H) (3 ^ 3) ≤ 3 ^ 3 := min_le_right _ _
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card ↥(H ⊔ Subgroup.closure {(1 : G)}) :=
        Subgroup.card_le_of_le (h.trans le_sup_left)
  · obtain ⟨x, hxE, hxH⟩ := SetLike.not_le_iff_exists.1 h
    refine ⟨x, hxE, (min_le_left _ _).trans (twNeg_three_mul_card_le hE ?_ ?_)⟩
    · exact sup_le hHE ((Subgroup.closure_le E).2 (Set.singleton_subset_iff.2 hxE))
    · refine lt_of_le_of_ne le_sup_left fun h' => hxH ?_
      rw [h']
      exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)

private theorem twNeg_exists_gen {G : Type*} [Group G] (E : Subgroup G)
    (hE : Nat.card E = 3 ^ 3) :
    ∃ x₁ ∈ E, ∃ x₂ ∈ E, ∃ x₃ ∈ E, ∀ N : Subgroup G, x₁ ∈ N → x₂ ∈ N → x₃ ∈ N → E ≤ N := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hcl : ∀ {x : G} {N : Subgroup G}, x ∈ N → Subgroup.closure {x} ≤ N := fun hx =>
    (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hx)
  obtain ⟨x₁, hx₁, h₁⟩ := twNeg_step hE (bot_le : (⊥ : Subgroup G) ≤ E)
  have hH₁ : (⊥ : Subgroup G) ⊔ Subgroup.closure {x₁} ≤ E := sup_le bot_le (hcl hx₁)
  obtain ⟨x₂, hx₂, h₂⟩ := twNeg_step hE hH₁
  have hH₂ : (⊥ : Subgroup G) ⊔ Subgroup.closure {x₁} ⊔ Subgroup.closure {x₂} ≤ E :=
    sup_le hH₁ (hcl hx₂)
  obtain ⟨x₃, hx₃, h₃⟩ := twNeg_step hE hH₂
  have hH₃ : (⊥ : Subgroup G) ⊔ Subgroup.closure {x₁} ⊔ Subgroup.closure {x₂} ⊔
      Subgroup.closure {x₃} ≤ E := sup_le hH₂ (hcl hx₃)
  rw [Subgroup.card_bot] at h₁
  simp only [min_le_iff] at h₁ h₂ h₃
  have hc : Nat.card E ≤ Nat.card ↥((⊥ : Subgroup G) ⊔ Subgroup.closure {x₁} ⊔
      Subgroup.closure {x₂} ⊔ Subgroup.closure {x₃}) := by
    rw [hE]
    omega
  have hEq := Subgroup.eq_of_le_of_card_ge hH₃ hc
  refine ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, fun N h1 h2 h3 => ?_⟩
  rw [← hEq]
  exact sup_le (sup_le (sup_le bot_le (hcl h1)) (hcl h2)) (hcl h3)

private theorem twNeg_prod_zpow {M ι : Type*} [CommGroup M] (ξ : M) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem twNeg_triPairing_three_smul {τ : Tag} (b : Fin τ.rank → ZMod 3)
    (v : Fin τ.rank → ℤ) : triPairing b ((3 : ℤ) • v) = 0 := by
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  simp only [triPairing, Pi.smul_apply, smul_eq_mul, Int.cast_mul, h3, zero_mul, mul_zero,
    Finset.sum_const_zero]

private theorem twNeg_exists_omega (K : Type) [Field K] (hr : ringChar K ≠ 3) :
    ∃ ω : (AlgebraicClosure K)ˣ, IsPrimitiveRoot (ω : AlgebraicClosure K) 3 := by
  have hne3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)),
      map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 ((ringChar.spec K 3).1 h) with h1 | h3
    · exact CharP.ringChar_ne_one h1
    · exact hr h3
  haveI : NeZero ((3 : ℕ) : AlgebraicClosure K) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  exact ⟨(hζ.isUnit (by norm_num)).unit, by rw [IsUnit.unit_spec]; exact hζ⟩

private theorem twNeg_rootChar_eq_one {τ : Tag} {L : Type} [Field L] {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (k : Fin τ.rank → ℕ) (m : Fin τ.rank → ℤ)
    (h : triPairing (fun i => (k i : ZMod 3)) m = 0) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (fun i => ω ^ k i) m = 1 := by
  have e : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
      (fun i => ω ^ k i) m = ω ^ (∑ i, (k i : ℤ) * m i) := by
    unfold CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
    rw [← twNeg_prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show (ω ^ k i) ^ m i = _
    rw [← zpow_natCast, ← zpow_mul]
  have h0 : ((∑ i, (k i : ℤ) * m i : ℤ) : ZMod 3) = 0 := by
    rw [← h]
    simp [triPairing]
  obtain ⟨c, hc⟩ : (3 : ℤ) ∣ ∑ i, (k i : ℤ) * m i := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h0
  rw [e, hc, zpow_mul, show ω ^ (3 : ℤ) = 1 by exact_mod_cast hω3, one_zpow]

section Plane

open CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private noncomputable def twNegChar (L : Type) [Field L] (m : Fin TwistTag.E6.tag.rank → ℤ) :
    (Fin TwistTag.E6.tag.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a m
  map_one' := by simp [rootChar]
  map_mul' a b := by simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private noncomputable def twNegDiag (K : Type) [Field K] (σ : K ≃+* K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
    (twistedE6RootGroup K σ).subtype)

private theorem twNegDiag_apply (K : Type) [Field K] (σ : K ≃+* K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (x : twistedE6RootGroup K σ) :
    twNegDiag K σ g0 x =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0 := by
  simp [twNegDiag, MulAut.conj_apply]

private noncomputable def twNegKer (K : Type) [Field K] (σ : K ≃+* K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (m : Fin TwistTag.E6.tag.rank → ℤ) :
    Subgroup (twistedE6RootGroup K σ) :=
  ((twNegChar (AlgebraicClosure K) m).ker.map
    (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))).comap (twNegDiag K σ g0)

private theorem mem_twNegKer {K : Type} [Field K] {σ : K ≃+* K}
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {m : Fin TwistTag.E6.tag.rank → ℤ}
    {x : twistedE6RootGroup K σ} :
    x ∈ twNegKer K σ g0 m ↔ ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootChar a m = 1 ∧ rootDiagUnit TwistTag.E6.tag a =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 := by
  rw [twNegKer, Subgroup.mem_comap, Subgroup.mem_map, twNegDiag_apply]
  rfl

private theorem twNeg_exponent {K : Type} [Field K] {σ : K ≃+* K}
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {ω : (AlgebraicClosure K)ˣ}
    (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3) {x : twistedE6RootGroup K σ}
    (hx3 : x ^ 3 = 1)
    (hT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) :
    ∃ k : Fin TwistTag.E6.tag.rank → ℕ, rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0 := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom hT)
  have hd3 : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0) ^ 3 = 1 := by
    rw [← twNegDiag_apply K σ g0 x, ← map_pow, hx3, map_one]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) = rootDiagUnit TwistTag.E6.tag 1 := by
      have e1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) =
          (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K) a) ^ 3 :=
        map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) a 3
      rw [e1, ha, hd3]
      exact (map_one (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))).symm
    intro i
    simpa using congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) i
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 3 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hk])⟩
  choose k hk using fun i => hpow (a i) (ha3 i)
  refine ⟨k, ?_⟩
  rw [← ha]
  exact congrArg (rootDiagUnit TwistTag.E6.tag) (funext fun i => (hk i).symm)

theorem exists_a2Plane_of_regular (K : Type) [Field K]
    (σ : K ≃+* K) (hr : ringChar K ≠ 3) (E₀ : Subgroup (twistedE6RootGroup K σ))
    (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 3)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hT : ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hreg : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      ¬ TwKills K σ E₀ g0 α) :
    ∃ β₁ β₂ δ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β₁ ∧
      IsRoot TwistTag.E6.tag β₂ ∧ IsRoot TwistTag.E6.tag (β₁ + β₂) ∧
      TwKills K σ E₀ g0 ((3 : ℤ) • β₁) ∧ TwKills K σ E₀ g0 δ ∧
      ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂) ∧
      ∃ P : Subgroup (twistedE6RootGroup K σ), P ≤ E₀ ∧ P.relIndex E₀ = 3 ∧
        ∀ x ∈ P, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit TwistTag.E6.tag a = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0 ∧ rootChar a β₁ = 1 ∧ rootChar a β₂ = 1 := by
  obtain ⟨ω, hω⟩ := twNeg_exists_omega K hr
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, hgen⟩ := twNeg_exists_gen E₀ hcard
  obtain ⟨k₁, hk₁⟩ := twNeg_exponent hω (hexp x₁ hx₁) (hT x₁ hx₁)
  obtain ⟨k₂, hk₂⟩ := twNeg_exponent hω (hexp x₂ hx₂) (hT x₂ hx₂)
  obtain ⟨k₃, hk₃⟩ := twNeg_exponent hω (hexp x₃ hx₃) (hT x₃ hx₃)
  have hkill : ∀ m : Fin TwistTag.E6.tag.rank → ℤ,
      triPairing (fun i => (k₁ i : ZMod 3)) m = 0 → triPairing (fun i => (k₂ i : ZMod 3)) m = 0 →
      triPairing (fun i => (k₃ i : ZMod 3)) m = 0 → TwKills K σ E₀ g0 m := by
    intro m h₁ h₂ h₃
    have hle : E₀ ≤ twNegKer K σ g0 m := hgen _
      (mem_twNegKer.2 ⟨_, twNeg_rootChar_eq_one hω3 k₁ m h₁, hk₁⟩)
      (mem_twNegKer.2 ⟨_, twNeg_rootChar_eq_one hω3 k₂ m h₂, hk₂⟩)
      (mem_twNegKer.2 ⟨_, twNeg_rootChar_eq_one hω3 k₃ m h₃, hk₃⟩)
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_twNegKer.1 (hle hx)
    exact ⟨a, hax, ha⟩
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hβ₁₂, hd₁, hd₂, hd₃, δ, hδ₁, hδ₂, hδ₃, hδθ⟩ :
      ∃ β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β₁ ∧
        IsRoot TwistTag.E6.tag β₂ ∧ IsRoot TwistTag.E6.tag (β₁ + β₂) ∧
        triPairing (fun i => (k₁ i : ZMod 3)) (β₁ - β₂) = 0 ∧
        triPairing (fun i => (k₂ i : ZMod 3)) (β₁ - β₂) = 0 ∧
        triPairing (fun i => (k₃ i : ZMod 3)) (β₁ - β₂) = 0 ∧
        ∃ δ : Fin TwistTag.E6.tag.rank → ℤ, triPairing (fun i => (k₁ i : ZMod 3)) δ = 0 ∧
          triPairing (fun i => (k₂ i : ZMod 3)) δ = 0 ∧
          triPairing (fun i => (k₃ i : ZMod 3)) δ = 0 ∧ ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂) :=
    twA2Plane_exists (fun i => (k₁ i : ZMod 3)) (fun i => (k₂ i : ZMod 3))
      (fun i => (k₃ i : ZMod 3)) (fun α hα h₁ h₂ h₃ => hreg α hα (hkill α h₁ h₂ h₃))
  have hrange : ∀ x : E₀, (twNegDiag K σ g0).comp E₀.subtype x ∈
      (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)).range := by
    intro x
    have h := hT x x.2
    rw [← twNegDiag_apply] at h
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.torusGroup_le_range_rootDiagUnitHom h
  set f := ((twNegDiag K σ g0).comp E₀.subtype).codRestrict _ hrange with hf
  set e := MonoidHom.ofInjective (f := rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))
    CFSG.LieType.Chevalley.rootDiagUnit_injective with he
  set c : E₀ →* (Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) :=
    e.symm.toMonoidHom.comp f with hc
  have hcx : ∀ x : E₀, rootDiagUnit TwistTag.E6.tag (c x) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
    intro x
    have h1 : ((e (c x) : (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)).range) :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
          rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K) (c x) :=
      MonoidHom.ofInjective_apply _
    have h2 : e (c x) = f x := by simp [hc]
    have h3 : ((f x : (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)).range) :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) = twNegDiag K σ g0 x := rfl
    rw [h2, h3, twNegDiag_apply] at h1
    exact h1.symm
  set χ : E₀ →* (AlgebraicClosure K)ˣ := (twNegChar (AlgebraicClosure K) β₁).comp c with hχ
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle3 : χ.range ≤ rootsOfUnity 3 (AlgebraicClosure K) := by
    rintro _ ⟨x, rfl⟩
    refine (mem_rootsOfUnity 3 _).2 ?_
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hexp x x.2)
    rw [← map_pow, hx3, map_one]
  have hcard3 : Nat.card χ.range ≤ 3 :=
    (Subgroup.card_le_of_le hle3).trans (card_rootsOfUnity _ _)
  have hdvd : Nat.card χ.range ∣ 3 ^ 3 := (Subgroup.card_range_dvd χ).trans hcard.dvd
  obtain ⟨x₀, hx₀, hx₀χ⟩ : ∃ x ∈ E₀, ∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 → rootChar a β₁ ≠ 1 := by
    have h := hreg β₁ hβ₁
    simp only [TwKills, not_forall, not_exists, not_and] at h
    obtain ⟨x, hx, h⟩ := h
    exact ⟨x, hx, h⟩
  have hne : χ.range ≠ ⊥ := by
    intro hbot
    have h : χ ⟨x₀, hx₀⟩ ∈ χ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h
    exact hx₀χ _ (hcx ⟨x₀, hx₀⟩) h
  haveI : Finite χ.range :=
    Nat.finite_of_card_ne_zero fun h0 => by rw [h0] at hdvd; norm_num at hdvd
  have hone : 1 < Nat.card χ.range := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hχcard : Nat.card χ.range = 3 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hj'] at hcard3 hone ⊢
    interval_cases j <;> simp_all
  refine ⟨β₁, β₂, δ, hβ₁, hβ₂, hβ₁₂,
    hkill _ (twNeg_triPairing_three_smul _ _) (twNeg_triPairing_three_smul _ _)
      (twNeg_triPairing_three_smul _ _),
    hkill δ hδ₁ hδ₂ hδ₃, hδθ, χ.ker.map E₀.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : (χ.ker.map E₀.subtype).subgroupOf E₀ = χ.ker :=
      Subgroup.comap_map_eq_self_of_injective E₀.subtype_injective _
    rw [Subgroup.relIndex, h1, Subgroup.index_ker, hχcard]
  · rintro _ ⟨y, hy, rfl⟩
    have hy1 : rootChar (c y) β₁ = 1 := MonoidHom.mem_ker.1 hy
    refine ⟨c y, hcx y, hy1, ?_⟩
    obtain ⟨a', ha', hchar⟩ := hkill (β₁ - β₂) hd₁ hd₂ hd₃ y y.2
    have haa : a' = c y := CFSG.LieType.Chevalley.rootDiagUnit_injective (ha'.trans (hcx y).symm)
    rw [haa] at hchar
    have hsplit : rootChar (c y) β₁ = rootChar (c y) (β₁ - β₂) * rootChar (c y) β₂ := by
      rw [← rootChar_add, sub_add_cancel]
    rwa [hy1, hchar, one_mul, eq_comm] at hsplit

end Plane

end CFSG.LieType.SeitzGeneration.ExcWideThree
