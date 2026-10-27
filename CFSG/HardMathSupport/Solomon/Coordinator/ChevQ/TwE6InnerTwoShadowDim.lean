module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoA2Holonomy
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixDimTw
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.RankThree.E6 (weylMatrix)

private theorem shadowDim_three_ne_zero {K : Type} [Field K] (hK3 : ringChar K ≠ 3) :
    (3 : AlgebraicClosure K) ≠ 0 := by
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    rcases (Nat.dvd_prime Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 h') with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hK3 h1
  intro h
  apply h3K
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_ofNat, h, map_zero]

section Kind3A2


theorem twE6FixDim_eq_24_of_kind3A2 {K : Type} [Field K] {σ : K ≃+* K} (hK3 : ringChar K ≠ 3)
    {x : twistedE6RootGroup K σ} (hx3 : x ^ 3 = 1)
    {g0 t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {w : WeylGroup TwistTag.E6.tag}
    (hw3 : w ^ 3 = 1)
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (hN : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, v + w • v + w • w • v = 0) :
    twE6FixDim K σ x = 24 := by
  classical
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hmov : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → w • γ ≠ γ := by
    intro γ hγ he
    apply hγ.ne_zero
    have h := hN γ
    rw [he, he] at h
    funext i
    have h' := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
    omega
  have e1 : ∀ (p : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) [DecidablePred p],
      ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ ∧ p γ) = ∅ :=
    fun p _ => Finset.filter_false_of_mem fun γ hγ h => hmov γ (mem_rootFinset.1 hγ) h.1
  rw [twE6FixDim_eq_of_monomial_of_pow_three hx3 hw3 hx,
    finrank_ker_weylMatrix_sub_one_eq_zero (shadowDim_three_ne_zero hK3) hN, e1,
    Finset.filter_true_of_mem fun γ hγ => hmov γ (mem_rootFinset.1 hγ), Finset.card_empty,
    card_rootFinset]
  rfl

end Kind3A2

section Card


private theorem shadowDim_iform_neg_right {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right, neg_one_mul]

theorem card_filter_smul_eq_self_of_a2 {τ : Tag} {w : WeylGroup τ} {γ₁ γ₂ : Fin τ.rank → ℤ}
    (hγ : IsA2Pair γ₁ γ₂) (h₁ : w • γ₁ = γ₁) (h₂ : w • γ₂ = γ₂)
    (hfix : ∀ γ, IsRoot τ γ → w • γ = γ → γ ∈ a2Roots γ₁ γ₂) :
    ((rootFinset τ).filter fun γ => w • γ = γ).card = 6 := by
  classical
  have hset : ((rootFinset τ).filter fun γ => w • γ = γ) =
      {γ₁, -γ₁, γ₂, -γ₂, γ₁ + γ₂, -(γ₁ + γ₂)} := by
    ext γ
    simp only [Finset.mem_filter, mem_rootFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hγr, hwγ⟩
      simpa only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] using hfix γ hγr hwγ
    · intro h
      have hmem : γ ∈ a2Roots γ₁ γ₂ := by
        simpa only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] using h
      refine ⟨a2Roots_isRoot hγ γ hmem, ?_⟩
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [smul_neg, smul_add, h₁, h₂]
  obtain ⟨m, hm⟩ : ∃ m, iform γ₁ γ₂ = m := ⟨_, rfl⟩
  have h11 : iform γ₁ γ₁ = -2 * m := by
    have := hγ.two_iform
    rw [hm] at this
    linarith
  have h22 : iform γ₂ γ₂ = -2 * m := by rw [hγ.iform_snd, h11]
  have h21 : iform γ₂ γ₁ = m := by rw [iform_comm, hm]
  have hm0 : m ≠ 0 := by
    have := iform_self_pos hγ.isRoot_fst.ne_zero
    omega
  have hne : ∀ u v : Fin τ.rank → ℤ,
      (iform γ₁ u ≠ iform γ₁ v ∨ iform γ₂ u ≠ iform γ₂ v) → u ≠ v := by
    rintro u v h rfl
    simp at h
  have n1 : γ₁ ∉ ({-γ₁, γ₂, -γ₂, γ₁ + γ₂, -(γ₁ + γ₂)} : Finset (Fin τ.rank → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine hne _ _ ?_ <;>
      simp only [shadowDim_iform_neg_right, iform_add_right, h11, h22, hm, h21] <;> omega
  have n2 : -γ₁ ∉ ({γ₂, -γ₂, γ₁ + γ₂, -(γ₁ + γ₂)} : Finset (Fin τ.rank → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> refine hne _ _ ?_ <;>
      simp only [shadowDim_iform_neg_right, iform_add_right, h11, h22, hm, h21] <;> omega
  have n3 : γ₂ ∉ ({-γ₂, γ₁ + γ₂, -(γ₁ + γ₂)} : Finset (Fin τ.rank → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> refine hne _ _ ?_ <;>
      simp only [shadowDim_iform_neg_right, iform_add_right, h11, h22, hm, h21] <;> omega
  have n4 : -γ₂ ∉ ({γ₁ + γ₂, -(γ₁ + γ₂)} : Finset (Fin τ.rank → ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_⟩ <;> refine hne _ _ ?_ <;>
      simp only [shadowDim_iform_neg_right, iform_add_right, h11, h22, hm, h21] <;> omega
  have n5 : γ₁ + γ₂ ∉ ({-(γ₁ + γ₂)} : Finset (Fin τ.rank → ℤ)) := by
    simp only [Finset.mem_singleton]
    refine hne _ _ ?_
    simp only [shadowDim_iform_neg_right, iform_add_right, h11, h22, hm, h21]
    omega
  rw [hset, Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
    Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4,
    Finset.card_insert_of_notMem n5, Finset.card_singleton]

end Card

section Kind2A2


private theorem shadowDim_frame_pow_three {K : Type} [Field K] {σ : K ≃+* K}
    {x : twistedE6RootGroup K σ} (hx3 : x ^ 3 = 1)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0) ^ 3 = 1 := by
  rw [← twE6Frame_pow, hx3, twE6Frame_one]

theorem rootVec_fixed_of_kind2A2 {K : Type} [Field K] {σ : K ≃+* K}
    {x : twistedE6RootGroup K σ} (hx3 : x ^ 3 = 1)
    {g0 t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {w : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {γ₁ γ₂ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsA2Pair γ₁ γ₂) (h₁ : w • γ₁ = γ₁)
    (h₂ : w • γ₂ = γ₂)
    (hμ : ∃ μ : Fin TwistTag.E6.tag.rank → ℤ, 2 • γ₁ + γ₂ = μ + w • μ + w • w • μ)
    {γ γ' : Fin TwistTag.E6.tag.rank → ℤ} (hγa : γ ∈ a2Roots γ₁ γ₂) (hγ'a : γ' ∈ a2Roots γ₁ γ₂)
    (hfix : ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
        (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
          rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) :
    ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
        (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ') =
      rootVec TwistTag.E6.tag (AlgebraicClosure K) γ' := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact rootVec_fixed_of_a2Norm hx (shadowDim_frame_pow_three hx3 g0) hγ h₁ h₂ hμ hγa hγ'a hfix

theorem twE6FixDim_eq_24_iff_of_kind2A2 {K : Type} [Field K] {σ : K ≃+* K}
    (hK3 : ringChar K ≠ 3) {x : twistedE6RootGroup K σ} (hx3 : x ^ 3 = 1)
    {g0 t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {w : WeylGroup TwistTag.E6.tag}
    (hw3 : w ^ 3 = 1)
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {γ₁ γ₂ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsA2Pair γ₁ γ₂) (h₁ : w • γ₁ = γ₁)
    (h₂ : w • γ₂ = γ₂)
    (hfix : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → w • γ = γ →
      γ ∈ a2Roots γ₁ γ₂)
    (hμ : ∃ μ : Fin TwistTag.E6.tag.rank → ℤ, 2 • γ₁ + γ₂ = μ + w • μ + w • w • μ)
    (hN : ∀ j : Fin TwistTag.E6.tag.rank, ∃ m n : ℤ,
      (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) +
          w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) +
          w • w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        m • γ₁ + n • γ₂) :
    twE6FixDim K σ x = 24 ↔
      ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) ≠
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁ := by
  classical
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hy3 := shadowDim_frame_pow_three hx3 g0
  have hγ₁ : γ₁ ∈ a2Roots γ₁ γ₂ := Set.mem_insert _ _
  have hcard6 := card_filter_smul_eq_self_of_a2 hγ h₁ h₂ hfix
  have hcard66 : ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ ≠ γ).card = 66 := by
    have h := Finset.card_filter_add_card_filter_not (s := rootFinset TwistTag.E6.tag)
      (fun γ => w • γ = γ)
    rw [hcard6, card_rootFinset] at h
    have h72 : TwistTag.E6.tag.rootCount = 72 := rfl
    have e : ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ ≠ γ).card =
        ((rootFinset TwistTag.E6.tag).filter fun γ => ¬ w • γ = γ).card := rfl
    omega
  have eall : ∀ (p : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) [DecidablePred p],
      (∀ γ, IsRoot TwistTag.E6.tag γ → w • γ = γ → p γ) →
        ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ ∧ p γ) =
          (rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ :=
    fun p _ hp => Finset.filter_congr fun γ hγr =>
      ⟨fun h => h.1, fun h => ⟨h, hp γ (mem_rootFinset.1 hγr) h⟩⟩
  have enone : ∀ (p : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) [DecidablePred p],
      (∀ γ, IsRoot TwistTag.E6.tag γ → w • γ = γ → ¬ p γ) →
        ((rootFinset TwistTag.E6.tag).filter fun γ => w • γ = γ ∧ p γ) = ∅ :=
    fun p _ hp => Finset.filter_false_of_mem fun γ hγr h => hp γ (mem_rootFinset.1 hγr) h.1 h.2
  have h2 : Module.finrank (AlgebraicClosure K) (LinearMap.ker
      (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → AlgebraicClosure K)) - 1)) = 2 :=
    finrank_ker_weylMatrix_sub_one_of_a2 (shadowDim_three_ne_zero hK3) hw3 hγ h₁ h₂ hN
  rw [twE6FixDim_eq_of_monomial_of_pow_three hx3 hw3 hx, h2, hcard66]
  by_cases hv : ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
        Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
      (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁
  · rw [eall, hcard6]
    · exact ⟨fun h => absurd h (by norm_num), fun h => absurd hv h⟩
    · exact fun γ hγr hwγ =>
        rootVec_fixed_of_a2Norm hx hy3 hγ h₁ h₂ hμ hγ₁ (hfix γ hγr hwγ) hv
  · rw [enone, Finset.card_empty]
    · exact ⟨fun _ => hv, fun _ => rfl⟩
    · exact fun γ hγr hwγ hγv =>
        hv (rootVec_fixed_of_a2Norm hx hy3 hγ h₁ h₂ hμ (hfix γ hγr hwγ) hγ₁ hγv)

end Kind2A2

section Fixer


@[expose] def twE6RootVecFixer (K : Type) [Field K] (σ : K ≃+* K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (S : Set (Fin TwistTag.E6.tag.rank → ℤ)) :
    Subgroup (twistedE6RootGroup K σ) where
  carrier := {x | ∀ γ ∈ S, ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
        Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
      (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ}
  mul_mem' {x y} hx hy γ hγ := by
    rw [twE6Frame_mul]
    exact units_mul_apply_eq_self (hx γ hγ) (hy γ hγ)
  one_mem' γ _ := by
    rw [twE6Frame_one, Units.val_one, Module.End.one_apply]
  inv_mem' {x} hx γ hγ := by
    rw [twE6Frame_inv]
    exact units_inv_apply_eq_self (hx γ hγ)

theorem mem_twE6RootVecFixer {K : Type} [Field K] {σ : K ≃+* K}
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    {x : twistedE6RootGroup K σ} :
    x ∈ twE6RootVecFixer K σ g0 S ↔ ∀ γ ∈ S, ((g0⁻¹ * baseChangeGL (algebraMap K
      (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
        (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
      rootVec TwistTag.E6.tag (AlgebraicClosure K) γ :=
  Iff.rfl

theorem twE6RootVecFixer_anti {K : Type} [Field K] {σ : K ≃+* K}
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {S T : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (h : S ⊆ T) : twE6RootVecFixer K σ g0 T ≤ twE6RootVecFixer K σ g0 S :=
  fun _ hx γ hγ => hx γ (h hγ)

end Fixer

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {G : Type*} [Group G] {w u : G} (hw : w ^ 3 = 1)
    (hu : u ∈ Subgroup.zpowers w) : u = 1 ∨ u = w ∨ u = w⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hw' : w ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hw
  have hk : w ^ k = w ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, hw', one_zpow, mul_one]
  rw [hk]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero w)
  · exact Or.inr (Or.inl (zpow_one w))
  · refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_left ?_))
    rw [← zpow_add_one]
    exact hw'

section CaseII


theorem not_kind3A2_of_twE6FixDim_ne {K : Type} [Field K] {σ : K ≃+* K} (hK3 : ringChar K ≠ 3)
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : ∀ x ∈ E₀, x ^ 3 = 1)
    (hII : ∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24)
    {g0 t : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {x : twistedE6RootGroup K σ} (hx : x ∈ E₀)
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hxu : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) :
    ¬ ∀ v : Fin TwistTag.E6.tag.rank → ℤ, v + u • v + u • u • v = 0 := by
  intro hk3
  have hu3 := pow_eq_one_of_twE6Frame_eq (hE₀ x hx) ht hxu
  refine hII x hx ?_ (twE6FixDim_eq_24_of_kind3A2 hK3 (hE₀ x hx) ht hu3 hxu hk3)
  rintro rfl
  rw [twE6Frame_one] at hxu
  obtain rfl := eq_one_of_one_eq_torus_mul_canonicalRep ht hxu
  have h := congrFun (hk3 (Pi.single ⟨0, by decide⟩ 1)) ⟨0, by decide⟩
  simp at h

theorem mem_twE6RootVecFixer_of_kind2A2 {K : Type} [Field K] {σ : K ≃+* K}
    (hK3 : ringChar K ≠ 3) {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : ∀ x ∈ E₀, x ^ 3 = 1)
    (hII : ∀ s ∈ E₀, s ≠ 1 → twE6FixDim K σ s ≠ 24)
    {g0 t : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {x : twistedE6RootGroup K σ} (hx : x ∈ E₀)
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hxu : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    {γ₁ γ₂ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsA2Pair γ₁ γ₂) (h₁ : u • γ₁ = γ₁)
    (h₂ : u • γ₂ = γ₂)
    (hfix : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
      γ ∈ a2Roots γ₁ γ₂)
    (hμ : ∃ μ : Fin TwistTag.E6.tag.rank → ℤ, 2 • γ₁ + γ₂ = μ + u • μ + u • u • μ)
    (hN : ∀ j : Fin TwistTag.E6.tag.rank, ∃ m n : ℤ,
      (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) +
          u • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) +
          u • u • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        m • γ₁ + n • γ₂) :
    x ∈ twE6RootVecFixer K σ g0 (a2Roots γ₁ γ₂) := by
  by_cases hx1 : x = 1
  · subst hx1
    exact one_mem _
  have hu3 := pow_eq_one_of_twE6Frame_eq (hE₀ x hx) ht hxu
  have hv := not_not.1 fun hne =>
    hII x hx hx1 ((twE6FixDim_eq_24_iff_of_kind2A2 hK3 (hE₀ x hx) ht hu3 hxu hγ h₁ h₂ hfix hμ
      hN).2 hne)
  exact mem_twE6RootVecFixer.2 fun γ hγa =>
    rootVec_fixed_of_kind2A2 (hE₀ x hx) ht hxu hγ h₁ h₂ hμ (Set.mem_insert _ _) hγa hv

end CaseII

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
