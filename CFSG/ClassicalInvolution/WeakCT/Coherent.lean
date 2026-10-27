module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

section Adjust

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_adjust (hK : 4 ≤ Nat.card K) {θ θ₀ : SL(3, K) →* X} {V₀ V₁ V₂ : Subgroup X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, K)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, K))
    (h0 : (B12 K).map θ = V₀) (h1 : (B23 K).map θ = V₁) (h1' : (B12 K).map θ₀ = V₁)
    (h2 : (B23 K).map θ₀ = V₂) (hcomm : ∀ x ∈ V₀, ∀ y ∈ V₂, x * y = y * x) :
    ∃ θ' : SL(3, K) →* X, θ'.ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map θ' = V₁ ∧
      (B23 K).map θ' = V₂ ∧
      θ'.comp (blockSL K 3 2 0 (by omega)) = θ.comp (blockSL K 3 2 1 (by omega)) := by
  have hK3 : 3 ≤ Nat.card K := by omega
  have hm₁ : Function.Injective (θ.comp (blockSL K 3 2 1 (by omega))) :=
    comp_blockSL_injective hθ _ (by omega)
  have hm₂ : Function.Injective (θ₀.comp (blockSL K 3 2 0 (by omega))) :=
    comp_blockSL_injective hθ₀ _ (by omega)
  have hr₁ : (θ.comp (blockSL K 3 2 1 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1]
    rfl
  have hr₂ : (θ₀.comp (blockSL K 3 2 0 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1']
    rfl
  have hrr : (θ.comp (blockSL K 3 2 1 (by omega))).range =
      (θ₀.comp (blockSL K 3 2 0 (by omega))).range := hr₁.trans hr₂.symm
  let α : SL(2, K) ≃* SL(2, K) :=
    (MonoidHom.ofInjective hm₁).trans
      ((MulEquiv.subgroupCongr hrr).trans (MonoidHom.ofInjective hm₂).symm)
  have hα : ∀ A, θ₀ (blockSL K 3 2 0 (by omega) (α A)) = θ (blockSL K 3 2 1 (by omega) A) := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hm₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrr (MonoidHom.ofInjective hm₁ A)))
    exact h
  have hD : (D23 K).map θ = (D12 K).map θ₀ :=
    torus_agree hK3 hθ hθ₀ (h1.trans h1'.symm)
      (fun x hx y hy => hcomm x (h0 ▸ hx) y (h2 ▸ hy))
  have hD' : (diagTorus2 K).map (θ.comp (blockSL K 3 2 1 (by omega))) =
      (diagTorus2 K).map (θ₀.comp (blockSL K 3 2 0 (by omega))) := by
    rw [← map_D23, ← map_D12]
    exact hD
  have hαD : (diagTorus2 K).map α.toMonoidHom ≤ diagTorus2 K := by
    rintro _ ⟨d, hd, rfl⟩
    have hmem : (θ.comp (blockSL K 3 2 1 (by omega))) d ∈
        (diagTorus2 K).map (θ₀.comp (blockSL K 3 2 0 (by omega))) := hD' ▸ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', hd'eq⟩ := hmem
    have hαd : α d = d' := hm₂ ((hα d).trans hd'eq.symm)
    simpa [hαd] using hd'
  obtain ⟨β, hβ0, hβ1⟩ := exists_extend hK α hαD
  have hB12 : (B12 K).map β.toMonoidHom = B12 K := by
    ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨α A, (hβ0 A).symm⟩
    · rintro ⟨A, rfl⟩
      refine ⟨blockSL K 3 2 0 (by omega) (α.symm A), ⟨_, rfl⟩, ?_⟩
      show β (blockSL K 3 2 0 (by omega) (α.symm A)) = _
      rw [hβ0, MulEquiv.apply_symm_apply]
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · rw [map_comp_mulEquiv, hB12, h1']
  · rw [map_comp_mulEquiv, hβ1, h2]
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (blockSL K 3 2 0 (by omega) A)) = θ (blockSL K 3 2 1 (by omega) A)
    rw [hβ0, hα]

end Adjust

section Chain

variable {K : Type} [Field K] {X : Type} [Group X]

@[expose] def ChainGood (V : ℕ → Subgroup X) (θ : ℕ → SL(3, K) →* X) (i : ℕ) : Prop :=
  (θ i).ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map (θ i) = V i ∧
    (B23 K).map (θ i) = V (i + 1) ∧
    ∀ j, i = j + 1 → (θ i).comp (blockSL K 3 2 0 (by omega)) =
      (θ j).comp (blockSL K 3 2 1 (by omega))

theorem ChainGood.update {V : ℕ → Subgroup X} {θ : ℕ → SL(3, K) →* X} {i k : ℕ}
    (h : ChainGood V θ i) (hik : i < k) (θ' : SL(3, K) →* X) :
    ChainGood V (Function.update θ k θ') i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hne : i ≠ k := by omega
  refine ⟨by rwa [Function.update_of_ne hne], by rwa [Function.update_of_ne hne],
    by rwa [Function.update_of_ne hne], fun j hj => ?_⟩
  have hjk : j ≠ k := by omega
  rw [Function.update_of_ne hne, Function.update_of_ne hjk]
  exact h4 j hj

variable [Finite K]

theorem exists_chain (hK : 4 ≤ Nat.card K) (N : ℕ) (V : ℕ → Subgroup X)
    (θ₀ : ℕ → SL(3, K) →* X)
    (h₀ : ∀ i < N, (θ₀ i).ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map (θ₀ i) = V i ∧
      (B23 K).map (θ₀ i) = V (i + 1))
    (hcomm : ∀ i, i + 2 ≤ N → ∀ x ∈ V i, ∀ y ∈ V (i + 2), x * y = y * x) :
    ∃ θ : ℕ → SL(3, K) →* X, ∀ i < N, ChainGood V θ i := by
  have key : ∀ k, k ≤ N → ∃ θ : ℕ → SL(3, K) →* X, ∀ i < k, ChainGood V θ i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => 1, fun i hi => absurd hi (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨θ, hθ⟩ := ih (by omega)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · obtain ⟨a, b, c⟩ := h₀ 0 (by omega)
        refine ⟨Function.update θ 0 (θ₀ 0), fun i hi => ?_⟩
        obtain rfl : i = 0 := by omega
        exact ⟨by simpa using a, by simpa using b, by simpa using c, fun j hj => by omega⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        obtain ⟨hk1, hk2, hk3, -⟩ := hθ j (by omega)
        obtain ⟨a, b, c⟩ := h₀ (j + 1) (by omega)
        obtain ⟨θ', h1, h2, h3, h4⟩ := exists_adjust hK hk1 a hk2 hk3 b c
          (hcomm j (by omega))
        refine ⟨Function.update θ (j + 1) θ', fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (hθ i hlt).update hlt θ'
        · refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, fun j' hj' => ?_⟩
          have hjj : j' = j := by omega
          subst hjj
          simp only [Function.update_self, Function.update_of_ne (show j' ≠ j' + 1 by omega)]
          exact h4
  exact (key N le_rfl).imp fun θ hθ i hi => hθ i hi

end Chain

section Family

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_ctFamily_of_pairs (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 2 ≤ n)
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j)) :
    ∃ F : CTFamily K X n, ∀ i, (F.ι i).range = U i ∧ Function.Injective (F.ι i) := by
  classical
  let V : ℕ → Subgroup X := fun i => if h : i < n then U ⟨i, h⟩ else ⊥
  have hV : ∀ (i : ℕ) (h : i < n), V i = U ⟨i, h⟩ := fun i h => dite_eq_left h
  have hpair : ∀ i : ℕ, ∃ θ₀ : SL(3, K) →* X, i + 1 < n →
      (θ₀.ker ≤ Subgroup.center SL(3, K) ∧ (B12 K).map θ₀ = V i ∧
        (B23 K).map θ₀ = V (i + 1)) := by
    intro i
    by_cases h : i + 1 < n
    · obtain ⟨W, hWpair⟩ := hpair ⟨i, by omega⟩ ⟨i + 1, h⟩ rfl
      obtain ⟨θ₀, -, h1, h2, h3⟩ := pair_normalize hWpair
      exact ⟨θ₀, fun _ => ⟨h1, by rw [hV i (by omega)]; exact h2, by rw [hV _ h]; exact h3⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose θ₀ hθ₀ using hpair
  obtain ⟨θ, hθ⟩ := exists_chain hK (n - 1) V θ₀ (fun i hi => hθ₀ i (by omega))
    (fun i hi x hx y hy => by
      rw [hV i (by omega)] at hx
      rw [hV (i + 2) (by omega)] at hy
      exact hcomm ⟨i, by omega⟩ ⟨i + 2, by omega⟩ (by simp) x hx y hy)
  let ι : Fin n → (SL(2, K) →* X) := fun i =>
    if h : (i : ℕ) + 1 < n then (θ i).comp (blockSL K 3 2 0 (by omega))
    else (θ ((i : ℕ) - 1)).comp (blockSL K 3 2 1 (by omega))
  have hι_pos : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      ι i = (θ i).comp (blockSL K 3 2 0 (by omega)) := fun i h => dite_eq_left h
  have hι_neg : ∀ (i : Fin n), ¬ (i : ℕ) + 1 < n →
      ι i = (θ ((i : ℕ) - 1)).comp (blockSL K 3 2 1 (by omega)) := fun i h => dite_eq_right h
  have hrange_inj : ∀ i : Fin n, (ι i).range = U i ∧ Function.Injective (ι i) := by
    intro i
    by_cases h : (i : ℕ) + 1 < n
    · obtain ⟨g1, g2, -, -⟩ := hθ i (by omega)
      rw [hι_pos i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B12 K).map (θ i) = U i := by rw [g2, hV i i.2]
      exact this
    · have hi : (i : ℕ) - 1 + 1 = i := by have := i.2; omega
      obtain ⟨g1, -, g3, -⟩ := hθ ((i : ℕ) - 1) (by have := i.2; omega)
      rw [hι_neg i h]
      refine ⟨?_, comp_blockSL_injective g1 _ (by omega)⟩
      rw [MonoidHom.range_comp]
      have : (B23 K).map (θ ((i : ℕ) - 1)) = U i := by
        rw [g3, hi, hV i i.2]
      exact this
  refine ⟨{ ι := ι, θ := fun i => θ i, left := ?_, right := ?_, comm := ?_ }, hrange_inj⟩
  · intro i h
    exact (hι_pos i h).symm
  · intro i h
    by_cases h2 : (i : ℕ) + 2 < n
    · rw [hι_pos ⟨i + 1, h⟩ h2]
      exact ((hθ (i + 1) (by omega)).2.2.2 i rfl).symm
    · rw [hι_neg ⟨i + 1, h⟩ h2]
      simp
  · intro i j hij a b
    have ha : ι i a ∈ U i := (hrange_inj i).1 ▸ ⟨a, rfl⟩
    have hb : ι j b ∈ U j := (hrange_inj j).1 ▸ ⟨b, rfl⟩
    exact hcomm i j hij _ ha _ hb

theorem exists_ctFamily (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 2 ≤ n) {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakCTSystem K n U W) :
    ∃ F : CTFamily K X n, ∀ i, (F.ι i).range = U i ∧ Function.Injective (F.ι i) :=
  exists_ctFamily_of_pairs hK hn hW.comm fun i j hj => ⟨_, hW.pair i j hj⟩

end Family

end CFSG.ClassicalInvolution.WeakCT
