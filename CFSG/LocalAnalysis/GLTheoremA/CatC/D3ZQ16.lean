module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ14

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Roots

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem degLayerRoots_J2 {d : ℤ} (hd : 1 ≤ d) :
    degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) d =
      ↑((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ =>
        0 < height v ∧ v 0 + v 1 + v 3 = d) := by
  have e1 : degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) d =
      ↑((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ =>
        0 < height v ∧ d ≤ v 0 + v 1 + v 3) := degSet_J2 hd
  have e2 : degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) (d + 1) =
      ↑((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ =>
        0 < height v ∧ d + 1 ≤ v 0 + v 1 + v 3) := degSet_J2 (by omega : 1 ≤ d + 1)
  unfold degLayerRoots
  rw [e1, e2]
  ext v
  simp only [Set.mem_diff, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hne
    exact h4 ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, by omega⟩, fun h => by have := h.2.2; omega⟩

@[expose] def cntRoots (d : ℤ) (p : (Fin Tag.D4.rank → ℤ) → Prop) [DecidablePred p] : ℕ :=
  ((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ =>
    0 < height v ∧ v 0 + v 1 + v 3 = d ∧ p v).card

@[expose] def parE (β₀ β₁ β₃ : ℤ) (v : Fin Tag.D4.rank → ℤ) : Prop :=
  (β₀ * v 0 + β₁ * v 1 + β₃ * v 3) % 2 = 0

instance (β₀ β₁ β₃ : ℤ) : DecidablePred (parE β₀ β₁ β₃) := fun v =>
  inferInstanceAs (Decidable ((β₀ * v 0 + β₁ * v 1 + β₃ * v 3) % 2 = 0))

theorem sign_combin (β₀ β₁ β₃ γ₀ γ₁ γ₃ : ℤ) (hβ₀ : β₀ = 0 ∨ β₀ = 1) (hβ₁ : β₁ = 0 ∨ β₁ = 1)
    (hβ₃ : β₃ = 0 ∨ β₃ = 1) (hγ₀ : γ₀ = 0 ∨ γ₀ = 1) (hγ₁ : γ₁ = 0 ∨ γ₁ = 1)
    (hγ₃ : γ₃ = 0 ∨ γ₃ = 1)
    (h1 : cntRoots 1 (parE β₀ β₁ β₃) = cntRoots 1 (parE γ₀ γ₁ γ₃))
    (h2 : cntRoots 1 (parE γ₀ γ₁ γ₃) = cntRoots 1 (parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃)))
    (hne : ¬(β₀ = 0 ∧ β₁ = 0 ∧ β₃ = 0)) :
    cntRoots 1 (fun v => parE β₀ β₁ β₃ v ∧ parE γ₀ γ₁ γ₃ v) = 0 ∧
      cntRoots 2 (fun v => parE β₀ β₁ β₃ v ∧ parE γ₀ γ₁ γ₃ v) = 0 := by
  rcases hβ₀ with rfl | rfl <;> rcases hβ₁ with rfl | rfl <;> rcases hβ₃ with rfl | rfl <;>
    rcases hγ₀ with rfl | rfl <;> rcases hγ₁ with rfl | rfl <;> rcases hγ₃ with rfl | rfl <;>
    revert h1 h2 hne <;> decide +kernel

theorem card_subtype_layer_eq {Δ : Set (Fin Tag.D4.rank → ℤ)} {s : Finset (Fin Tag.D4.rank → ℤ)}
    (hΔ : Δ = ↑s) (p : (Fin Tag.D4.rank → ℤ) → Prop) [DecidablePred p] :
    Nat.card {i : Δ // p i.1} = (s.filter p).card := by
  subst hΔ
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  exact
    { toFun := fun i => ⟨i.1.1, Finset.mem_filter.2 ⟨i.1.2, i.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.1 x.2).1⟩, (Finset.mem_filter.1 x.2).2⟩
      left_inv := fun i => rfl
      right_inv := fun x => rfl }

theorem card_subtype_layer_J2 {d : ℤ} (hd : 1 ≤ d) (p : (Fin Tag.D4.rank → ℤ) → Prop)
    [DecidablePred p] :
    Nat.card {i : degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) d // p i.1} =
      cntRoots d p := by
  rw [card_subtype_layer_eq (degLayerRoots_J2 hd) p, cntRoots, Finset.filter_filter]
  congr 1

end Roots

section Signs

variable {K : Type} [Field K]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem rootChar_J2 (b : Fin Tag.D4.rank → Kˣ) (h2 : b 2 = 1) (v : Fin Tag.D4.rank → ℤ) :
    rootChar b v = b 0 ^ v 0 * b 1 ^ v 1 * b 3 ^ v 3 := by
  unfold rootChar
  have h : (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [h2, mul_assoc]

theorem zpow_sign {u : Kˣ} {β : ℤ} (h : (β = 0 ∧ u = 1) ∨ (β = 1 ∧ u = -1)) (m : ℤ) :
    u ^ m = (-1 : Kˣ) ^ (β * m) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp
  · simp

theorem rootChar_signs (b : Fin Tag.D4.rank → Kˣ) (h2 : b 2 = 1) {β₀ β₁ β₃ : ℤ}
    (h0 : (β₀ = 0 ∧ b 0 = 1) ∨ (β₀ = 1 ∧ b 0 = -1))
    (h1 : (β₁ = 0 ∧ b 1 = 1) ∨ (β₁ = 1 ∧ b 1 = -1))
    (h3 : (β₃ = 0 ∧ b 3 = 1) ∨ (β₃ = 1 ∧ b 3 = -1)) (v : Fin Tag.D4.rank → ℤ) :
    rootChar b v = (-1 : Kˣ) ^ (β₀ * v 0 + β₁ * v 1 + β₃ * v 3) := by
  rw [rootChar_J2 b h2, zpow_sign h0, zpow_sign h1, zpow_sign h3, _root_.zpow_add, _root_.zpow_add]

theorem neg_one_zpow_eq_one_iff (hK2 : ringChar K ≠ 2) (n : ℤ) :
    (-1 : Kˣ) ^ n = 1 ↔ n % 2 = 0 := by
  rcases Int.even_or_odd n with he | ho
  · rw [he.neg_one_zpow]
    simp only [true_iff]
    exact Int.even_iff.1 he
  · rw [ho.neg_one_zpow]
    have hne : (-1 : Kˣ) ≠ 1 := fun h => Ring.neg_one_ne_one_of_char_ne_two hK2
      (by simpa using congrArg (fun u : Kˣ => (u : K)) h)
    have : n % 2 = 1 := Int.odd_iff.1 ho
    simp only [hne, false_iff]
    omega

theorem neg_one_zpow_eq_neg_one {n : ℤ} (h : n % 2 ≠ 0) : (-1 : Kˣ) ^ n = -1 := by
  have : Odd n := Int.odd_iff.2 (by omega)
  exact this.neg_one_zpow

theorem rootChar_one_or_neg_one (b : Fin Tag.D4.rank → Kˣ) (h2 : b 2 = 1) {β₀ β₁ β₃ : ℤ}
    (h0 : (β₀ = 0 ∧ b 0 = 1) ∨ (β₀ = 1 ∧ b 0 = -1))
    (h1 : (β₁ = 0 ∧ b 1 = 1) ∨ (β₁ = 1 ∧ b 1 = -1))
    (h3 : (β₃ = 0 ∧ b 3 = 1) ∨ (β₃ = 1 ∧ b 3 = -1)) (hK2 : ringChar K ≠ 2)
    (v : Fin Tag.D4.rank → ℤ) :
    (parE β₀ β₁ β₃ v ∧ ((rootChar b v : Kˣ) : K) = 1) ∨
      (¬ parE β₀ β₁ β₃ v ∧ ((rootChar b v : Kˣ) : K) = -1) := by
  rw [rootChar_signs b h2 h0 h1 h3 v]
  by_cases hp : parE β₀ β₁ β₃ v
  · left
    refine ⟨hp, ?_⟩
    have := (neg_one_zpow_eq_one_iff hK2 _).2 hp
    rw [this]; simp
  · right
    refine ⟨hp, ?_⟩
    have := neg_one_zpow_eq_neg_one (K := K) hp
    rw [this]; simp

@[expose] def uTorus (μ : Kˣ) : Fin Tag.D4.rank → Kˣ := fun i => if i = 2 then 1 else μ

theorem uTorus_two (μ : Kˣ) : uTorus μ 2 = 1 := by simp [uTorus]

theorem rootChar_uTorus (μ : Kˣ) (v : Fin Tag.D4.rank → ℤ) :
    rootChar (uTorus μ) v = μ ^ (v 0 + v 1 + v 3) := by
  rw [rootChar_J2 _ (uTorus_two μ)]
  have e0 : uTorus μ 0 = μ := by simp [uTorus]
  have e1 : uTorus μ 1 = μ := by simp [uTorus]
  have e3 : uTorus μ 3 = μ := by simp [uTorus]
  rw [e0, e1, e3, _root_.zpow_add, _root_.zpow_add]

end Signs

end CFSG.LocalAnalysis.GLTheoremA
