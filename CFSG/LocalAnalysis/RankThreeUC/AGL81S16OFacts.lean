module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UnitCase
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure O6LocalFacts (p n : ℕ) (M L V : Subgroup G) (sing : G → Prop) : Prop where
  card_V : Nat.card ↥V = 2 ^ (6 * n)
  nonsing_good : ∀ v ∈ V, v ≠ 1 → ¬ sing v →
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G))
  p_dvd : ∀ v ∈ V, v ≠ 1 → p ∣ Nat.card ↥(M ⊓ centralizer ({v} : Set G))
  ts_index : ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → sing w) →
    2 ^ (4 * n) ≤ W.relIndex V
  ts_equal : ∀ W : Subgroup G, W ≤ V → (∀ w ∈ W, w ≠ 1 → sing w) →
    W.relIndex V = 2 ^ (4 * n) → 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (W : Set G))
  transvection : ∀ t ∈ M, IsPGroup 2 ↥(zpowers t) → t ∉ centralizer (V : Set G) →
    (V ⊓ centralizer ({t} : Set G)).relIndex V < 2 ^ (2 * n) →
    ∀ v ∈ V, ⁅t, v⁆ ≠ 1 → ¬ sing ⁅t, v⁆
  outer_nonsing : ∀ a ∈ M, a ^ 2 = 1 → a ∉ L ⊔ (M ⊓ centralizer (V : Set G)) →
    ∃ v ∈ V, ⁅a, v⁆ ≠ 1 ∧ ¬ sing ⁅a, v⁆
  outer_rank : ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
    ¬ A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
    (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A ≤ 2 ^ (3 * n + 1)
  parabolic : ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
    ∃ P R : Subgroup G, P ≤ L ∧ R ≤ T ∧ 2 ≤ CFSG.Open.pRank p P ∧
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
        (∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
          V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) →
        A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) → ∀ a ∈ A, ∀ x ∈ P, ⁅x, a⁆ ∈ R

omit [Finite G] in
theorem centralizer_le_normalizer_subgroup (U : Subgroup G) :
    centralizer (U : Set G) ≤ normalizer (U : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  have h1 : ∀ z ∈ U, x * z * x⁻¹ = z := fun z hz => by
    have := mem_centralizer_iff.mp hx z hz
    rw [← this]
    simp
  have h2 : ∀ z ∈ U, x⁻¹ * z * x = z := fun z hz => by
    have := mem_centralizer_iff.mp hx z hz
    rw [mul_assoc, this]
    simp
  constructor
  · intro hy
    rw [h1 y hy]
    exact hy
  · intro hy
    have := h2 _ hy
    rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
    exact this ▸ hy

theorem LocalSetting.hr_strict_of_facts {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop}
    (hp : p.Prime) (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : O6LocalFacts p n M L V sing) :
    ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ M → 2 ^ (4 * n) < U.relIndex V := by
  intro U hUV hUM
  have hts : ∀ w ∈ U, w ≠ 1 → sing w := by
    intro w hw hw1
    by_contra hns
    apply hUM
    have hcw := hS.centralizer_le_of_good hp (hUV hw) hw1 (hF.nonsing_good w (hUV hw) hw1 hns)
    exact le_trans (centralizer_le (Set.singleton_subset_iff.mpr hw)) hcw
  refine lt_of_le_of_ne (hF.ts_index U hUV hts) fun heq => ?_
  have hU1 : U ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left, hF.card_V] at heq
    have := Nat.pow_right_injective (le_refl 2) heq
    omega
  have hN : normalizer (U : Set G) ≤ M :=
    hS.u2 U hU1 ((elementary_isPGroup 2 V hS.elemAbelian).to_le hUV) (hF.ts_equal U hUV hts heq.symm)
  exact hUM (le_trans (centralizer_le_normalizer_subgroup U) hN)

end CFSG.LocalAnalysis.RankThreeUC
