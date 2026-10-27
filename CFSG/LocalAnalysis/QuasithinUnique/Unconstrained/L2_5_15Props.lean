module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def IsL33OrM11 (X : Type) [Group X] : Prop :=
  StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)

section FiniteFacts

variable {G : Type} [Group G]

@[expose] def threeCoreCent (K : Subgroup G) (u : G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ K ∧ g * u = u * g ∧ g ^ 3 = 1}

theorem threeCoreCent_le (K : Subgroup G) (u : G) : threeCoreCent K u ≤ K := by
  rw [threeCoreCent, Subgroup.closure_le]
  exact fun g hg => hg.1

theorem threeCoreCent_comm {K : Subgroup G} {u v : G} (hv : v ∈ threeCoreCent K u) :
    v * u = u * v := by
  have : threeCoreCent K u ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [threeCoreCent, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr hg.2.1
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hv)

structure K33InvFacts (K : Subgroup G) (u : G) : Prop where
  mem : u ∈ threeCoreCent K u
  center : ∀ w ∈ threeCoreCent K u, (∀ v ∈ threeCoreCent K u, v * w = w * v) → w = 1 ∨ w = u
  centralizer : ∀ b ∈ K, (∀ v ∈ threeCoreCent K u, b * v = v * b) → b = 1 ∨ b = u
  aut : ∀ P : Subgroup (MulAut ↥(threeCoreCent K u)), IsPGroup 2 P → Nat.card P ≤ 8

structure K33Facts (K : Subgroup G) : Prop where
  card : Nat.card ↥K = 5616 ∨ Nat.card ↥K = 7920
  rank : ∃ E : Subgroup G, E ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9
  inv : ∀ u ∈ K, u ≠ 1 → u ^ 2 = 1 → K33InvFacts K u

@[expose] def K33LocalFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsL33OrM11 ↥K → K33Facts K

@[expose] def IsAutPair (K A : Subgroup G) : Prop :=
  K ≤ A ∧ Nat.card ↥A = 2 * Nat.card ↥K ∧ A ⊓ Subgroup.centralizer (K : Set G) = ⊥

structure L33Facts (K : Subgroup G) : Prop where
  aut_card : Nat.card (MulAut ↥K) ≤ 2 * Nat.card ↥K
  inv_class : ∀ a ∈ K, ∀ b ∈ K, a ≠ 1 → b ≠ 1 → a ^ 2 = 1 → b ^ 2 = 1 →
    ∃ k ∈ K, k⁻¹ * a * k = b
  z4 : ∀ u ∈ K, u ≠ 1 → u ^ 2 = 1 → ∀ y ∈ Subgroup.normalizer (K : Set G),
    (∀ v ∈ threeCoreCent K u, y * v = v * y) → ¬ Ch1.InducesInner y K →
      ∀ w ∈ K, (y * y)⁻¹ * w * (y * y) = u⁻¹ * w * u
  outer_inv : ∀ A : Subgroup G, IsAutPair K A → ∀ f ∈ A, ∀ f' ∈ A, f ∉ K → f' ∉ K →
    f ^ 2 = 1 → f' ^ 2 = 1 → ∃ a ∈ A, a⁻¹ * f * a = f'
  e8_conj : ∀ A : Subgroup G, IsAutPair K A → ∀ F F' : Subgroup G, F ≤ A → F' ≤ A →
    CFSG.Assembly.IsElemAbelian 2 F → Nat.card F = 8 → CFSG.Assembly.IsElemAbelian 2 F' →
    Nat.card F' = 8 → ∃ a ∈ A, CFSG.conjugate F a = F'
  e8_exists : ∀ A : Subgroup G, IsAutPair K A → ∀ E : Subgroup G, E ≤ K → IsFourSubgroup E →
    ∃ F : Subgroup G, F ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 F ∧ Nat.card F = 8 ∧ E ≤ F ∧
      F ⊓ K = E ∧ A ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G)

@[expose] def L33AutFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), StatedClassicalModel ↥K .PSL 3 3 1 →
    L33Facts K

end FiniteFacts

end CFSG.QuasithinUnique
