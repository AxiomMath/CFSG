module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

@[expose] def omegaOne {N : ℕ} (Δ₀ : Finset (Fin N)) (ω : Perm (Fin N)) (a : Fin N) :
    Finset (Fin N) :=
  insert a (insert (ω a) Δ₀)

@[expose] def altOn {N : ℕ} (Ω₁ : Finset (Fin N)) : Subgroup (Perm (Fin N)) :=
  alternatingGroup (Fin N) ⊓ fixingSubgroup (Perm (Fin N)) ((Ω₁ : Set (Fin N))ᶜ)

@[expose] def subL {G : Type} [Group G] {N : ℕ} (S L : Subgroup G)
    (θ : ↥(L ⊔ S) →* Perm (Fin N)) (Ω₁ : Finset (Fin N)) : Subgroup G :=
  perfectCore (L ⊓ ((altOn Ω₁).comap θ).map (L ⊔ S).subtype)

structure E0Data {N : ℕ} (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N)))
    (ω : Perm (Fin N)) : Prop where
  six_le : 6 ≤ N
  card_Δ₀ : Δ₀.card = 4
  card_P : Nat.card P = 4
  P_sq : ∀ p ∈ P, p * p = 1
  P_fix : ∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i
  P_trans : ∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j
  ω_invol : ∀ x, ω (ω x) = x
  ω_fix : ∀ x ∈ Δ₀, ω x = x
  ω_free : ∀ x, x ∉ Δ₀ → ω x ≠ x

structure E0NS {G : Type} [Group G] (X S L : Subgroup G) (N : ℕ) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Δ₀ : Finset (Fin N)) (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) : Prop
    extends E0Data Δ₀ P ω where
  asc : Asc81bHyp X S
  block : IsWeakSBlock X S L
  normalizes : S ≤ Subgroup.normalizer (L : Set G)
  natural : NaturalSectionTheta S L N θ
  ker_le : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S
  image_S : (S.subgroupOf (L ⊔ S)).map θ =
    P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}

variable {N : ℕ} {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}

theorem mem_altOn_iff {Ω₁ : Finset (Fin N)} {σ : Perm (Fin N)} :
    σ ∈ altOn Ω₁ ↔ σ ∈ alternatingGroup (Fin N) ∧ ∀ x, x ∉ Ω₁ → σ x = x := by
  simp [altOn, mem_fixingSubgroup_iff]

theorem subL_le {G : Type} [Group G] (S L : Subgroup G) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (Ω₁ : Finset (Fin N)) : subL S L θ Ω₁ ≤ L :=
  (perfectCore_le _).trans inf_le_left

theorem subL_perfect {G : Type} [Group G] [Finite G] (S L : Subgroup G)
    (θ : ↥(L ⊔ S) →* Perm (Fin N)) (Ω₁ : Finset (Fin N)) :
    ⁅subL S L θ Ω₁, subL S L θ Ω₁⁆ = subL S L θ Ω₁ :=
  perfectCore_perfect _

namespace E0Data

theorem exists_not_mem (h : E0Data Δ₀ P ω) : ∃ a, a ∉ Δ₀ := by
  by_contra hcon
  push Not at hcon
  have h1 : Δ₀ = Finset.univ := Finset.eq_univ_of_forall hcon
  have h2 := h.card_Δ₀
  have h3 := h.six_le
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem ω_not_mem (h : E0Data Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀) : ω a ∉ Δ₀ := fun hω => by
  have := h.ω_fix _ hω
  rw [h.ω_invol] at this
  exact ha (this ▸ hω)

theorem ω_ne_self (h : E0Data Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀) : ω a ≠ a :=
  h.ω_free a ha

theorem card_omegaOne (h : E0Data Δ₀ P ω) {a : Fin N} (ha : a ∉ Δ₀) :
    (omegaOne Δ₀ ω a).card = 6 := by
  have h1 : ω a ∉ Δ₀ := h.ω_not_mem ha
  have h2 : a ∉ insert (ω a) Δ₀ := by
    rw [Finset.mem_insert, not_or]
    exact ⟨(h.ω_ne_self ha).symm, ha⟩
  rw [omegaOne, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1, h.card_Δ₀]

end E0Data

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
