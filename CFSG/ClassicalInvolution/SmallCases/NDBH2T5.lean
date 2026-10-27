module

public import CFSG.ClassicalInvolution.SmallCases.NDBH2T4

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem c3_conj {K : Subgroup G} (hΩ : ConjInvariant (𝒞 K)) {x : G}
    (h : ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l → l ≠ x → l * x = x * l →
      L ∈ tqMembers (𝒞 K) x) (g : G) :
    ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l → l ≠ g * x * g⁻¹ →
      l * (g * x * g⁻¹) = g * x * g⁻¹ * l → L ∈ tqMembers (𝒞 K) (g * x * g⁻¹) := by
  intro L hL l hl hlx hcomm
  rw [tqMembers_conj hΩ]
  refine ⟨conjSub g⁻¹ L, h _ ?_ (g⁻¹ * l * g) ?_ ?_ ?_, conjSub_conjSub_inv g L⟩
  · obtain ⟨k, rfl⟩ := hL
    exact ⟨g⁻¹ * k, conjSub_mul _ _ _⟩
  · have h1 := hl.conj g⁻¹
    rwa [inv_inv] at h1
  · intro e
    apply hlx
    rw [← e]
    group
  · calc g⁻¹ * l * g * x = g⁻¹ * (l * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * l) * g := by rw [hcomm]
      _ = x * (g⁻¹ * l * g) := by group

end NDBH2

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NarrowTriangle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        ¬ HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, ∀ n' : G, IsClassicalMember p f N' n' →
          n' ≠ z → modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) →
          (∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
            (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
            oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) →
          (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
            modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
              modOdd z (exactCore z M) = modOdd z (exactCore z N')) → False

@[expose] def TriangleA2Partner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        ¬ HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, ∀ n' : G, IsClassicalMember p f N' n' →
          n' ≠ z → modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) →
          (∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
            (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
            oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) →
          (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
            modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
              modOdd z (exactCore z M) = modOdd z (exactCore z N')) →
          (∃ x ∈ ({z, n, n'} : Set G), ∃ L ∈ 𝒞 K, ∃ l : G, IsClassicalMember p f L l ∧
            l ≠ x ∧ l * x = x * l ∧ L ∉ tqMembers (𝒞 K) x) → False

variable {p f}

theorem narrowTriangle_of_noAllA1Narrow (h : NoAllA1Narrow p f) : NarrowTriangle p f :=
  fun G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz =>
    (h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz).2.1

theorem false_of_triangle_of_c3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) {N : Subgroup G}
    (hN : N ∈ tqMembers (𝒞 K) z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z)
    (hnt : ¬ HasTwin p f K z) {N' : Subgroup G} (hN' : N' ∈ tqMembers (𝒞 K) z) {n' : G}
    (hn' : IsClassicalMember p f N' n') (hn'z : n' ≠ z)
    (hne : modOdd z (exactCore z N') ≠ modOdd z (exactCore z N))
    (hprod : ∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
      (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    (hc3 : ∀ x ∈ ({z, n, n'} : Set G), ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l →
      l ≠ x → l * x = x * l → L ∈ tqMembers (𝒞 K) x) : False := by
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  have hs := NDBH2.axisSeed_of_triangle C hall' hN hN' hn hn' hnz hn'z hne hprod
  obtain ⟨K₂, K₃, z₂, z₃, R₁, R₂, R₃, P, g₂, g₃, hT, hz₂, hz₃⟩ :=
    NDBH2.exists_hTri C.hΩ hp2 hq (CoreAssembly.mem_conjClass_self K) hz hs
  refine NDBH2.false_of_hTri hnab C hno hall' hz hnt hT ?_
  intro x hx
  rcases hx with h | h | h
  · rw [h]
    exact hc3 z (Or.inl rfl)
  · rw [h, hz₂]
    exact NDBH2.c3_conj C.hΩ.conjInvariant (hc3 n (Or.inr (Or.inl rfl))) g₂
  · rw [h, hz₃]
    exact NDBH2.c3_conj C.hΩ.conjInvariant (hc3 n' (Or.inr (Or.inr rfl))) g₃

theorem triangle_false_of_residual (hR : TriangleA2Partner p f) : NarrowTriangle p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz hT N' hN' n' hn' hn'z
    hne hprod hshape
  by_cases hc3 : ∀ x ∈ ({z, n, n'} : Set G), ∀ L ∈ 𝒞 K, ∀ l : G, IsClassicalMember p f L l →
      l ≠ x → l * x = x * l → L ∈ tqMembers (𝒞 K) x
  · exact false_of_triangle_of_c3 hnab hp2 hq hz hBelow hno D hall hN hn hnz hT hN' hn' hn'z hne
      hprod hc3
  · push Not at hc3
    exact hR G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz hT N' hN' n' hn' hn'z hne
      hprod hshape hc3

end CFSG.ClassicalInvolution.NDB
