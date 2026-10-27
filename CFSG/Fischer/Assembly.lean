module

public import CFSG.Sporadic.Fi22.Uniqueness
public import CFSG.Sporadic.Fi22.FischerOpen
public import CFSG.Sporadic.Fi23.Uniqueness
public import CFSG.Sporadic.Fi23.FischerOpen
public import CFSG.Sporadic.Fi24.Fischer
public import CFSG.Sporadic.Fi24.FischerOpen
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Facts

variable {tr cs : Set (Set Sporadic.Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
  (hfix22 : ∀ g : Sporadic.Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Sporadic.Fi22.D // g * (x : Sporadic.Fi22.J) * g⁻¹ = x} ∈
      ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Sporadic.Fi22.D) (σ : Equiv.Perm Sporadic.Fi22.D),
    (∀ g : Sporadic.Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Sporadic.Fi22.pair_D g = Pair.conjPerm Sporadic.Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Sporadic.Fi22.pair_D (χ : Sporadic.Fi22.J))
  {d1 t2 : Sporadic.Fi23.J} (hd1 : d1 ∈ LocalClass Sporadic.Fi23.D23 Sporadic.Fi23.d)
  (hcover : ∀ g : Sporadic.Fi23.J, g ^ 2 = 1 → g ≠ 1 →
    IsConj Sporadic.Fi23.d g ∨ IsConj (Sporadic.Fi23.d * d1) g ∨ IsConj t2 g)

include hTF hfix22 hcent22 hd1 hcover in
theorem full_of_facts :
    ∀ k : Fin 3, Subgroup.center (Carrier k) = ⊥ ∧ IsSimpleGroup (commutator (Carrier k)) ∧
      ∃ D : Set (Carrier k), HasType k (Carrier k) D ∧
        (∀ E : Set (Carrier k), Pair (Carrier k) E → E = D) ∧ LocalStructure k D ∧
        ∀ (X : Type) [Group X] (E : Set X), Pair X E →
          Subgroup.center X = ⊥ → IsSimpleGroup (commutator X) → HasType k X E →
          ∃ iso : X ≃* Carrier k, iso '' E = D := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  intro k
  match k with
  | 0 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi22.existence_carrier
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi22.fischer_uniqueness_zero polarFacts X E hP hZ hS hT⟩
  | 1 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi23.existence_carrier
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi23.fischer_uniqueness_one polarFacts hyperovalFacts hFF X E hP hZ hS hT⟩
  | 2 =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Sporadic.Fi24.existence_carrier polarFacts hyperovalFacts hFF
      hTF hfix22 hcent22 Sporadic.Fi24.edgeSwap_a hd1 hcover
    exact ⟨h1, h2, _, h3, h4, h5, fun X _ E hP hZ hS hT =>
      Sporadic.Fi24.fischer_uniqueness_two polarFacts hyperovalFacts hFF hTF hfix22 hcent22
        Sporadic.Fi24.edgeSwap_a hd1 hcover X E hP hZ hS hT⟩

include hTF in
theorem open_of_facts :
    ∀ k ∈ ({22, 23, 24} : Set ℕ),
      (∃ (G : Type) (_ : Group G) (_ : Finite G) (D : Set G),
        fischerEUIsCenterlessPair D ∧ fischerEUType k D ∧
        (∀ D' : Set G, fischerEUIsPair D' → D' = D) ∧
        ∀ d ∈ D, fischerEULocalStructure k d) ∧
      (∀ (G H : Type) [Group G] [Group H] [Finite G] [Finite H] (D : Set G) (E : Set H),
        fischerEUIsCenterlessPair D → fischerEUType k D →
        fischerEUIsCenterlessPair E → fischerEUType k E →
        ∃ φ : G ≃* H, φ '' D = E) := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  intro k hk
  rcases hk with rfl | rfl | rfl
  · refine ⟨Sporadic.Fi22.open_existence_22, fun G H _ _ _ _ D E hD hDT hE hET => ?_⟩
    obtain ⟨-, hDT'⟩ | ⟨h, -⟩ | ⟨h, -⟩ := hDT
    · obtain ⟨-, hET'⟩ | ⟨h, -⟩ | ⟨h, -⟩ := hET
      · exact Sporadic.Fi22.open_uniqueness_22 polarFacts G H D E hD hDT' hE hET'
      all_goals exact absurd h (by decide)
    all_goals exact absurd h (by decide)
  · refine ⟨Sporadic.Fi23.open_existence_23, fun G H _ _ _ _ D E hD hDT hE hET => ?_⟩
    obtain ⟨h, -⟩ | ⟨-, hDT'⟩ | ⟨h, -⟩ := hDT
    · exact absurd h (by decide)
    · obtain ⟨h, -⟩ | ⟨-, hET'⟩ | ⟨h, -⟩ := hET
      · exact absurd h (by decide)
      · exact Sporadic.Fi23.open_uniqueness_23 polarFacts hyperovalFacts hFF G H D E hD hDT' hE
          hET'
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · refine ⟨Sporadic.Fi24.open_existence_24 polarFacts,
      fun G H _ _ _ _ D E hD hDT hE hET => ?_⟩
    obtain ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hDT'⟩ := hDT
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · obtain ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hET'⟩ := hET
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact Sporadic.Fi24.open_uniqueness_24 polarFacts hyperovalFacts hFF hTF G H D E hD hDT'
          hE hET'

end Facts

end CFSG.Fischer
