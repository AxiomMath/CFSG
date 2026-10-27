module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Layers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TauAll

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups
open CompsPD4Layers

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPD4LayersAll

section Std

variable {τ : Tag} [hτ : E6Sub τ]
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def D4SwapLayerRLAll (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      RationalLieType ℓ P


theorem swapLayerRLAll_generic (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      RationalLieType ℓ (fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    RationalLieType ℓ P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact rationalLieType_layer_swap hstd h₂ hRL hh hlang hP


end Std

section OfLeaf

variable {τ : Tag} [E6Sub τ]

theorem d4SwapLayerRLAll_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerRLAll τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerRLAll_generic hf (Equiv.swap 1 3) (CompsPD4TauAll.exists_fix_swap13_RL_all hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerRLAll_generic hf (Equiv.swap 0 3) (CompsPD4TauAll.exists_fix_swap03_RL_all hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerRLAll_generic hf (Equiv.swap 0 1) (CompsPD4TauAll.exists_fix_swap01_RL_all hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

end OfLeaf

section Tags


theorem d4SwapLayerRLAll_E6 : D4SwapLayerRLAll .E6 := d4SwapLayerRLAll_of_leafSwap leafSwap_E6
theorem d4SwapLayerRLAll_E7 : D4SwapLayerRLAll .E7 := d4SwapLayerRLAll_of_leafSwap leafSwap_E7
theorem d4SwapLayerRLAll_E8 : D4SwapLayerRLAll .E8 := d4SwapLayerRLAll_of_leafSwap leafSwap_E8

end Tags

end CompsPD4LayersAll

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
