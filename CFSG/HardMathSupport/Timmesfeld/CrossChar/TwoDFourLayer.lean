module

public import CFSG.RankThree.PartOne.KD4L.TranspositionLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints d4Nodes)


set_option linter.unusedSectionVars false


@[expose] def E6FixDNAll : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (f : ℕ), 1 ≤ f →
    E6Fix (ℓ := ℓ) f (dN L)

theorem e6FixDNAll_proved : E6FixDNAll :=
  fun _ _ _ _ _ _ _ hf => E6Fix_dN hf

theorem leafSwap_E6 : ∀ i j : Fin Tag.E6.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
    (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
    ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
    (∀ x : Fin Tag.E6.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
    (∀ x : Fin Tag.E6.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4)) := by
  decide +kernel

@[expose] def D4SwapLayer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      Finite P ∧ CFSG.IsQuasisimple P

theorem d4SwapLayer_E8 (_hE6 : E6FixDNAll) : D4SwapLayer .E8 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  obtain ⟨hfin, hqs, -, -⟩ :=
    transposition_layer_of_leafSwap leafSwap_E8 hf hij hi hj n hn hact P hP
  exact ⟨hfin, hqs⟩

theorem d4SwapLayer_E7 (_hE6 : E6FixDNAll) : D4SwapLayer .E7 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  obtain ⟨hfin, hqs, -, -⟩ :=
    transposition_layer_of_leafSwap leafSwap_E7 hf hij hi hj n hn hact P hP
  exact ⟨hfin, hqs⟩

theorem d4SwapLayer_E6 (_hE6 : E6FixDNAll) : D4SwapLayer .E6 := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  obtain ⟨hfin, hqs, -, -⟩ :=
    transposition_layer_of_leafSwap leafSwap_E6 hf hij hi hj n hn hact P hP
  exact ⟨hfin, hqs⟩

section Twisted

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem twisted_swap_layer (_hE6 : E6FixDNAll) (hf : 1 ≤ f) {i j : Fin TwistTag.E6.tag.rank}
    (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    Finite ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun k hk => by
      have := hact _ (single_mem_parabolicRoots hk)
      rw [permLattice_single (Equiv.swap i j)] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap13 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    obtain ⟨hfin, hqs, -, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs⟩
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap03 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    obtain ⟨hfin, hqs, -, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs⟩
  · obtain ⟨n₂, h₂, hfix⟩ := exists_fix_swap01 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    obtain ⟨hfin, hqs, -, -⟩ := layer_of_swap hstd h₂ (by decide) hfix hh hlang rfl
    exact ⟨hfin, hqs⟩

theorem twisted_swap_layer_E6 (hE6 : E6FixDNAll) (hf : 1 ≤ f) {i j : Fin Tag.E6.rank}
    (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
        u • permLattice (Equiv.swap i j) α) :
    Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  twisted_swap_layer hE6 hf hij hi hj hn hu hact

end Twisted

end CFSG.HardMathSupport.Timmesfeld.CrossChar
