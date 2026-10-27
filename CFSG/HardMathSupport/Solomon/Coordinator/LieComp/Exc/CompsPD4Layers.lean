module

public import CFSG.RankThree.PartOne.KD4L.TrialityEquiv
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Tau
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTriD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFourLayer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPD4Layers

section Generic

variable {τ : Tag} {L : Type} [Field L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem nonempty_equiv_stdLayer {n₁ n h : ModGL τ L} (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Nonempty (↥P ≃* ↥(stdLayer ℓ f n₁)) := by
  have hmem : ∀ g : ModGL τ L, g ∈ P ↔ h * g * h⁻¹ ∈ stdLayer ℓ f n₁ := fun g => by
    rw [hP, Subgroup.mem_inf, mem_stdLayer, mem_twistedFixedPoints, hlang g]
    refine and_congr_left fun _ => ⟨fun hg => mul_mem (mul_mem hh hg) (inv_mem hh), fun hg => ?_⟩
    have := mul_mem (mul_mem (inv_mem hh) hg) hh
    simpa [mul_assoc] using this
  exact ⟨{ toFun := fun g => ⟨h * g * h⁻¹, (hmem g).1 g.2⟩
           invFun := fun u => ⟨h⁻¹ * u * h, (hmem _).2 (by simp [mul_assoc])⟩
           left_inv := fun g => Subtype.ext (by simp [mul_assoc])
           right_inv := fun u => Subtype.ext (by simp [mul_assoc])
           map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }⟩

end Generic

theorem rationalLieType_of_chevSimple_center_bot {G : Type} [Group G] {ℓ : ℕ} {R : Subgroup G}
    (hZ : Subgroup.center ↥R = ⊥) (h1 : IsChevSimple ℓ ↥R)
    (h2 : IsEmpty (↥R ≃* alternatingGroup (Fin 6))) : RationalLieType ℓ R := by
  let e : (↥R ⧸ Subgroup.center ↥R) ≃* ↥R :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨isChevSimple_congr e.symm h1, ⟨fun f => h2.false (e.symm.trans f)⟩⟩

section Std

variable {τ : Tag} [hτ : E6Sub τ]
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem rationalLieType_layer_swap {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ)
    (h₂ : Acts n₂ σ) (hRL : RationalLieType ℓ (fixE6 ℓ f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    RationalLieType ℓ P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact rationalLieType_of_equiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)) hRL

theorem rationalLieType_layer_triality {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    RationalLieType ℓ P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  obtain ⟨h1, h2⟩ := isChevSimple_graphFixedRootGroup_cubic_exc (Fact.out : ℓ.Prime) hf K hKc σ
    hstd.he hσ
  exact rationalLieType_of_equiv eP
    (rationalLieType_of_chevSimple_center_bot (center_graphFixedRootGroup_eq_bot σ.surjective) h1
      h2)

@[expose] def D4SwapLayerRL (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    (ℓ = 2 ∨ 5 ≤ ℓ ^ f) →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      RationalLieType ℓ P

@[expose] def D4TrialityLayerRL (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      RationalLieType ℓ P

theorem swapLayerRL_generic (hf : 1 ≤ f) (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f)
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

theorem trialityLayerRL_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    RationalLieType ℓ P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact rationalLieType_layer_triality hf hstd hh hlang hP

end Std

section OfLeaf

variable {τ : Tag} [E6Sub τ]

theorem d4SwapLayerRL_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerRL τ := by
  intro L _ _ ℓ f _ _ hf hq i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerRL_generic hf hq (Equiv.swap 1 3) (CompsPD4Tau.exists_fix_swap13_RL hf hq)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerRL_generic hf hq (Equiv.swap 0 3) (CompsPD4Tau.exists_fix_swap03_RL hf hq)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerRL_generic hf hq (Equiv.swap 0 1) (CompsPD4Tau.exists_fix_swap01_RL hf hq)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

theorem d4TrialityLayerRL_of_leafCycle
    (hleaf : ∀ a b c : Fin τ.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
      b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
      a ≠ b → b ≠ c → a ≠ c →
      ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
        (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧
          ((List.formPerm [a, b, c]).symm i).val ≤ 4))) :
    D4TrialityLayerRL τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact trialityLayerRL_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact trialityLayerRL_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

end OfLeaf

section Tags


theorem d4SwapLayerRL_E6 : D4SwapLayerRL .E6 := d4SwapLayerRL_of_leafSwap leafSwap_E6
theorem d4SwapLayerRL_E7 : D4SwapLayerRL .E7 := d4SwapLayerRL_of_leafSwap leafSwap_E7
theorem d4SwapLayerRL_E8 : D4SwapLayerRL .E8 := d4SwapLayerRL_of_leafSwap leafSwap_E8
theorem d4TrialityLayerRL_E6 : D4TrialityLayerRL .E6 := d4TrialityLayerRL_of_leafCycle leafCycle_E6
theorem d4TrialityLayerRL_E7 : D4TrialityLayerRL .E7 := d4TrialityLayerRL_of_leafCycle leafCycle_E7
theorem d4TrialityLayerRL_E8 : D4TrialityLayerRL .E8 := d4TrialityLayerRL_of_leafCycle leafCycle_E8

end Tags

end CompsPD4Layers

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
