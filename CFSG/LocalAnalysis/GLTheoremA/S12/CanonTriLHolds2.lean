module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonTriL

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw

set_option linter.unusedSectionVars false

section D4Cubic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp


theorem notG2_graphFixedRootGroup_cubic {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    NotG2LieType ℓ ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ (ℓ ^ f')) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (ℓ ^ f') := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  have hK' : Nat.card K = (ℓ ^ f') ^ TwistTag.D4.order := hK
  obtain ⟨ψ⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4 hℓ hf' K
    hK' σ₁.toRingHom (fun c => hσ₁ c)
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e0 : (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 ℓ f' := ⟨hℓ, hf', rfl⟩
  refine ⟨.trialityD4, 0, f', by decide, Or.inr (Or.inl ⟨rfl, by decide, hadm, ?_⟩)⟩
  exact ⟨K, inferInstance, inferInstance, hK', σ₁.toRingHom, fun c => hσ₁ c,
    ⟨(e0.trans e).trans ψ.symm⟩⟩

end D4Cubic

section D4LayerDefs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def D4TrialityLayerNotG2 (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      NotG2LieType ℓ ↥P

@[expose] def D4SwapLayerNotG2 (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      NotG2LieType ℓ ↥P

end D4LayerDefs

section D4Tau

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem notG2_tauDatum :
    NotG2LieType ℓ ↥(tauDatum L ℓ f hf).orbitGroup := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine ⟨.POmegaMinus, 4, _, by decide, lieModel_orbitGroup_of_datum_four (τ := Tag.E6)
    (Or.inr (Or.inl rfl)) (tauDatum L ℓ f hf) (m := 4) le_rfl
    (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau bTau_root bTau_injective iform_bTau
    ?_ ?_ ?_ ?_ ?_⟩
  ·
    ext β
    constructor
    · intro hβ
      rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
      obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
      have hjS : j ∈ d4Support := d4Aux_support ▸ hj
      rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact single_mem_simpleRootsJ hf h1S
      · exact single_mem_simpleRootsJ hf h3S
      · exact single_mem_simpleRootsJ hf h2S
      · exact single_mem_simpleRootsJ hf h4S
  ·
    intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  ·
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

include hf in
theorem notG2_fixE6_dN :
    NotG2LieType ℓ ↥(fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact notG2_tauDatum hf

include hf in
theorem exists_fix_swap13_notG2 :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotG2LieType ℓ ↥(fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, notG2_fixE6_dN hf⟩

include hf in
theorem exists_fix_swap03_notG2 :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotG2LieType ℓ ↥(fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact NotG2LieType.map_conj _ (notG2_fixE6_dN hf)

include hf in
theorem exists_fix_swap01_notG2 :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotG2LieType ℓ ↥(fixE6 ℓ f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹,
    ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact NotG2LieType.map_conj _ (notG2_fixE6_dN hf)

end D4Tau

section D4Std

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [hτ : E6Sub τ]
variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem notG2_layer_swap {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ)
    (h₂ : Acts n₂ σ) (hRL : NotG2LieType ℓ ↥(fixE6 ℓ f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotG2LieType ℓ ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact hRL.of_mulEquiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm

theorem notG2_layer_triality {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotG2LieType ℓ ↥P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact (notG2_graphFixedRootGroup_cubic (Fact.out : ℓ.Prime) hf K hKc σ hstd.he
    hσ).of_mulEquiv eP.symm

theorem trialityLayerNotG2_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotG2LieType ℓ ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact notG2_layer_triality hf hstd hh hlang hP

theorem swapLayerNotG2_generic (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotG2LieType ℓ ↥(fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotG2LieType ℓ ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact notG2_layer_swap hstd h₂ hRL hh hlang hP

end D4Std

section D4OfLeaf

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [E6Sub τ]

theorem d4TrialityLayerNotG2_of_leafCycle
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
    D4TrialityLayerNotG2 τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact trialityLayerNotG2_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact trialityLayerNotG2_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

theorem d4SwapLayerNotG2_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerNotG2 τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerNotG2_generic hf (Equiv.swap 1 3) (exists_fix_swap13_notG2 hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerNotG2_generic hf (Equiv.swap 0 3) (exists_fix_swap03_notG2 hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerNotG2_generic hf (Equiv.swap 0 1) (exists_fix_swap01_notG2 hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

end D4OfLeaf

section D4Tags

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers


theorem d4SwapLayerNotG2_E6 : D4SwapLayerNotG2 .E6 := d4SwapLayerNotG2_of_leafSwap leafSwap_E6
theorem d4SwapLayerNotG2_E7 : D4SwapLayerNotG2 .E7 := d4SwapLayerNotG2_of_leafSwap leafSwap_E7
theorem d4SwapLayerNotG2_E8 : D4SwapLayerNotG2 .E8 := d4SwapLayerNotG2_of_leafSwap leafSwap_E8
theorem d4TrialityLayerNotG2_E6 : D4TrialityLayerNotG2 .E6 :=
  d4TrialityLayerNotG2_of_leafCycle leafCycle_E6
theorem d4TrialityLayerNotG2_E7 : D4TrialityLayerNotG2 .E7 :=
  d4TrialityLayerNotG2_of_leafCycle leafCycle_E7
theorem d4TrialityLayerNotG2_E8 : D4TrialityLayerNotG2 .E8 :=
  d4TrialityLayerNotG2_of_leafCycle leafCycle_E8

end D4Tags

section D4Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_notG2_d4_of_layer (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      NotG2LieType ℓ ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    NotG2LieType (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact NotG2LieType.map_conj (MulAut.conj nv) hP

variable {Fr : L →+* L}

theorem rootSpan_inf_model_notG2_d4_swap
    (hL : D4SwapLayerNotG2 τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α) :
    NotG2LieType (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_notG2_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

theorem rootSpan_inf_model_notG2_d4 (hL : D4TrialityLayerNotG2 τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    NotG2LieType (ringChar L)
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_notG2_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl)
    hact

end D4Transport

section D4Component

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem notG2_rationalComponent_of_d4_outer [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (hR3 : D4TrialityLayerNotG2 τ)
    (hR2 : D4SwapLayerNotG2 τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      NotG2LieType (ringChar L) ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        rootSpan_inf_model_notG2_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        rootSpan_inf_model_notG2_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        rootSpan_inf_model_notG2_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2, rootSpan_inf_model_notG2_d4 hR3 S hFr hΦ hn v hu h12 h24
          h14 hv1 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2, rootSpan_inf_model_notG2_d4 hR3 S hFr hΦ hn v hu h14
          h24.symm h12 hv1 hv4 hv2 hact⟩
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end D4Component

section D4TwLayers

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem twisted_swap_layer_notG2 (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    NotG2LieType ℓ ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun k hk => by
    have := hact _ (single_mem_parabolicRoots hk)
    rw [permLattice_single (Equiv.swap i j)] at this
    exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap13_notG2 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact notG2_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap03_notG2 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact notG2_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap01_notG2 (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact notG2_layer_swap hstd h₂ hRL hh hlang rfl

theorem twisted_triality_layer_notG2 (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    NotG2LieType ℓ ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact notG2_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact notG2_layer_triality hf hstd hh hlang rfl

end D4TwLayers

section D4TwComponent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers


theorem notG2_rationalComponent_of_d4_twE6_of_layer {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
      u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      IsD4LeafPerm π → π ≠ 1 →
      (¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      NotG2LieType ℓ ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → πJ * πJ ≠ 1 := by
    intro hnin2 h2
    apply hnin2
    have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
        exact (e6WeylTwist_simple j).symm
      exact hle ⟨u, hu, rfl⟩
    have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨e6WeylTwist u, hδu, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
    refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
        (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
      intro x hx
      rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
        inv_smul_smul]
    set β := u • permLattice πJ α with hβ
    have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
      rw [hβ, ← hθ' α hα]
      exact hθmem α hα
    have e1 : S.ρ (v • α) = v • β := by
      rw [hβ, ← hθ' α hα, smul_inv_smul]
    have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
      rw [← hθ' β hβJ, smul_inv_smul]
    have e3 : permLattice πJ (permLattice πJ α) = α := by
      rw [← permLattice_mul, h2]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer := hlay ℓ f hf hq _ hn'M u hu πJ hπJleaf hπ1 hπ2 hact
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      NotG2LieType ℓ ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    have e : Q ≃* Q.map (MulAut.conj nv).toMonoidHom :=
      Q.equivMapOfInjective _ (MulAut.conj nv).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1,
      NotG2LieType.map_conj (MulAut.conj nv) hlayer.2⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs.1, ringChar.eq L ℓ]
  exact hqs.2

end D4TwComponent

section D4Rank4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups


theorem notG2_of_rank_four {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact notG2_rationalComponent_of_d4_outer d4Base_E6
        d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) d4TrialityLayerNotG2_E6
        d4SwapLayerNotG2_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      refine notG2_rationalComponent_of_d4_twE6_of_layer S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv
        hρ hnin (fun ℓ f _ _ hf hqf n hn u hu π hleaf hπ1 _ hact => ?_)
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
          twisted_swap_layer_notG2 hf h12 hv1 hv2 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
          twisted_swap_layer_notG2 hf h14 hv1 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
          twisted_swap_layer_notG2 hf h24 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
          twisted_triality_layer_notG2 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
          twisted_triality_layer_notG2 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact notG2_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6)
      d4TrialityLayerNotG2_E7 d4SwapLayerNotG2_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact notG2_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6)
      d4TrialityLayerNotG2_E8 d4SwapLayerNotG2_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin

end D4Rank4

section Classes

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups


theorem notG2_rationalComponent_outerD {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i h5
      hshape.2 hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
    exact ⟨.POmegaMinus, m, e, by decide, hlie⟩
  · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hshape.2, hr4]
    have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    exact notG2_of_rank_four S hp hpL hT hTp h1 i hr4 hc hout

theorem notG2_rationalComponent_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact notG2_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact notG2_inner_nonA_E6 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact notG2_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

theorem notG2_rationalComponent_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E7.rank → Lˣ}
    (hT : rootDiagUnit Tag.E7 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E7 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact notG2_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact notG2_inner_nonA_E7 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact notG2_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, by decide, hlie⟩

theorem notG2_rationalComponent_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {p : ℕ} (hp : p.Prime) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E8 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact notG2_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact notG2_inner_nonA_E8 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact notG2_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, by decide, hlie⟩

theorem notG2_rationalComponent_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NotG2LieType (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  rcases hτ with rfl | rfl | rfl
  · exact notG2_rationalComponent_E6 S hp hT hap h1 i hq
  · exact notG2_rationalComponent_E7 S hp hT hap h1 i hq
  · exact notG2_rationalComponent_E8 S hp hT hap h1 i hq

end Classes

section Groups

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)



theorem false_of_G2_adjointE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut ↥(adjointGroup τ K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) {mm : ℕ}
    (hJl : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J (fun l : GLALabel => l = ⟨.G2, 0, mm⟩)) :
    False := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := exists_inndiag_of_mem_innAutDerived_E hτ hp β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := τ) (Or.inr (Or.inr hτ)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h' =>
    absurd h' (by rcases hτ with rfl | rfl | rfl <;> decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hRl := (CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_congr eJ _).1 hJl
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hNG := notG2_rationalComponent_E hτ S hp hT hap h1 i hqs
  rw [hch] at hNG
  exact false_of_notG2LieType hNG hRl

theorem false_of_G2_of_adjointEquiv {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (ψ : S ≃* ↥(adjointGroup τ K)) {β : MulAut S}
    (hβmem : β ∈ innAutDerived S) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJl : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J (fun l : GLALabel => l = ⟨.G2, 0, m⟩)) :
    False := by
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  exact false_of_G2_adjointE hτ hK2 hp hp2 hβ'mem hβ'p hβ'1 (isComponentOf_transport ψ β hJ)
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_transport ψ hJl)

theorem false_of_G2_E {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .E6 ∨ labL.tag = .E7 ∨ labL.tag = .E8) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJl : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J (fun l : GLALabel => l = ⟨.G2, 0, m⟩)) :
    False := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen
    (Or.inr (ht.imp id (Or.imp id Or.inl))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  rcases ht with rfl | rfl | rfl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E6 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    exact false_of_G2_of_adjointEquiv (Or.inl rfl) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ hJl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E7 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    exact false_of_G2_of_adjointEquiv (Or.inr (Or.inl rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ hJl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E8 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    exact false_of_G2_of_adjointEquiv (Or.inr (Or.inr rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ hJl

theorem false_of_G2_twE6 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .twE6) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJl : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J (fun l : GLALabel => l = ⟨.G2, 0, m⟩)) :
    False := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_exc hcen (Or.inr (Or.inr (Or.inr (Or.inr ht)))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedE6 0 2 n := hM
  have hn : 1 ≤ n := hLM.admissible.2.1
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let ψ : S ≃* ↥(twistedE6RootGroup K σ) :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₀).trans
      (b.trans eK)
  have hβ : MulAut.congr ψ β ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJ' := isComponentOf_transport ψ β hJ
  have hJl' := CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_transport ψ hJl
  have hpq : p ≠ q.p := hp2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
      hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hmem : MulAut.congr ψ β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβ
  obtain ⟨h, hh⟩ := hmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
    (by rw [map_pow, hh, hβ'p, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ'1 (by rw [← hh, h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
      q.exponent_pos hp hp2 hpq
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  obtain ⟨LS, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime LS hp
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      q.prime_p hp hK hpq) (fun h => absurd h (by decide)) hT hap h1
  rw [← hh] at hJ'
  obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    LS hp ι hinj hrange _ hconj hT hap h1 hTame hJ'
  let eJ : ↥(J.map ψ.toMonoidHom) ≃* ↥(rationalComponent LS.ρ LS.Γ (rootCharHom a) i) :=
    ((J.map ψ.toMonoidHom).equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hRl := (CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_congr eJ _).1 hJl'
  have hℓL : ringChar (AlgebraicClosure K) = 2 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
      (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
      (by rw [hK, ← pow_mul])
  have hNG := notG2_rationalComponent_E6 LS hp hT hap h1 i hqi
  rw [hℓL] at hNG
  exact false_of_notG2LieType hNG hRl

end Groups

section Dispatch

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)



theorem false_of_G2_S {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β)
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (hdvd : labL.n ∣ m)
    {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup β))
    (hKl : HasLabel ↥K (fun l : GLALabel => l = ⟨.G2, 0, m⟩)) : False := by
  rcases fam_cover labL with hF | hF | hF | hF | hF
  · exact false_of_G2_lin hp hp2 hcen hF hin hβp hK hKl
  · exact false_of_G2_uni hp hp2 hcen hF hin hβp hK hKl
  · rcases hF with ht | ht | ht
    · exact false_of_G2_symp hp hp2 hcen (Or.inl ht) hin hβp hK hKl
    · exact false_of_G2_symp hp hp2 hcen (Or.inr ht) hin hβp hK hKl
    · exact false_of_G2_small hcen hin hβ1 hdvd (Or.inl ht) hK hKl
  · exact false_of_G2_orth hp hp2 hcen hF hin hβp hK hKl
  · rcases hF with h | h | h | h | h | h | h | h | h | h | h
    · exact false_of_G2_E hp hp2 hcen hin hβp hβ1 (Or.inl h) hK hKl
    · exact false_of_G2_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inl h)) hK hKl
    · exact false_of_G2_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inr h)) hK hKl
    · exact false_of_G2_F4 hp hp2 hcen hin hβp hβ1 h hK hKl
    · exact false_of_G2_twE6 hp hp2 hcen hin hβp hβ1 h hK hKl
    ·
      rcases Nat.lt_or_ge labL.n 2 with hn | hn
      · have hS : HasLabel S (· = labL) :=
          CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
        have hn1 : labL.n = 1 := by
          have := (CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hS).1
          omega
        exact false_of_G2_small hcen hin hβ1 hdvd
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hn1⟩))))) hK hKl
      · exact false_of_G2_triD4 hp hp2 hcen hin hβp hβ1 h hn hK hKl
    · exact false_of_G2_small hcen hin hβ1 hdvd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hK hKl
    · exact false_of_G2_small hcen hin hβ1 hdvd (Or.inr (Or.inl h)) hK hKl
    · exact false_of_G2_small hcen hin hβ1 hdvd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hK hKl
    · exact false_of_G2_twF4 hcen hin hdvd h hKl
    · exact false_of_G2_small hcen hin hβ1 hdvd (Or.inr (Or.inr (Or.inl h))) hK hKl

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.CanonTriL

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F

section Main


theorem noG2Comp_holds : NoG2Comp := by
  intro Γ _ _ L K y labL p hp hp2 hyp hyN hyC hM hK m hKlab
  have hdvd : labL.n ∣ m :=
    CanonSubcomp.subcompField_holds Γ L K y labL ⟨.G2, 0, m⟩ p hp hp2 hyp hyN hyC hM hK hKlab
      (fun h => by simp at h)
  have hLl : HasLabel ↥L (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hM
  have hβ1 := CanonSubcomp.centerQuotAut_conjAut_ne_one hyN hyC (hasLabel_isQuasisimple hLl).1
  obtain ⟨hcen, hin, hpow, hKb, hlb⟩ :=
    CanonInn.marked_bridge hyN hyp hM hK ((labelOf_iff_hasLabel K _).1 hKlab)
  exact CanonTriL.false_of_G2_S hp hp2 hcen hin hpow hβ1 hdvd hKb hlb

end Main

end CFSG.LocalAnalysis.GLTheoremA

end
