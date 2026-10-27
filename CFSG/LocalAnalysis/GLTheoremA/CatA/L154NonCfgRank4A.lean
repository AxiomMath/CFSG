module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint (LieModel)


section Generic

@[expose] def L154R4Model (ℓ f : ℕ) (X : Type) [Group X] : Prop :=
  LieModel (X ⧸ Subgroup.center X) .POmegaMinus 4 ℓ f ∨
    LieModel (X ⧸ Subgroup.center X) .trialityD4 0 ℓ f

theorem l154r4_model_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {ℓ f : ℕ}
    (h : L154R4Model ℓ f X) : L154R4Model ℓ f Y := by
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)
  exact h.imp (fun h => h.of_mulEquiv e') (fun h => h.of_mulEquiv e')

theorem l154r4_model_map_conj {G : Type} [Group G] {ℓ f : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : L154R4Model ℓ f ↥R) : L154R4Model ℓ f ↥(R.map φ.toMonoidHom) :=
  l154r4_model_of_mulEquiv (R.equivMapOfInjective φ.toMonoidHom φ.injective) h

end Generic

section Cubic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T


theorem l154r4_lieModel_graphFixed_trialityD4 {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = (ℓ ^ d) ^ 3) (σ₀ : k ≃+* k)
    (hσ₀ : (∀ c, σ₀ c = c ^ ℓ ^ d) ∨ ∀ c, σ₀ c = c ^ (ℓ ^ d) ^ 2) :
    LieModel ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) .trialityD4 0 ℓ d := by
  rcases eq_or_ne ℓ 2 with rfl | h2
  · exact CFSG.RankThree.PartOne.Sec66T.lieModel_graphFixedRootGroup_trialityD4 hd hk σ₀ hσ₀
  · exact CFSG.ComponentClassification.CatLeafProof.lieModel_graphFixedRootGroup_trialityD4_odd
      hℓ h2 hd hk σ₀ hσ₀

theorem l154r4_model_graphFixed_cubic {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    L154R4Model ℓ f' ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e0 : (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine Or.inr ((l154r4_lieModel_graphFixed_trialityD4 hℓ hf' hK σ ?_).of_mulEquiv e0.symm)
  rcases hr with rfl | rfl
  · exact Or.inl fun c => by rw [hσ, pow_one]
  · exact Or.inr hσ

end Cubic

section TauRoots

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped Matrix MatrixGroups

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem l154r4_tau_simpleRoots : (tauDatum L ℓ f hf).simpleRootsJ = Set.range bTau := by
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

end TauRoots

section Tau

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem l154r4_model_tauDatum_all : L154R4Model ℓ f ↥(tauDatum L ℓ f hf).orbitGroup := by
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
  refine Or.inl (lieModel_orbitGroup_of_datum_four (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau
    bTau_root bTau_injective iform_bTau (l154r4_tau_simpleRoots hf) ?_ ?_ ?_ ?_)
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
theorem l154r4_model_fixE6_dN_all : L154R4Model ℓ f ↥(fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact l154r4_model_tauDatum_all hf

include hf in
theorem l154r4_exists_fix_swap13_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      L154R4Model ℓ f ↥(fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, l154r4_model_fixE6_dN_all hf⟩

include hf in
theorem l154r4_exists_fix_swap03_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      L154R4Model ℓ f ↥(fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact l154r4_model_map_conj _ (l154r4_model_fixE6_dN_all hf)

include hf in
theorem l154r4_exists_fix_swap01_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      L154R4Model ℓ f ↥(fixE6 ℓ f n₂) := by
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
    exact l154r4_model_map_conj _ (l154r4_model_fixE6_dN_all hf)

end Tau

section Std

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [hτ : E6Sub τ]
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem l154r4_model_layer_swap {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ)
    (h₂ : Acts n₂ σ) (hRL : L154R4Model ℓ f ↥(fixE6 ℓ f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    L154R4Model ℓ f ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact l154r4_model_of_mulEquiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm hRL

theorem l154r4_model_layer_triality {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    L154R4Model ℓ f ↥P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact l154r4_model_of_mulEquiv eP.symm
    (l154r4_model_graphFixed_cubic (Fact.out : ℓ.Prime) hf K hKc σ hstd.he hσ)

theorem l154r4_trialityLayer_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    L154R4Model ℓ f ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact l154r4_model_layer_triality hf hstd hh hlang hP

theorem l154r4_swapLayer_generic (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      L154R4Model ℓ f ↥(fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    L154R4Model ℓ f ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact l154r4_model_layer_swap hstd h₂ hRL hh hlang hP

end Std

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
