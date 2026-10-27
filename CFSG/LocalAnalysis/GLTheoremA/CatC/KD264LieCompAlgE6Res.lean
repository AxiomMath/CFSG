module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Pred

private def NotEightKd264e6 (X : Type*) [Group X] : Prop :=
  ¬ (Nat.card (X ⧸ Subgroup.center X) = 504 ∨ Nat.card (X ⧸ Subgroup.center X) = 5515776)

private theorem notEight_of_mulEquiv_kd264e6 {X Y : Type*} [Group X] [Group Y]
    (h : NotEightKd264e6 X) (e : X ≃* Y) : NotEightKd264e6 Y := by
  have hc : Nat.card (X ⧸ Subgroup.center X) = Nat.card (Y ⧸ Subgroup.center Y) :=
    Nat.card_congr (QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
      (Subgroup.map_center_eq e)).toEquiv
  unfold NotEightKd264e6 at h ⊢
  rwa [← hc]

private theorem notEight_map_kd264e6 {G : Type} [Group G] {R : Subgroup G} (φ : G ≃* G)
    (h : NotEightKd264e6 ↥R) : NotEightKd264e6 ↥(R.map φ.toMonoidHom) :=
  notEight_of_mulEquiv_kd264e6 h (R.equivMapOfInjective φ.toMonoidHom φ.injective)

private theorem notEight_of_dvd_kd264e6 {X : Type*} [Group X]
    (h : 2 ^ 12 ∣ Nat.card (X ⧸ Subgroup.center X)) : NotEightKd264e6 X := by
  unfold NotEightKd264e6
  intro hN
  have h' : 2 ^ 12 ∣ Nat.card (X ⧸ Subgroup.center X) * 1 := by
    rw [mul_one]
    exact h
  obtain ⟨h9, -⟩ := two_pow_le_of_dvd_kd264alg (by decide) hN h'
  omega

end Pred

namespace ExcUntw

section Base

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Solomon.Coordinator.LieComp


private theorem notEight_graphFixedRootGroup_cubic_kd264e6 {f' : ℕ} (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((2 ^ f') ^ r)) :
    NotEightKd264e6 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  let q' : TauCeti.PrimePower := ⟨2, f', Nat.prime_two, hf'⟩
  have hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid := TauCeti.LieTypeIndex.valid_trialityD4 q'
  have hKq : Nat.card K = q'.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ q'.card) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one, TauCeti.PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ q'.card := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, TauCeti.PrimePower.card_def, ← pow_mul,
          show 2 ^ f' * (2 ^ f') ^ 2 = (2 ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (2 ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  obtain ⟨eCat⟩ := catEquiv_trialityD4_of_field q' hv' K hKq σ₁ hσ₁
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hcard : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      CFSG.Open.orderTrialityD4 (2 ^ f') := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q', hv'⟩
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⟨e.trans eCat.symm⟩
    change _ = CFSG.Open.orderTrialityD4 q'.card at h
    have hqc : q'.card = 2 ^ f' := TauCeti.PrimePower.card_def _
    rw [h, hqc]
  apply notEight_of_dvd_kd264e6
  have hq : Nat.card (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  rw [hq, hcard]
  unfold CFSG.Open.orderTrialityD4
  have h12 : 2 ^ 12 ∣ (2 ^ f') ^ 12 := pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 12
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h12 _) _) _

end Base

section BaseTau

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
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
private theorem lieModel_tauDatum_kd264e6 :
    LieModel (↥(tauDatum L ℓ f hf).orbitGroup ⧸ Subgroup.center ↥(tauDatum L ℓ f hf).orbitGroup)
      .POmegaMinus 4 ℓ f := by
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
  refine lieModel_orbitGroup_of_datum_four (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau
    bTau_root bTau_injective iform_bTau ?_ ?_ ?_ ?_ ?_
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
private theorem notEight_fixE6_dN_kd264e6 (h2 : ringChar L = 2) :
    NotEightKd264e6 ↥(fixE6 ℓ f (dN L)) := by
  have hℓ : ℓ = 2 := (ringChar.eq L ℓ).symm.trans h2
  subst hℓ
  rw [fixE6_dN hf]
  unfold NotEightKd264e6
  intro hN
  have hlie := lieModel_tauDatum_kd264e6 (L := L) (ℓ := 2) hf
  have hne : Nat.card (↥(tauDatum L 2 f hf).orbitGroup ⧸
      Subgroup.center ↥(tauDatum L 2 f hf).orbitGroup) ≠ 0 := by
    rcases hN with h | h <;> rw [h] <;> norm_num
  haveI : Finite (↥(tauDatum L 2 f hf).orbitGroup ⧸
      Subgroup.center ↥(tauDatum L 2 f hf).orbitGroup) := Nat.finite_of_card_ne_zero hne
  exact not_card_compAlgEight_of_lieModel_POmegaMinus_kd264alg hlie hN

include hf in
private theorem exists_fix_swap13_notEight_kd264e6 (h2 : ringChar L = 2) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotEightKd264e6 ↥(fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, notEight_fixE6_dN_kd264e6 hf h2⟩

include hf in
private theorem exists_fix_swap03_notEight_kd264e6 (h2 : ringChar L = 2) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotEightKd264e6 ↥(fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact notEight_map_kd264e6 _ (notEight_fixE6_dN_kd264e6 hf h2)

include hf in
private theorem exists_fix_swap01_notEight_kd264e6 (h2 : ringChar L = 2) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotEightKd264e6 ↥(fixE6 ℓ f n₂) := by
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
    exact notEight_map_kd264e6 _ (notEight_fixE6_dN_kd264e6 hf h2)

end BaseTau

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
variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

private theorem notEight_layer_swap_kd264e6 {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ)
    (h₂ : Acts n₂ σ) (hRL : NotEightKd264e6 ↥(fixE6 ℓ f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotEightKd264e6 ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact notEight_of_mulEquiv_kd264e6 hRL (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm

private theorem notEight_layer_triality_kd264e6 (h2 : ringChar L = 2) {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotEightKd264e6 ↥P := by
  have hℓ : ℓ = 2 := (ringChar.eq L ℓ).symm.trans h2
  subst hℓ
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact notEight_of_mulEquiv_kd264e6
    (notEight_graphFixedRootGroup_cubic_kd264e6 hf K hKc σ hstd.he hσ) eP.symm

private theorem trialityLayerNotEight_generic_kd264e6 (h2 : ringChar L = 2) (hf : 1 ≤ f)
    (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotEightKd264e6 ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact notEight_layer_triality_kd264e6 h2 hf hstd hh hlang hP

private theorem swapLayerNotEight_generic_kd264e6 (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      NotEightKd264e6 ↥(fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    NotEightKd264e6 ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact notEight_layer_swap_kd264e6 hstd h₂ hRL hh hlang hP

end Std

section Tags

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups


private theorem d4TrialityLayerNotEight_E6_kd264e6 (L : Type) [Field L] [IsAlgClosed L]
    (h2 : ringChar L = 2) (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (a b c : Fin Tag.E6.rank) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6),
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) :
    NotEightKd264e6 ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2'
  · exact trialityLayerNotEight_generic_kd264e6 h2 hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact _ rfl
  · exact trialityLayerNotEight_generic_kd264e6 h2 hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2'
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact _ rfl

private theorem d4SwapLayerNotEight_E6_kd264e6 (L : Type) [Field L] [IsAlgClosed L]
    (h2 : ringChar L = 2) (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (i j : Fin Tag.E6.rank) (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6),
      ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) :
    NotEightKd264e6 ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi' hj' hij
  rcases hcases with h1 | h2' | h3
  · exact swapLayerNotEight_generic_kd264e6 hf (Equiv.swap 1 3)
      (exists_fix_swap13_notEight_kd264e6 hf h2)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact _ rfl
  · exact swapLayerNotEight_generic_kd264e6 hf (Equiv.swap 0 3)
      (exists_fix_swap03_notEight_kd264e6 hf h2)
      (Equiv.swap i j) h2' (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact _ rfl
  · exact swapLayerNotEight_generic_kd264e6 hf (Equiv.swap 0 1)
      (exists_fix_swap01_notEight_kd264e6 hf h2)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact _ rfl

end Tags

section Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem rootSpan_inf_model_notEight_d4_of_layer_kd264e6 (S : LangSetup Tag.E6 L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (v : WeylGroup Tag.E6) {u : WeylGroup Tag.E6}
    (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)) {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L), n ∈ adjointGroup Tag.E6 L →
      (∃ u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6),
        ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
          weylQuotientHom Tag.E6 L ⟨n, hn⟩ • α = u • permLattice π α) →
      NotEightKd264e6 ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    NotEightKd264e6
      ↥(rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  have hmodel : rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
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
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact notEight_map_kd264e6 (MulAut.conj nv) hP

end Transport

section Component

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem notEight_rationalComponent_of_d4_outer_kd264e6 (h2 : ringChar L = 2)
    (S : LangSetup Tag.E6 L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    NotEightKd264e6 ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hE6 := e6FixDNAll_proved
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  have hlin0 : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), w₀ • α = permLattice π α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set Tag.E6)
        (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
      rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hswap : ∀ {i' j' : Fin Tag.E6.rank}, i' ≠ j' → i'.val ∈ ({1, 2, 4} : Set ℕ) →
      j'.val ∈ ({1, 2, 4} : Set ℕ) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i' j') α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) ∧
        NotEightKd264e6 ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) := by
    intro i' j' hij hi hj hact'
    rw [hΨ]
    exact ⟨(rootSpan_inf_model_quasisimple_d4_swap (d4SwapLayer_E6 hE6) S hFr hΦ hn v hu hij hi
      hj hact').2,
      rootSpan_inf_model_notEight_d4_of_layer_kd264e6 S hFr hΦ hn v hu
        (fun ℓ f _ _ hf _ n hn' _ hex =>
          d4SwapLayerNotEight_E6_kd264e6 L h2 ℓ f hf i' j' hij hi hj n hn' hex) hact'⟩
  have htri : ∀ {a' b' c' : Fin Tag.E6.rank}, a' ≠ b' → b' ≠ c' → a' ≠ c' →
      a'.val ∈ ({1, 2, 4} : Set ℕ) → b'.val ∈ ({1, 2, 4} : Set ℕ) →
      c'.val ∈ ({1, 2, 4} : Set ℕ) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a', b', c']) α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) ∧
        NotEightKd264e6 ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) := by
    intro a' b' c' hab hbc hac ha hb hc hact'
    rw [hΨ]
    exact ⟨(rootSpan_inf_model_quasisimple_d4 d4TrialityLayer_E6 S hFr hΦ hn v hu hab hbc hac ha
      hb hc hact').2,
      rootSpan_inf_model_notEight_d4_of_layer_kd264e6 S hFr hΦ hn v hu
        (fun ℓ f _ _ hf _ n hn' _ hex =>
          d4TrialityLayerNotEight_E6_kd264e6 L h2 ℓ f hf a' b' c' hab hbc hac ha hb hc n hn' hex)
        hact'⟩
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) ∧
      NotEightKd264e6 ↥(rootSpan Tag.E6 L Ψ ⊓ S.D.model) := by
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact hswap h12 hv1 hv2 hact
    · exact hswap h14 hv1 hv4 hact
    · exact hswap h24 hv2 hv4 hact
    · exact htri h12 h24 h14 hv1 hv2 hv4 hact
    · exact htri h14 h24.symm h12 hv1 hv4 hv2 hact
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end Component

end ExcUntw

section Kac

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

private theorem kc_single24_kd264e6 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 24 →
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 := by
  decide +kernel


private theorem kernelRoots_subset_of_ncard24_kd264e6 {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i := by
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
  have hcnt := ncard_kernelRoots_eq_cntB hζ w hchar
  have h24 := kc_single24_kd264e6 m0 m1 m2 m3 m4 m5 hsum x hx (hncard.symm.trans hc)
  have hk : (kernelRoots (rootCharHom a)).ncard = 24 := hcnt.trans h24
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  exact (Set.eq_of_subset_of_ncard_le hle (by rw [hk, hc]) hfin).ge

end Kac

section Main

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6D4OuterNotEight_holds :
    E6D4OuterNotEight := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i hr hc hnin _
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3L facts_E6 kacCount_E6_four
    (by decide) (by decide)
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
  ·
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    exact ExcUntw.notEight_rationalComponent_of_d4_outer_kd264e6 (ringChar.eq L 2) S hFr hΦ' hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
  ·
    rw [hs, Function.iterate_one] at hnin
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq : S.D.q = 2 ^ 3 := by rw [hq8]; norm_num
    have hall := kernelRoots_subset_of_ncard24_kd264e6 h3L hap i hc
    obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv S ⟨t, ht, Fr, hFr, hΦ⟩
      (ℓ := 2) (f := 3) (by norm_num) hq (by norm_num) hT hap i v hv hall hρ hnin
    haveI := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.finite_rationalComponent S a i
    have hcard : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =
        CFSG.Open.orderTrialityD4 (2 ^ 3) := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds _ _ ⟨e⟩
      change _ = CFSG.Open.orderTrialityD4 (TauCeti.PrimePower.card _) at h
      rw [h, TauCeti.PrimePower.card_def]
    have hquot : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) =
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
    have hdvd : 2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      rw [hquot, hcard]
      unfold CFSG.Open.orderTrialityD4
      have h12 : 2 ^ 12 ∣ (2 ^ 3) ^ 12 := pow_dvd_pow_of_dvd (dvd_pow_self 2 (by norm_num)) 12
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h12 _) _) _
    exact notEight_of_dvd_kd264e6 hdvd

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
