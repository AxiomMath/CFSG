module

public import CFSG.RankThree.PartOne.KD4L.TranspositionLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDDatum4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRecog

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem rationalLieType_of_equiv {G G' : Type} [Group G] [Group G'] {ℓ : ℕ} {R : Subgroup G}
    {C : Subgroup G'} (e : ↥R ≃* ↥C) (h : RationalLieType ℓ C) : RationalLieType ℓ R := by
  let g : (↥R ⧸ Subgroup.center ↥R) ≃* (↥C ⧸ Subgroup.center ↥C) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨isChevSimple_congr g.symm h.1, ⟨fun f => h.2.false (g.symm.trans f)⟩⟩

theorem rationalLieType_map_conj {G : Type} [Group G] {ℓ : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : RationalLieType ℓ R) : RationalLieType ℓ (R.map φ.toMonoidHom) :=
  rationalLieType_of_equiv (R.equivMapOfInjective φ.toMonoidHom φ.injective).symm h

namespace CompsPD4Tau


@[expose] def bTau : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 1 1, Pi.single 3 1, Pi.single 2 1, Pi.single 4 1]

theorem iform_bTau (j k : Fin 4) :
    iform (bTau j) (bTau k) = CFSG.LieType.Universal.Spin.cartanD 4 j k := by
  fin_cases j <;> fin_cases k <;>
    simp [bTau, iform_single_single_E6', cartanD_apply] <;> decide

theorem bTau_root (j : Fin 4) : IsRoot Tag.E6 (bTau j) := by
  fin_cases j <;> exact isRoot_single _ _

theorem bTau_injective : Function.Injective bTau := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first
    | rfl
    | (exfalso
       simp only [bTau] at h
       exact (single_ne_single (by decide)) h)

theorem exists_frame_E6 {L : Type} [Field L] {i k : Fin Tag.E6.rank}
    (hE : (nodeIdx (some i), nodeIdx (some k)) ∈ e6EdgeIdx) :
    ∃ θ : SL(3, L) →* ModGL Tag.E6 L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 Tag.E6 L (Pi.single i 1) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 Tag.E6 L (Pi.single k 1) := by
  obtain ⟨ρ, σ, hρ, h01, h12⟩ := e6_frames (L := L) (some i) (some k) hE
  obtain ⟨θ, h0, h1⟩ := exists_normalized_a2Frame hρ
  rw [kacE6_extRoot] at h01 h12
  exact ⟨θ, by rw [h0, h01]; rfl, by rw [h1, h12]; rfl⟩

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

theorem theta_single_tau {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) :
    (tauDatum L ℓ f hf).θ (toReal (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
      toReal (Pi.single (gam j) 1 : Fin Tag.E6.rank → ℤ) := by
  have hK : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots d4Gen.χ := by
    rw [kernelRoots_d4Gen]
    exact single_mem_parabolicRoots hj
  change d4Gen.θ _ = _
  rw [d4Gen_theta_toReal hK, permLattice_gam_single]

include hf in
theorem twoDChainRecog_four (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    CompsPTwoDDatumG.TwoDChainRecog ℓ L f 4 := by
  by_cases h2 : ℓ = 2
  · subst h2
    exact CompsPTwoDChainE.twoDChainRecog_even hf le_rfl
  · exact CompsPTwoDRecog.twoDChainRecog_odd h2 hf le_rfl (hq.resolve_left h2)

include hf in
theorem rationalLieType_tauDatum (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    RationalLieType ℓ (tauDatum L ℓ f hf).orbitGroup := by
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
  refine CompsPTwoDDatum4.rationalLieType_of_datum_four (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (twoDChainRecog_four hf hq) bTau bTau_root
    bTau_injective iform_bTau ?_ ?_ ?_ ?_ ?_
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
theorem rationalLieType_fixE6_dN (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    RationalLieType ℓ (fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact rationalLieType_tauDatum hf hq

include hf in
theorem exists_fix_swap13_RL (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      RationalLieType ℓ (fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, rationalLieType_fixE6_dN hf hq⟩

include hf in
theorem exists_fix_swap03_RL (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      RationalLieType ℓ (fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact rationalLieType_map_conj _ (rationalLieType_fixE6_dN hf hq)

include hf in
theorem exists_fix_swap01_RL (hq : ℓ = 2 ∨ 5 ≤ ℓ ^ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      RationalLieType ℓ (fixE6 ℓ f n₂) := by
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
    exact rationalLieType_map_conj _ (rationalLieType_fixE6_dN hf hq)

end CompsPD4Tau

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
