module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLeviHom
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.EPilot
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)


section Hom

variable (K : Type) [Field K] [Finite K] [CharP K 2]

noncomputable def d6Order : CommOrder (SpinPlus.Φ 6 K three_le_rank_D6) :=
  Classical.choice (SpinPlus.conclusionB (K := K) three_le_rank_D6).2.1

@[expose] noncomputable def spinToE7 : spinGroup (quadPlus 6 K) →* ↥(adjointGroup .E7 K) :=
  liftOfPresentationB (SpinPlus.presentationB three_le_rank_D6) (d6Order K)
    (SpinPlus.commutatorFormula three_le_rank_D6 (d6Order K)) (fun γ _ c d => d6LeviPar_add γ c d)
    (commutatorFormula_d6LeviPar (d6Order K))

variable {K}

theorem spinToE7_x {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    spinToE7 K (SpinPlus.x 6 K three_le_rank_D6 γ c) = d6LeviPar K γ c :=
  liftOfPresentationB_apply _ _ _ _ _ hγ c

theorem coe_spinToE7_x {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    ((spinToE7 K (SpinPlus.x 6 K three_le_rank_D6 γ c) : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K (d6Embed γ) c := by
  rw [spinToE7_x hγ]
  rfl

omit [Finite K] [CharP K 2]
  in
theorem closure_spinX_eq_top :
    closure {g : spinGroup (quadPlus 6 K) | ∃ γ ∈ roots (isFiniteType_cartanD 6) ∅, ∃ c : K,
      SpinPlus.x 6 K three_le_rank_D6 γ c = g} = ⊤ := by
  rw [eq_top_iff, ← CFSG.LieType.Universal.Spin.plusDatum_iSup_eq_top 6 K three_le_rank_D6]
  refine iSup₂_le fun γ hγ g hg => ?_
  obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (K := K) three_le_rank_D6 γ hγ).1 g).1 hg
  exact subset_closure ⟨γ, hγ, c, rfl⟩

theorem range_spinToE7 : (spinToE7 K).range = perpLevi .E7 K := by
  rw [MonoidHom.range_eq_map, ← closure_spinX_eq_top, MonoidHom.map_closure,
    perpLevi_E7_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, (spinToE7_x hγ c).symm⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨_, ⟨γ, hγ, c, rfl⟩, spinToE7_x hγ c⟩

theorem spinToE7_mem_perpLevi (g : spinGroup (quadPlus 6 K)) :
    spinToE7 K g ∈ perpLevi .E7 K := by
  rw [← range_spinToE7]
  exact ⟨g, rfl⟩

theorem exists_spinToE7_ne_one : ∃ g, spinToE7 K g ≠ 1 := by
  have hr : (Pi.single 0 1 : Fin 6 → ℤ) ∈ roots (isFiniteType_cartanD 6) ∅ :=
    (SpinPlus.Φ 6 K three_le_rank_D6).single_mem 0
  refine ⟨SpinPlus.x 6 K three_le_rank_D6 (Pi.single 0 1) 1, fun h => ?_⟩
  rw [spinToE7_x hr, ← d6LeviPar_zero (Pi.single 0 1)] at h
  exact one_ne_zero (d6LeviPar_injective _ h)

end Hom

theorem center_spinGroup_quadPlus_eq_bot (K : Type) [Field K] [CharP K 2] :
    center (spinGroup (quadPlus 6 K)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := CFSG.LieType.Universal.Spin.spinToStatedProj_quadPlus (n := 6) (K := K)
    three_le_rank_D6
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot
    three_le_rank_D6 CharTwo.two_eq_zero

section Equiv

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spinToE7_injective : Function.Injective (spinToE7 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_spinGroup_quadPlus_eq_bot K]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D6)
    exists_spinToE7_ne_one

variable (K) in
@[expose] noncomputable def spinEquivPerpLevi : spinGroup (quadPlus 6 K) ≃* ↥(perpLevi .E7 K) :=
  (MonoidHom.ofInjective spinToE7_injective).trans (MulEquiv.subgroupCongr range_spinToE7)

theorem coe_spinEquivPerpLevi (g : spinGroup (quadPlus 6 K)) :
    ((spinEquivPerpLevi K g : perpLevi .E7 K) : adjointGroup .E7 K) = spinToE7 K g :=
  rfl

theorem spinEquivPerpLevi_x {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅)
    (c : K) :
    spinEquivPerpLevi K (SpinPlus.x 6 K three_le_rank_D6 γ c) =
      ⟨d6LeviPar K γ c, d6LeviPar_mem_perpLevi hγ c⟩ :=
  Subtype.ext (spinToE7_x hγ c)

theorem isQuasisimple_perpLevi_E7 : CFSG.IsQuasisimple (perpLevi .E7 K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (spinEquivPerpLevi K)
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D6)

theorem center_perpLevi_E7_eq_bot : center (perpLevi .E7 K) = ⊥ := by
  rw [← Subgroup.map_center_eq (spinEquivPerpLevi K), center_spinGroup_quadPlus_eq_bot K,
    Subgroup.map_bot]

theorem isQuasisimple_open_perpLevi_E7 : CFSG.Open.IsQuasisimple (perpLevi .E7 K) :=
  ⟨isQuasisimple_perpLevi_E7.1.commutator_eq_top, isQuasisimple_perpLevi_E7.2.1⟩

theorem isSimpleGroup_perpLevi_E7 : IsSimpleGroup (perpLevi .E7 K) := by
  have hq := isQuasisimple_perpLevi_E7 (K := K)
  have hZ := center_perpLevi_E7_eq_bot (K := K)
  have e : perpLevi .E7 K ⧸ center (perpLevi .E7 K) ≃* perpLevi .E7 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact @MulEquiv.isSimpleGroup _ _ _ _ hq.2.1 e.symm

theorem lieModel_perpLevi_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    LieModel (perpLevi .E7 K) .POmegaPlus 6 2 f := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hZ := center_spinGroup_quadPlus_eq_bot K
  have e : spinGroup (quadPlus 6 K) ⧸ center (spinGroup (quadPlus 6 K)) ≃* perpLevi .E7 K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (spinEquivPerpLevi K)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
    (Or.inl ⟨by decide, CFSG.LieType.Universal.Spin.statedClassicalModel_spin_quadPlus
      ⟨Nat.prime_two, hf, by norm_num⟩ hK⟩)

theorem lieModel_perpLevi_E7_quotient_center {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    LieModel (perpLevi .E7 K ⧸ center (perpLevi .E7 K)) .POmegaPlus 6 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq center_perpLevi_E7_eq_bot).trans
      QuotientGroup.quotientBot).symm (lieModel_perpLevi_E7 hK)

end Equiv

end CFSG.SeitzReduction.E7Pilot
