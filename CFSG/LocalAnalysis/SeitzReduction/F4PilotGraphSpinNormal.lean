module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinBetaC
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)

section Freedom

variable
  {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]

theorem conj_spinD4Graph_comp {ΦY : spinGroup (quadPlus 4 K) →* G} {t : G}
    {α δ : MulAut (spinGroup (quadPlus 4 K))}
    (hα : ∀ g, t * ΦY (α g) * t⁻¹ = ΦY (α (spinD4Graph K g)))
    (hδ : ∀ g, δ (spinD4Graph K g) = spinD4Graph K (δ g)) (g : spinGroup (quadPlus 4 K)) :
    t * ΦY ((δ.trans α) g) * t⁻¹ = ΦY ((δ.trans α) (spinD4Graph K g)) := by
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hδ, hα]

theorem conj_x_of_conj_spinD4Graph {ΦY : spinGroup (quadPlus 4 K) →* G} {t : G}
    {α : MulAut (spinGroup (quadPlus 4 K))}
    (hα : ∀ g, t * ΦY (α g) * t⁻¹ = ΦY (α (spinD4Graph K g))) :
    ∀ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∀ c : K,
      t * ΦY (α (SpinPlus.x 4 K three_le_rank_D4 γ c)) * t⁻¹ =
        ΦY (α (SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c)) := by
  intro γ hγ c
  rw [hα, spinD4Graph_x hγ]

end Freedom

section Normal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_spinD4Graph_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (h : HR8Kind e t f .X .omegaPlus8)
    {ΦY : spinGroup (quadPlus 4 K) →* G} (hrY : ΦY.range = neighbourCore e .X)
    (hiY : Function.Injective ΦY) :
    ∃ α : MulAut (spinGroup (quadPlus 4 K)), ∀ g,
      t * ΦY (α g) * t⁻¹ = ΦY (α (spinD4Graph K g)) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set Φ' : StatedOmega (StatedQuadPlus 4 K) →* G :=
    ΦY.comp (spinOmegaEquiv (K := K)).symm.toMonoidHom with hΦ'
  have hinj : Function.Injective Φ' := hiY.comp (spinOmegaEquiv (K := K)).symm.injective
  have hr' : Φ'.range = neighbourCore e .X := by
    rw [hΦ', MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (spinOmegaEquiv (K := K)).symm.surjective,
      ← MonoidHom.range_eq_map, hrY]
  have hker' : Φ'.ker ≤ center (StatedOmega (StatedQuadPlus 4 K)) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ').2 hinj]
    exact bot_le
  have : Group.IsPerfect (StatedOmega (StatedQuadPlus 4 K)) := isPerfect_omegaPlus8 K
  have : Finite (StatedOmega (StatedQuadPlus 4 K)) := Finite.of_injective Φ' hinj
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ := exists_graphLift_of_closed_X hw hf e
    (κ := .omegaPlus8) (by decide) (by decide) h
    (fun E' _ _ π' hπ' hc => omegaPlus8_exists_section K hK4 E' π' hπ' hc) Φ' hr' hker'
  obtain ⟨Ψ, hΨ⟩ := exists_conj_omegaPlusBetaC K hw.one_le hw.card_eq β hβ2 hβo hβfix
  refine ⟨((spinOmegaEquiv (K := K)).trans Ψ).trans (spinOmegaEquiv (K := K)).symm, fun g => ?_⟩
  have e1 : ∀ x, ΦY ((spinOmegaEquiv (K := K)).symm x) = Φ' x := fun _ => rfl
  simp only [MulEquiv.trans_apply]
  rw [e1, e1, ← hβ, hΨ, spinOmegaEquiv_spinD4Graph_eq_omegaPlusBetaC]

theorem exists_conj_spinD4Graph {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .omegaPlus8) {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N) (hiY : Function.Injective ΦY) :
    ∃ α : MulAut (spinGroup (quadPlus 4 K)), ∀ g,
      t * ΦY (α g) * t⁻¹ = ΦY (α (spinD4Graph K g)) := by
  cases N with
  | X => exact exists_conj_spinD4Graph_X hw hf e h hrY hiY
  | Y =>
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    exact exists_conj_spinD4Graph_X hw hf (e.trans (graphAutF4 K).symm)
      ((hr8Kind_Y_iff_X e).1 h) (hrY.trans (neighbourCore_Y_eq_X e)) hiY
  | X' => exact absurd rfl hN

end Normal

end CFSG.SeitzReduction.F4Pilot
