module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Abstract

variable {X : Type*} [Group X]

theorem conj_mul_mulAut_mul_conj_inv (η : MulAut X) (g : X) :
    MulAut.conj g * η * (MulAut.conj g)⁻¹ = MulAut.conj (g * (η g)⁻¹) * η := by
  have h1 : η * MulAut.conj g⁻¹ = MulAut.conj (η g⁻¹) * η := by
    rw [← mulAut_conj_conj_eq η g⁻¹, inv_mul_cancel_right]
  rw [← map_inv, mul_assoc, h1, ← mul_assoc, ← map_mul, map_inv]

theorem conj_conj_mul_eta {η : MulAut X} {j : X} (hj : η j = j) (x : X) :
    MulAut.conj (j * x * j⁻¹) * η = MulAut.conj j * (MulAut.conj x * η) * (MulAut.conj j)⁻¹ := by
  have h := mulAut_mul_conj_of_apply_eq hj
  rw [map_mul, map_mul, map_inv]
  calc MulAut.conj j * MulAut.conj x * (MulAut.conj j)⁻¹ * η =
        MulAut.conj j * MulAut.conj x * ((MulAut.conj j)⁻¹ * η * MulAut.conj j) *
          (MulAut.conj j)⁻¹ := by group
    _ = MulAut.conj j * (MulAut.conj x * η) * (MulAut.conj j)⁻¹ := by
        rw [show (MulAut.conj j)⁻¹ * η * MulAut.conj j = η by rw [mul_assoc, h]; group]
        group

theorem exists_add_apply_eq {K : Type*} [Field K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {e : K} (he : σ e ≠ e) {c : K} (hc : σ c = c) :
    ∃ d : K, d + σ d = c := by
  have hd0 : e + σ e ≠ 0 := fun h => he (CharTwo.add_eq_zero.mp h).symm
  have hσd : σ (e + σ e) = e + σ e := by rw [map_add, hσσ, add_comm]
  refine ⟨c * (e / (e + σ e)), ?_⟩
  rw [map_mul, hc, map_div₀, hσd, ← mul_add, ← add_div, div_self hd0, mul_one]

end Abstract

section Rows


variable {K : Type} [Field K]

theorem conj_pinnedX_mul_eta_E6 (h2 : (2 : K) = 0) {η : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    MulAut.conj (⟨pinnedX TwistTag.E6.tag K β c, pinnedX_mem_adjointGroup β c⟩ :
        adjointGroup TwistTag.E6.tag K) * η *
      (MulAut.conj (⟨pinnedX TwistTag.E6.tag K β c, pinnedX_mem_adjointGroup β c⟩ :
        adjointGroup TwistTag.E6.tag K))⁻¹ =
    MulAut.conj (⟨pinnedX TwistTag.E6.tag K β c *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) c,
      mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ :
        adjointGroup TwistTag.E6.tag K) * η := by
  have key : (⟨pinnedX TwistTag.E6.tag K β c, pinnedX_mem_adjointGroup β c⟩ :
      adjointGroup TwistTag.E6.tag K) *
        (η ⟨pinnedX TwistTag.E6.tag K β c, pinnedX_mem_adjointGroup β c⟩)⁻¹ =
      ⟨pinnedX TwistTag.E6.tag K β c * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) c,
        mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ := by
    apply Subtype.ext
    have hneg : ∀ a : K, -a = a := fun a => by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hη, ← twistHom_id_eq, twistHom_id_pinnedX h2 hβ,
      pinnedX_neg, hneg]
  rw [conj_mul_mulAut_mul_conj_inv, key]

theorem conj_twistedE6PairX_mul_eta [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K σ, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (d : K) :
    MulAut.conj (⟨twistedE6PairX σ β d, twistedE6PairX_mem_graphFixedRootGroup hσσ hβ d⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) * η *
      (MulAut.conj (⟨twistedE6PairX σ β d, twistedE6PairX_mem_graphFixedRootGroup hσσ hβ d⟩ :
        graphFixedRootGroup TwistTag.E6 K σ))⁻¹ =
    MulAut.conj (⟨twistedE6PairX σ β (d + σ d),
      twistedE6PairX_mem_graphFixedRootGroup hσσ hβ (d + σ d)⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) * η := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hρβ := hβ.permLattice TwistTag.E6.cartan_perm
  suffices key : (⟨twistedE6PairX σ β d, twistedE6PairX_mem_graphFixedRootGroup hσσ hβ d⟩ :
      graphFixedRootGroup TwistTag.E6 K σ) *
        (η ⟨twistedE6PairX σ β d, twistedE6PairX_mem_graphFixedRootGroup hσσ hβ d⟩)⁻¹ =
      ⟨twistedE6PairX σ β (d + σ d), twistedE6PairX_mem_graphFixedRootGroup hσσ hβ (d + σ d)⟩ by
    rw [conj_mul_mulAut_mul_conj_inv, key]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hη, ← twistHom_id_eq]
  simp only [twistedE6PairX]
  rw [map_mul, twistHom_id_pinnedX h2 hβ, twistHom_id_pinnedX h2 hρβ,
    permLattice_twistedE6_perm_perm, map_add, hσσ]
  have hc : ∀ a b : K, Commute (pinnedX TwistTag.E6.tag K β a)
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) b) := fun a b =>
    commute_pinnedX_permLattice_twistedE6 hβ a b
  have hneg : ∀ a : K, -a = a := fun a => by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
  rw [mul_inv_rev, pinnedX_neg, pinnedX_neg, hneg, hneg]
  calc pinnedX TwistTag.E6.tag K β d * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β)
        (σ d) * (pinnedX TwistTag.E6.tag K β (σ d) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) d) =
      pinnedX TwistTag.E6.tag K β d * (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β)
        (σ d) * pinnedX TwistTag.E6.tag K β (σ d)) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) d := by group
    _ = pinnedX TwistTag.E6.tag K β d * (pinnedX TwistTag.E6.tag K β (σ d) *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ d)) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) d := by
        rw [(hc (σ d) (σ d)).eq]
    _ = pinnedX TwistTag.E6.tag K β (d + σ d) *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ d + d) := by
        rw [pinnedX_add, pinnedX_add]
        group

theorem exists_conj_eq_twistedE6PairX_mul_eta [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {e : K} (he : σ e ≠ e)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K σ, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) {c : K} (hc : σ c = c) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ, MulAut.conj g * η * (MulAut.conj g)⁻¹ =
      MulAut.conj (⟨twistedE6PairX σ β c, twistedE6PairX_mem_graphFixedRootGroup hσσ hβ c⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) * η := by
  obtain ⟨d, hd⟩ := exists_add_apply_eq hσσ he hc
  refine ⟨_, (conj_twistedE6PairX_mul_eta hσσ hη hβ d).trans ?_⟩
  subst hd
  rfl

end Rows

end CFSG.SeitzReduction.F4Pilot
