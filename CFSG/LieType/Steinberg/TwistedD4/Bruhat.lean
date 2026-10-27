module

public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.Adjoint.Borel
public import CFSG.LieType.TitsSimplicity.Unipotent

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.TitsSimplicity

variable {K : Type} [Field K] (σ : K →+* K)

theorem borel_twisted_le :
    borel (twistedDatum σ) (hHat σ) ≤
    (borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K)).comap
      (twistedGroup σ).subtype := by
  refine sup_le (iSup_le fun i x hx => ?_) fun x hx => ?_
  · have hx' : (x : adjointGroup d4 K) ∈ hHatE σ i := hx
    exact Subgroup.mem_sup_left (hHatE_le_iSup_torus σ i hx')
  · rw [posUnipotent, twisted_setOf_pos_eq] at hx
    have h := iSup_twistedRootGroup_le σ (fun h => 0 < h) hx
    rw [Subgroup.mem_comap] at h ⊢
    refine Subgroup.mem_sup_right ?_
    rw [posUnipotent, adjDatum_roots]
    exact h

theorem negUnipotent_twisted_le :
    negUnipotent (twistedDatum σ) ≤
    (negUnipotent (adjDatum (rootOperatorFamily d4) K)).comap (twistedGroup σ).subtype := by
  intro x hx
  rw [negUnipotent, twisted_setOf_neg_eq] at hx
  have h := iSup_twistedRootGroup_le σ (fun h => h < 0) hx
  rw [Subgroup.mem_comap] at h ⊢
  rw [negUnipotent, adjDatum_roots]
  exact h

theorem twistedDatum_bruhatExtras
    : BruhatExtras (twistedDatum σ) (hHat σ) where
  borel_inf_negUnipotent := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have h : (g : adjointGroup d4 K) ∈
        borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K) ⊓
          negUnipotent (adjDatum (rootOperatorFamily d4) K) :=
      Subgroup.mem_inf.2 ⟨borel_twisted_le σ hg.1, negUnipotent_twisted_le σ hg.2⟩
    rw [(adjDatum_bruhatExtras (rootOperatorFamily d4) K).borel_inf_negUnipotent,
      Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem twistedDatum_rootGroupCommutators
    : RootGroupCommutators (twistedDatum σ) :=
  .of_divisible_eq_empty rfl fun _ hβ _ hx _ hy =>
    Subtype.ext (commute_of_mem_twistedRootSubgroupD4 σ (isRoot_of_mem_twistedDatum_roots σ hβ)
      hx hy).eq

end CFSG.LieType.Steinberg.TwistedD4
