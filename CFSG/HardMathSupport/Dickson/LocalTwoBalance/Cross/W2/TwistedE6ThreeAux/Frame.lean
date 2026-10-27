module

public import CFSG.RankThree.PartOne.KE.E6TwThreeFinal
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Transfer

variable {C M : Type*} [Group C] [Group M]

theorem layer_transfer (ψ : C →* M) (hψ : Function.Injective ψ) {p : ℕ} (P : Subgroup M)
    (R : Subgroup C) (hR : R.map ψ = P) (hq : CFSG.IsQuasisimple P)
    (hpP : ¬ Nat.Coprime p (Nat.card P)) :
    CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime p (Nat.card R) ∧ ∀ u, u ∈ R ↔ ψ u ∈ P := by
  refine ⟨?_, ?_, fun u => ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((R.equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr hR)).symm hq
  · rwa [← hR, Subgroup.card_map_of_injective hψ] at hpP
  · rw [← hR]
    exact (Subgroup.mem_map_iff_mem hψ).symm

theorem map_centralizer_of_injective (ψ : C →* M) (hψ : Function.Injective ψ) (e : C) :
    (Subgroup.centralizer ({e} : Set C)).map ψ =
      ψ.range ⊓ Subgroup.centralizer ({ψ e} : Set M) := by
  have h := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective ψ hψ ⊤ e
  rw [top_inf_eq] at h
  rw [MonoidHom.range_eq_map]
  exact h

end Transfer

section Frame

variable {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω] {g : ModGL Tag.E6 Ω}

variable (K σ Ω g) in
@[expose] def frameEmb (c₀ : twistedE6RootGroup K σ) :
    twistedE6RootGroup K σ →* ModGL Tag.E6 Ω :=
  (MulAut.conj g⁻¹).toMonoidHom.comp ((twE6Emb K σ Ω).comp (MulAut.conj c₀).toMonoidHom)

theorem frameEmb_apply (c₀ u : twistedE6RootGroup K σ) :
    frameEmb K σ Ω g c₀ u = g⁻¹ * twE6Emb K σ Ω (c₀ * u * c₀⁻¹) * g := by
  simp [frameEmb, MulAut.conj_apply]

theorem frameEmb_injective (c₀ : twistedE6RootGroup K σ) :
    Function.Injective (frameEmb K σ Ω g c₀) :=
  (MulAut.conj g⁻¹).injective.comp (twE6Emb_injective.comp (MulAut.conj c₀).injective)

theorem range_frameEmb (c₀ : twistedE6RootGroup K σ) :
    (frameEmb K σ Ω g c₀).range = phi3CStar K σ.toRingHom Ω g := by
  rw [← CFSG.RankThree.PartOne.KETw3.range_conj_twE6Emb σ g]
  unfold frameEmb
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (MulAut.conj c₀).surjective, Subgroup.map_top]

theorem orderOf_frameEmb (c₀ u : twistedE6RootGroup K σ) :
    orderOf (frameEmb K σ Ω g c₀ u) = orderOf u :=
  orderOf_injective _ (frameEmb_injective c₀) u

theorem map_centralizer_frameEmb (c₀ e : twistedE6RootGroup K σ) :
    (Subgroup.centralizer ({e} : Set (twistedE6RootGroup K σ))).map (frameEmb K σ Ω g c₀) =
      phi3CStar K σ.toRingHom Ω g ⊓
        Subgroup.centralizer ({frameEmb K σ Ω g c₀ e} : Set (ModGL Tag.E6 Ω)) := by
  rw [map_centralizer_of_injective _ (frameEmb_injective c₀), range_frameEmb]

end Frame

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
