module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOConfig
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem isSolvable_centralizer_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {z : X}
    {K : Subgroup X}
    (h : Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X))) :
    Group.IsSolvable ↥(centralizer ({e z} : Set Y) ⊓
      centralizer ((K.map e.toMonoidHom : Subgroup Y) : Set Y)) := by
  have hmem : ∀ y : ↥(centralizer ({e z} : Set Y) ⊓
      centralizer ((K.map e.toMonoidHom : Subgroup Y) : Set Y)),
      e.symm y ∈ centralizer ({z} : Set X) ⊓ centralizer (K : Set X) := by
    intro y
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp y.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hy1 ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy1
    · rw [mem_centralizer_iff] at hy2 ⊢
      intro k hk
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy2 (e k) (mem_map_of_mem _ hk)
  let f : ↥(centralizer ({e z} : Set Y) ⊓
      centralizer ((K.map e.toMonoidHom : Subgroup Y) : Set Y)) →*
      ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) :=
    (e.symm.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
  exact Group.isSolvable_of_isSolvable_injective hf

theorem endOddLieInputFor_of_config_solv (T : Finset StatedLieTag)
    (hT : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X →
      ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ T → p.Prime → p ≠ 2 →
        StatedLieAdmissible τ n p f → LieModel X τ n p f →
        ∀ (z : X) (K D : Subgroup X), EndOddCore.Config z K D →
        Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) → False) :
    Sol78.F514.EndOddLieInputFor T := by
  intro X _ _ hX τ n p f hτ hp hp2 hadm hmod z t K P D hK huniq hs hF _ _ _ _ _ hzD hD _ hdih
    h8 hsol hpump
  exact (hT X hX τ n p f hτ hp hp2 hadm hmod z K D
    { twoComp := hK
      unique := huniq
      simple := hs
      foote := hF
      mem_D := hzD
      D_le := hD
      dihedral := hdih
      card_D := h8
      pump := fun b hb hb2 => by
        obtain ⟨Y, hY, -, hYK⟩ := hpump b hb hb2
        exact ⟨Y, hY, hYK⟩ } hsol).elim

theorem endOddLieInputFor_orthogonal :
    Sol78.F514.EndOddLieInputFor {.POmegaOdd, .POmegaPlus, .POmegaMinus} := by
  refine endOddLieInputFor_of_config_solv _ fun X _ _ _ τ n p f hτ hp hp2 _ hmod z K D hcfg
    hsol => ?_
  have hτ' : τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hτ
  rcases hτ' with rfl | rfl | rfl
  · have h := OddClassSelector.statedClassicalModel_of_lieModel hmod
      (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
    have hn : 3 ≤ n := h.1.2.2.1
    obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_odd h k hk e
    exact orth_config_false hp hp2 h.1.2.1 hk (by omega) hnd
      (hcfg.map (coordinateOddWitnessEquiv k e)) (isSolvable_centralizer_map _ hsol)
  · have h := OddClassSelector.statedClassicalModel_of_lieModel hmod
      (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
    have hn : 4 ≤ n := h.1.2.2
    obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus h k hk e
    exact orth_config_false hp hp2 h.1.2.1 hk (by omega) hnd
      (hcfg.map (coordinatePlusWitnessEquiv k e)) (isSolvable_centralizer_map _ hsol)
  · have h := OddClassSelector.statedClassicalModel_of_lieModel hmod
      (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
    have hn : 4 ≤ n := h.1.2.2
    have hn1 : 1 ≤ n := by omega
    obtain ⟨-, k, _, _, hk, b, c, hirr, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus h k hk b c hirr e
    exact orth_config_false hp hp2 h.1.2.1 hk (by omega) hnd
      (hcfg.map (coordinateMinusWitnessEquiv k hn1 b c e)) (isSolvable_centralizer_map _ hsol)

end CFSG.ComponentClassification.CatLeafProof.EndOddO
