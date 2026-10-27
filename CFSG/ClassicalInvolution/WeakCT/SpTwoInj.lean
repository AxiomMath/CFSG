module

public import CFSG.ClassicalInvolution.WeakCT.SpModel
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

private theorem tv01_not_commute_tv10 {F : Type} [Field F] :
    ¬ Commute (tv 0 1 (1 : F) : SL(2, F)) (tv 1 0 (1 : F)) := by
  intro h
  have h00 := congrArg (fun g : SL(2, F) => ((g : Matrix (Fin 2) (Fin 2) F)) 0 0) h.eq
  simp [Matrix.SpecialLinearGroup.coe_mul, tv01_eq_sl2Upper, tv10_eq_sl2Lower,
    coe_sl2Upper, coe_sl2Lower] at h00

theorem hom_injective_of_long_two {F : Type} [Field F] (hF : Nat.card F = 2) {G : Type*}
    [Group G] {φ : StatedSp 2 F →* G} (hl : Function.Injective (φ.comp (spBlock F 1))) :
    Function.Injective φ := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  set e : StatedSp 2 F ≃* Equiv.Perm (Fin 6) :=
    CFSG.SeitzReduction.F4Pilot.sp4EquivPerm hF with he
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  have hN : Nontrivial φ.ker := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨g, MonoidHom.mem_ker.mpr hg, hg1⟩
  have hNmap : Nontrivial (φ.ker.map e.toMonoidHom) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    obtain ⟨x, hx, hx1⟩ := (Subgroup.nontrivial_iff_exists_ne_one φ.ker).mp hN
    refine ⟨e.toMonoidHom x, Subgroup.mem_map_of_mem e.toMonoidHom hx, fun h => hx1 ?_⟩
    exact e.injective (by simpa using h)
  have hnorm : (φ.ker.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (inferInstance : φ.ker.Normal) e.toMonoidHom e.surjective
  have hA : alternatingGroup (Fin 6) ≤ φ.ker.map e.toMonoidHom :=
    @Equiv.Perm.alternatingGroup_le_of_normal (Fin 6) _ _ (by simp)
      (φ.ker.map e.toMonoidHom) hnorm hNmap
  set c : SL(2, F) := ⁅(tv (n := 2) 0 1 (1 : F)), (tv (n := 2) 1 0 (1 : F))⁆ with hc
  have hcA : e (spBlock F 1 c) ∈ alternatingGroup (Fin 6) := by
    rw [hc, map_commutatorElement, map_commutatorElement]
    exact alternatingGroup.commutator_perm_le
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
        (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hcN : spBlock F 1 c ∈ φ.ker := by
    rw [← Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]
    exact hA hcA
  have hφc : φ (spBlock F 1 c) = 1 := MonoidHom.mem_ker.mp hcN
  have hc1 : c = 1 := hl (by simpa using hφc)
  exact tv01_not_commute_tv10
    (commutatorElement_eq_one_iff_commute.mp (by rwa [hc] at hc1))

end CFSG.ClassicalInvolution.WeakCT
