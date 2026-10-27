module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthCharM
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

variable {G : Type} [Group G]

theorem OrthCoord.exists_induced {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}
    (hC : OrthCoord K M ρ θ) (hMp : M = CFSG.Open.pCoreOf 2 K) {φ : G → G}
    (hφ : IsIsoOn K K φ) :
    ∃ σ : Perm (Fin 5), ∀ l : ↥K, ρ ⟨φ l, hφ.mem l l.2⟩ = σ * ρ l * σ⁻¹ := by
  classical
  let A : Subgroup (Perm (Fin 5)) := alternatingGroup (Fin 5)
  let ρA : ↥K →* A :=
    MonoidHom.codRestrict ρ A fun l => Equiv.Perm.mem_alternatingGroup.mpr (hC.sign_eq l)
  have hρA_coe : ∀ l : ↥K, (ρA l : Perm (Fin 5)) = ρ l := fun l => rfl
  have hρA_surj : Function.Surjective ρA := by
    intro a
    obtain ⟨l, hl⟩ := hC.surj (a : Perm (Fin 5)) (Equiv.Perm.mem_alternatingGroup.mp a.2)
    exact ⟨l, Subtype.ext hl⟩
  let τ : ↥K →* A := ρA.comp hφ.toMulEquiv.toMonoidHom
  have hτ_surj : Function.Surjective τ := hρA_surj.comp hφ.toMulEquiv.surjective
  have hker : ρA.ker ≤ τ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have hlρ : ρ l = 1 := by
      have h := congrArg (fun x : A => (x : Perm (Fin 5))) hl
      simpa [hρA_coe] using h
    have hlM : (l : G) ∈ M := (hC.ker l).mp hlρ
    have hlM' : (l : G) ∈ CFSG.Open.pCoreOf 2 K := by rwa [← hMp]
    have hφlM' : φ l ∈ CFSG.Open.pCoreOf 2 K := IsIsoOn.map_mem_pCoreOf hφ hlM'
    have hφlM : φ l ∈ M := by rwa [hMp]
    show ρA (hφ.toMulEquiv l) = 1
    apply Subtype.ext
    rw [hρA_coe]
    show ρ (hφ.toMulEquiv l) = 1
    exact (hC.ker (hφ.toMulEquiv l)).mpr (by rw [IsIsoOn.toMulEquiv_apply]; exact hφlM)
  let α : A →* A :=
    ρA.liftOfRightInverse (Function.surjInv hρA_surj)
      (Function.rightInverse_surjInv hρA_surj) ⟨τ, hker⟩
  have hα : ∀ l : ↥K, α (ρA l) = τ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply ρA (Function.surjInv hρA_surj)
      (Function.rightInverse_surjInv hρA_surj) ⟨τ, hker⟩ l
  have hα_surj : Function.Surjective α := by
    intro a
    obtain ⟨l, hl⟩ := hτ_surj a
    exact ⟨ρA l, by rw [hα l, hl]⟩
  have hα_bij : Function.Bijective α :=
    ⟨(Finite.injective_iff_surjective).mpr hα_surj, hα_surj⟩
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).2 (MulEquiv.ofBijective α hα_bij)
  have hσa : ∀ a : A, MulAut.conjNormal σ a = α a := by
    intro a
    rw [hσ]
    rfl
  refine ⟨σ, fun l => ?_⟩
  have hsub : hφ.toMulEquiv l = ⟨φ l, hφ.mem l l.2⟩ :=
    Subtype.ext (IsIsoOn.toMulEquiv_apply hφ l)
  calc
    ρ ⟨φ l, hφ.mem l l.2⟩ = (ρA (hφ.toMulEquiv l) : Perm (Fin 5)) := by
      rw [hρA_coe]
      exact (congrArg ρ hsub).symm
    _ = (α (ρA l) : Perm (Fin 5)) := by rw [hα l]; rfl
    _ = ((MulAut.conjNormal σ) (ρA l) : Perm (Fin 5)) :=
        (congrArg (fun x : A => (x : Perm (Fin 5))) (hσa (ρA l))).symm
    _ = σ * ρ l * σ⁻¹ := by rw [MulAut.conjNormal_apply, hρA_coe]

end CFSG.EvenSporadicStandard.HNRecog.Section4
