module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Layer

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

section Kernel

variable {Ω : Type} [Field Ω]

theorem commute_rootDiagUnit_of_mem_rootSpan_kernel (a : Fin Tag.E6.rank → Ωˣ)
    {v : ModGL Tag.E6 Ω} (hv : v ∈ rootSpan Tag.E6 Ω (rootCharKernel a)) :
    Commute v (rootDiagUnit Tag.E6 a) := by
  have hle : rootSpan Tag.E6 Ω (rootCharKernel a) ≤
      Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 Ω)) := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    have h := rootDiagUnit_conj_pinnedX a hα.1 c
    rw [hα.2, Units.val_one, one_mul] at h
    calc rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω α c
        = rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω α c * (rootDiagUnit Tag.E6 a)⁻¹ *
          rootDiagUnit Tag.E6 a := by group
      _ = pinnedX Tag.E6 Ω α c * rootDiagUnit Tag.E6 a := by rw [h]
  have := Subgroup.mem_centralizer_iff.1 (hle hv) _ (Set.mem_singleton _)
  exact this.symm

theorem conj_cm_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    {c : ModGL Tag.E6 Ω} (hc : c ∈ torusGroup Tag.E6 Ω) {v : ModGL Tag.E6 Ω}
    (hv : v ∈ rootSpan Tag.E6 Ω S) (w : WeylGroup Tag.E6) :
    c * canonicalRep (coxeterSystem Tag.E6) Ω w * v *
        (c * canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈
      rootSpan Tag.E6 Ω ((fun γ => w • γ) '' S) := by
  have h1 : canonicalRep (coxeterSystem Tag.E6) Ω w * v *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ ∈ rootSpan Tag.E6 Ω ((fun γ => w • γ) '' S) := by
    rw [← CFSG.RankThree.PartOne.KE.map_conj_rootSpan w hS]
    exact ⟨v, hv, rfl⟩
  have hS' : ∀ α ∈ (fun γ => w • γ) '' S, IsRoot Tag.E6 α := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact IsRoot.smul (hS γ hγ) w
  have hn := CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan (Ω := Ω) hS' hc
  have := (Subgroup.mem_normalizer_iff.1 hn _).1 h1
  have e : c * canonicalRep (coxeterSystem Tag.E6) Ω w * v *
        (c * canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ =
      c * (canonicalRep (coxeterSystem Tag.E6) Ω w * v *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) * c⁻¹ := by group
  rw [e]
  exact this

end Kernel

section Blocks

variable {Ω : Type} [Field Ω]

theorem e6A2Frame_mem_block (i : Fin 3) {γ : Fin 2 → ℤ} (hγ : γ ∈ RA2) :
    e6A2Frame i γ ∈ e6BlockRoots i := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq] at hγ
  obtain ⟨a, b, hab, h⟩ := hγ
  have hγ0 : γ 0 = (Pi.single a 1 - Pi.single b 1 : Fin 3 → ℤ) 0 := by
    have := congrFun h 0
    simpa [CFSG.LieType.Universal.SpecialLinear.toStd] using this
  have hγ1 : γ 1 = -((Pi.single a 1 - Pi.single b 1 : Fin 3 → ℤ) 2) := by
    have := congrFun h 2
    simp [CFSG.LieType.Universal.SpecialLinear.toStd] at this
    simp only [Pi.sub_apply]
    linarith
  have hfr : e6A2Frame i γ = e6A2Root i a b := by
    funext l
    simp only [e6A2Frame, e6A2Root, e6A2Weight, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, hγ0, hγ1]
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp; done) | (simp; ring)
  rw [mem_e6BlockRoots]
  refine ⟨?_, a, b, hab, hfr⟩
  rw [hfr]
  obtain ⟨m, hm⟩ := (e6A2_root_check.1 i a b hab)
  exact (isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩)

theorem frameBlock_mem_rootSpan_block {ψ : Fin 3 → SL(3, Ω) →* adjointGroup Tag.E6 Ω}
    (hψ : IsSignedFrame Ω ψ) (i : Fin 3) (A : SL(3, Ω)) :
    frameBlock ψ i A ∈ rootSpan Tag.E6 Ω (e6BlockRoots i) := by
  have hgen : ∀ γ ∈ RA2, ∀ c : Ω, frameBlock ψ i (CFSG.LieType.Steinberg.SL.x 2 Ω γ c) ∈
      rootSpan Tag.E6 Ω (e6BlockRoots i) := by
    intro γ hγ c
    change ((ψ i (CFSG.LieType.Steinberg.SL.x 2 Ω γ c) : adjointGroup Tag.E6 Ω) :
      ModGL Tag.E6 Ω) ∈ _
    rw [hψ i γ hγ c]
    exact rootSubgroup_le_rootSpan (e6A2Frame_mem_block i hγ)
      (Subgroup.subset_closure (Set.mem_range_self _))
  have hT : ∀ X ∈ CFSG.LinearGroups.elementarySet 3 Ω, frameBlock ψ i X ∈
      rootSpan Tag.E6 Ω (e6BlockRoots i) := by
    rintro _ ⟨a, b, hab, t, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · convert hgen ![1, 0] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · convert hgen ![1, 1] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · convert hgen ![-1, 0] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · exact absurd rfl hab
    · convert hgen ![0, 1] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · convert hgen ![-1, -1] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · convert hgen ![0, -1] (mem_RA2_of_toStd hab (by decide)) t using 2
      exact (CFSG.LieType.Steinberg.SL.x_eq hab (by decide) t).symm
    · exact absurd rfl hab
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 Ω) ≤
      (rootSpan Tag.E6 Ω (e6BlockRoots i)).comap (frameBlock ψ i) :=
    (Subgroup.closure_le _).2 fun X hX => hT X hX
  have hall : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 Ω) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]; trivial
  exact hle hall

end Blocks

end CFSG.HardMathSupport.Malle.SeitzCube
