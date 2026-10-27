module

public import CFSG.ClassicalGroups.UnitaryFlag.LineSU2

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K]

private theorem finrank_sup_three_le_two (h : UnitaryFieldData 2 m K)
    {L₁ L₂ L₃ : Submodule K (Fin 3 → K)} (h₁ : L₁ ∈ isotropicLines h 3)
    (h₂ : L₂ ∈ isotropicLines h 3) (h₃ : L₃ ∈ isotropicLines h 3)
    (hL3 : L₃ ≤ L₁ ⊔ L₂) :
    Module.finrank K ↥(L₁ ⊔ L₂ ⊔ L₃) ≤ 2 := by
  have h1 := (mem_isotropicLines.mp h₁).1
  have h2 := (mem_isotropicLines.mp h₂).1
  have h3 := (mem_isotropicLines.mp h₃).1
  have hsup : L₁ ⊔ L₂ ⊔ L₃ = L₁ ⊔ L₂ := sup_eq_left.mpr hL3
  rw [hsup]
  have h12 := Submodule.finrank_add_le_finrank_add_finrank L₁ L₂
  rw [h1, h2] at h12
  omega

theorem sup_three_isotropicTransvectionGroup_eq_top
    (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {L₁ L₂ L₃ : Submodule K (Fin 3 → K)}
    (h₁ : L₁ ∈ isotropicLines h 3) (h₂ : L₂ ∈ isotropicLines h 3) (h₃ : L₃ ∈ isotropicLines h 3)
    (hspan : L₁ ⊔ L₂ ⊔ L₃ = ⊤) :
    isotropicTransvectionGroup h 3 L₁ ⊔ isotropicTransvectionGroup h 3 L₂ ⊔
      isotropicTransvectionGroup h 3 L₃ = ⊤ := by
  have hfin3 : Module.finrank K ↥(L₁ ⊔ L₂ ⊔ L₃) = 3 := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  have h1dim := (mem_isotropicLines.mp h₁).1
  have h2dim := (mem_isotropicLines.mp h₂).1
  have hL12 : L₁ ≠ L₂ := by
    intro hEq
    have hle : Module.finrank K ↥(L₁ ⊔ L₂ ⊔ L₃) ≤ 2 := by
      have hEq' : L₁ ⊔ L₂ = L₁ := by rw [hEq, sup_idem]
      rw [hEq']
      have h := Submodule.finrank_add_le_finrank_add_finrank L₁ L₃
      rw [h1dim, (mem_isotropicLines.mp h₃).1] at h
      exact h
    omega
  have hL3 : ¬ L₃ ≤ L₁ ⊔ L₂ := by
    intro hle
    have hle2 : Module.finrank K ↥(L₁ ⊔ L₂ ⊔ L₃) ≤ 2 :=
      finrank_sup_three_le_two h h₁ h₂ h₃ hle
    omega
  have hale := stdPointA_mem_isotropicLines h
  have hble := stdPointB_mem_isotropicLines h
  have hne12 : (⟨L₁, h₁⟩ : isotropicLines h 3) ≠ ⟨L₂, h₂⟩ :=
    fun he => hL12 (congrArg Subtype.val he)
  have hneAB : (⟨stdPointA, hale⟩ : isotropicLines h 3) ≠ ⟨stdPointB, hble⟩ := by
    intro he
    have hval : stdPointA (K := K) = stdPointB (K := K) := congrArg Subtype.val he
    have hb : (stdIsoB : Fin 3 → K) ∈ stdPointA (K := K) := by
      rw [hval]
      exact stdIsoB_mem_stdPointB
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hb
    have h2c := congrFun hlam 2
    simp [stdIsoA, stdIsoB] at h2c
  obtain ⟨-, -, hpair, h3orth, -⟩ := unitary_isotropic_pair_orbits h (n := 3) (by norm_num)
  have horth : ¬ (∀ x ∈ L₁, ∀ y ∈ L₂, stdHermForm h 3 x y = 0) :=
    h3orth rfl ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ hne12
  have horthAB : ¬ (∀ x ∈ stdPointA, ∀ y ∈ stdPointB, stdHermForm h 3 x y = 0) := by
    intro hc
    have hzero := hc stdIsoA stdIsoA_mem_stdPointA stdIsoB stdIsoB_mem_stdPointB
    rw [stdHermForm_stdIsoA_stdIsoB] at hzero
    exact one_ne_zero hzero
  obtain ⟨g, hg1', hg2'⟩ :=
    (hpair ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ ⟨stdPointA, hale⟩ ⟨stdPointB, hble⟩ hne12 hneAB).mpr
      (iff_of_false horth horthAB)
  have hg1 : g • L₁ = stdPointA (K := K) := congrArg Subtype.val hg1'
  have hg2 : g • L₂ = stdPointB (K := K) := congrArg Subtype.val hg2'
  set z : Submodule K (Fin 3 → K) := g • L₃ with hzdef
  have hz : z ∈ isotropicLines h 3 := by
    rw [hzdef]
    exact (isotropicLines h 3).smul_mem g h₃
  have hstdPlane : g • (L₁ ⊔ L₂) = stdLinePlane (K := K) := by
    rw [unitarySU_smul_sup h g L₁ L₂, hg1, hg2, stdLinePlane_eq_stdPointA_sup_stdPointB]
  have hzW : ¬ z ≤ stdLinePlane (K := K) := by
    intro hzle
    apply hL3
    have h1 : g⁻¹ • z ≤ g⁻¹ • stdLinePlane (K := K) := unitarySU_smul_mono h g⁻¹ hzle
    have h2 : g⁻¹ • z = L₃ := by rw [hzdef, inv_smul_smul]
    have h3 : g⁻¹ • stdLinePlane (K := K) = L₁ ⊔ L₂ := by
      rw [← hstdPlane, inv_smul_smul]
    rwa [h2, h3] at h1
  have hstd := sup_stdLineSU2_isotropicTransvectionGroup_eq_top h hm hz hzW
  change isotropicTransvectionGroup h 3 stdPointA ⊔ isotropicTransvectionGroup h 3 stdPointB ⊔
    isotropicTransvectionGroup h 3 z = ⊤ at hstd
  have hmapA := (unitary_point_conjugation h g h₁).2.1
  have hmapB := (unitary_point_conjugation h g h₂).2.1
  have hmapC := (unitary_point_conjugation h g h₃).2.1
  have hH : Subgroup.map (MulAut.conj g).toMonoidHom
      (isotropicTransvectionGroup h 3 L₁ ⊔ isotropicTransvectionGroup h 3 L₂ ⊔
        isotropicTransvectionGroup h 3 L₃) = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hmapA, hmapB, hmapC, hg1, hg2, ← hzdef]
    exact hstd
  have htop : Subgroup.map (MulAut.conj g).toMonoidHom (⊤ : Subgroup (unitarySU 2 m K 3)) = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  have hinj : Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  exact hinj (hH.trans htop.symm)

end CFSG.ClassicalGroups.UnitaryFlag
