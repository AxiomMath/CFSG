module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

private theorem centerOf_conj_mem (g : C) {z : C} (hz : z ∈ centerOf Q) :
    g * z * g⁻¹ ∈ centerOf Q := by
  obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(inferInstance : Q.Normal).conj_mem z hzQ g, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxQ : g⁻¹ * x * g ∈ Q := by
    simpa using (inferInstance : Q.Normal).conj_mem x hx g⁻¹
  have h1 : (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) :=
    (Subgroup.mem_centralizer_iff.mp hzc) (g⁻¹ * x * g) hxQ
  calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = (g * z * g⁻¹) * x := by group

theorem AschbacherHyp.centralizer_commutator_le_of_le_commutator [Finite C]
    (hC : AschbacherHyp C Q) (hQL : Q ≤ commutator C) :
    centralizer (commutator C : Set C) ≤ centerOf Q := by
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  haveI : Finite Q := hC.plus.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  let W : Subgroup C :=
    { carrier := {x | x ∈ Q ∧ ∀ g ∈ commutator C, ⁅g, x⁆ ∈ centerOf Q}
      one_mem' := by
        refine ⟨Q.one_mem, ?_⟩
        intro g _
        rw [commutatorElement_one_right]
        exact (centerOf Q).one_mem
      mul_mem' := by
        rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
        refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
        intro g hg
        have hcx : ⁅g, x⁆ ∈ centerOf Q := hx g hg
        have hcy : ⁅g, y⁆ ∈ centerOf Q := hy g hg
        have hc : x * ⁅g, y⁆ = ⁅g, y⁆ * x :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcy).2) x hxQ
        have hxy : x * ⁅g, y⁆ * x⁻¹ = ⁅g, y⁆ := by rw [hc, mul_inv_cancel_right]
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅g, x⁆ * x * ⁅g, y⁆ * x⁻¹ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) := by group
        rw [h1, hxy]
        exact mul_mem hcx hcy
      inv_mem' := by
        rintro x ⟨hxQ, hx⟩
        refine ⟨Q.inv_mem hxQ, ?_⟩
        intro g hg
        have hcx : ⁅g, x⁆ ∈ centerOf Q := hx g hg
        have hcxi : ⁅g, x⁆⁻¹ ∈ centerOf Q := (centerOf Q).inv_mem hcx
        have hc : x * ⁅g, x⁆⁻¹ = ⁅g, x⁆⁻¹ * x :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcxi).2) x hxQ
        have hconj : x⁻¹ * ⁅g, x⁆⁻¹ * x = ⁅g, x⁆⁻¹ := by
          rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [commutatorElement_inv_right, ← commutatorElement_inv, hconj]
        exact hcxi }
  have hZW : centerOf Q ≤ W := by
    intro z hz
    obtain ⟨hzQ, _⟩ := Subgroup.mem_inf.mp hz
    refine ⟨hzQ, ?_⟩
    intro g _
    rw [commutatorElement_def]
    exact mul_mem (centerOf_conj_mem g hz) ((centerOf Q).inv_mem hz)
  have hWQ : W ≤ Q := fun _ hx => hx.1
  have hinv : ∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g _ w hw
    refine ⟨(inferInstance : Q.Normal).conj_mem w hw.1 g, ?_⟩
    intro h hh
    have ha : g⁻¹ * h * g ∈ commutator C := by
      simpa using (inferInstance : (commutator C).Normal).conj_mem h hh g⁻¹
    have hcw : ⁅g⁻¹ * h * g, w⁆ ∈ centerOf Q := hw.2 (g⁻¹ * h * g) ha
    have hconj : g * ⁅g⁻¹ * h * g, w⁆ * g⁻¹ ∈ centerOf Q := centerOf_conj_mem g hcw
    have heq : g * ⁅g⁻¹ * h * g, w⁆ * g⁻¹ = ⁅h, g * w * g⁻¹⁆ := by
      rw [conjugate_commutatorElement]
      congr 1
      group
    rw [heq] at hconj
    exact hconj
  rcases hC.irreducible W hZW hWQ hinv with hW | hW
  ·
    intro x hx
    have hxW : x ∈ W := by
      refine ⟨hC.centralizer_le (Subgroup.centralizer_le hQL hx), ?_⟩
      intro g hg
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hx) g hg)]
      exact (centerOf Q).one_mem
    rwa [hW] at hxW
  ·
    exfalso
    have hcomm : commutator C ≤ Q := by
      refine le_of_forall_commutator_mem_centerOf hE hC.centralizer_le (K := commutator C) ?_
      intro g hg x hx
      have hxW : x ∈ W := hW.symm ▸ hx
      exact hxW.2 g hg
    haveI : IsMulCommutative (C ⧸ Q) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
    obtain ⟨a, b, hab⟩ := A5WrTwo.exists_mul_ne_mul
    obtain ⟨e⟩ := hC.quotient
    exact hab (by
      calc a * b = e (e.symm a) * e (e.symm b) := by rw [e.apply_symm_apply, e.apply_symm_apply]
        _ = e (e.symm a * e.symm b) := by rw [map_mul]
        _ = e (e.symm b * e.symm a) := by rw [mul_comm']
        _ = e (e.symm b) * e (e.symm a) := by rw [map_mul]
        _ = b * a := by rw [e.apply_symm_apply, e.apply_symm_apply])

end CFSG.EvenSporadicStandard.HNRecog
