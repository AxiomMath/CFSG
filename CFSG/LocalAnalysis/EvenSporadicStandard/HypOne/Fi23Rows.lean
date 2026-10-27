module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Lift
public import CFSG.Sporadic.FischerOddCore.Fi23LocalComp

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open Subgroup CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore
  CFSG.Blueprint.Fischer CFSG.Monster.B.Fischer CFSG.EvenSporadicStandard.TwoCo1.HypOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fourClassesLarge_fi22J
    (v : CFSG.Sporadic.Fi22.J) (hv : orderOf v = 2) :
    FourClassesLarge ↥(centralizer ({v} : Set CFSG.Sporadic.Fi22.J)) := by
  have hp : orderOf ((fi22PJ.symm v : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hv
  have h := (CFSG.EvenSporadicStandard.HypOne.Fi22.fourClassesLarge_rows).1 _
    (fi22PJ.symm v).2 hp
  have e3 : ↥(centralizer ({fi22PJ (fi22PJ.symm v)} : Set CFSG.Sporadic.Fi22.J)) ≃*
      ↥(centralizer ({v} : Set CFSG.Sporadic.Fi22.J)) :=
    MulEquiv.subgroupCongr (by rw [MulEquiv.apply_symm_apply])
  exact FourClassesLarge.of_mulEquiv
    (((@centralizerEquiv fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ
      (fi22PJ.symm v)).trans e3).symm.trans
      (centralizerSubgroupEquiv fi22P (fi22PJ.symm v))) h

theorem fourClassesLarge_d :
    FourClassesLarge ↥(centralizer ({d} : Set J)) := by
  have hP : (⊤ : Subgroup ↥(centralizer ({d} : Set J))) ≤
      ⁅(⊤ : Subgroup ↥(centralizer ({d} : Set J))), ⊤⁆ := by
    rw [← _root_.commutator_def]
    exact commutator_C.symm.le
  refine fourClassesLarge_of_perfect hP fun x hx _ => ?_
  have hxc : x ∈ Subgroup.center ↥(centralizer ({d} : Set J)) :=
    Subgroup.mem_center_iff.2 fun g => hx g trivial
  have hc : Nat.card (Subgroup.center ↥(centralizer ({d} : Set J))) = 2 := card_center_C
  have h2 : (⟨x, hxc⟩ : Subgroup.center ↥(centralizer ({d} : Set J))) ^ 2 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  simpa using congrArg Subtype.val h2

theorem mul_self_of_isConj_d {x : J} (hx : IsConj d x) :
    x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  calc g * d * g⁻¹ * (g * d * g⁻¹) = g * (d * d) * g⁻¹ := by group
    _ = 1 := by rw [d_sq]; group

theorem mul_self_of_isConj_t2
    {x : J} (hx : IsConj t2 x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  have h2 : t2 * t2 = 1 := by rw [← pow_two]; exact t2_sq
  calc g * t2 * g⁻¹ * (g * t2 * g⁻¹) = g * (t2 * t2) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem fourClassesLarge_pair
    {h e1 : J} {P : Subgroup J} (he1eq : e1 = h * d * h⁻¹) (he1 : e1 ∈ LocalClass D23 d)
    (hP : P ≤ ⁅P, P⁆) (hdP : d ∈ P) (he1P : e1 ∈ P)
    (hcomm : ∀ p ∈ P, p * d = d * p ∧ p * e1 = e1 * p) :
    FourClassesLarge ↥(centralizer ({d * e1} : Set J)) := by
  have hdd : d * d = 1 := d_sq
  obtain ⟨hD1, hne, hcomm1⟩ := he1
  have hee : e1 * e1 = 1 := mul_self_of_isConj_d hD1
  have hrB : IsConj (d * d1) (d * e1) :=
    isConj_d_mul_d1_of_mem (IsConj.refl d : d ∈ D23) ⟨hD1, hne, hcomm1⟩
  have hda : d * (d * e1) = e1 := by rw [← mul_assoc, hdd, one_mul]
  have hea : e1 * (d * e1) = d := by
    calc e1 * (d * e1) = e1 * d * e1 := (mul_assoc _ _ _).symm
      _ = d * e1 * e1 := by rw [hcomm1]
      _ = d := by rw [mul_assoc, hee, mul_one]
  refine fourClassesLarge_centralizer_of_pair fi23Kappa fi23Kappa_surjective
    (fun c hc => fi23Kappa_eq_one hc) fourClassesLarge_fi22J he1eq (r := d * e1) ?_ ?_ ?_ ?_
    hne.symm ?_ ?_ ?_ ?_ ?_ hP hdP he1P
  · calc d * e1 * (d * e1) = d * (e1 * d) * e1 := by group
      _ = d * (d * e1) * e1 := by rw [hcomm1]
      _ = (d * d) * (e1 * e1) := by group
      _ = 1 := by rw [hdd, hee, one_mul]
  · intro h1
    exact hne (mul_left_cancel (a := d) (h1.trans hdd.symm))
  · intro h1
    have h2 : e1 = 1 := mul_left_cancel (a := d) (by rw [mul_one]; exact h1)
    exact d_ne_one (isConj_one_right.1 (h2 ▸ hD1).symm)
  · intro h1
    exact d_ne_one (mul_right_cancel (b := e1) (by rw [one_mul]; exact h1))
  · calc d * e1 * d = d * (e1 * d) := mul_assoc _ _ _
      _ = d * (d * e1) := by rw [hcomm1]
  · rw [← mul_assoc, hcomm1]
  · intro g hg
    rw [hda] at hg
    exact not_isConj_d_d_mul_d1 (hD1.trans (hrB.trans (isConj_iff.2 ⟨g, hg⟩)).symm)
  · intro g hg
    rw [hea] at hg
    exact not_isConj_d_d_mul_d1 (hrB.trans (isConj_iff.2 ⟨g, hg⟩)).symm
  · intro p hp
    obtain ⟨hpd, hpe⟩ := hcomm p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * (d * e1) = (p * d) * e1 := (mul_assoc _ _ _).symm
      _ = (d * p) * e1 := by rw [hpd]
      _ = d * (p * e1) := mul_assoc _ _ _
      _ = d * (e1 * p) := by rw [hpe]
      _ = d * e1 * p := (mul_assoc _ _ _).symm

theorem fourClassesLarge_triple
    {h e1 c : J} {P : Subgroup J} (he1eq : e1 = h * d * h⁻¹) (he1 : e1 ∈ LocalClass D23 d)
    (hc : c ∈ LocalClass D23 d) (hce1 : c ∈ LocalClass D23 e1) (hP : P ≤ ⁅P, P⁆) (hdP : d ∈ P)
    (he1P : e1 ∈ P) (hcomm : ∀ p ∈ P, p * d = d * p ∧ p * e1 = e1 * p ∧ p * c = c * p) :
    FourClassesLarge ↥(centralizer ({d * e1 * c} : Set J)) := by
  have hdd : d * d = 1 := d_sq
  obtain ⟨hD1, hne, hcomm1⟩ := he1
  obtain ⟨hDc, hnc, hcomm2⟩ := hc
  obtain ⟨hD1c, hnc1, hcomm3⟩ := hce1
  have hee : e1 * e1 = 1 := mul_self_of_isConj_d hD1
  have hdD : d ∈ D23 := IsConj.refl d
  have hrt : IsConj t2 (d * e1 * c) :=
    isConj_t2_of_mem hdD ⟨hD1, hne, hcomm1⟩ ⟨hDc, hnc, hcomm2⟩ ⟨hD1c, hnc1, hcomm3⟩
  have hbc : IsConj (d * d1) (e1 * c) := isConj_d_mul_d1_of_mem hD1 ⟨hD1c, hnc1, hcomm3⟩
  have hbd : IsConj (d * d1) (d * c) := isConj_d_mul_d1_of_mem hdD ⟨hDc, hnc, hcomm2⟩
  have hda : d * (d * e1 * c) = e1 * c := by rw [← mul_assoc, ← mul_assoc, hdd, one_mul]
  have hea : e1 * (d * e1 * c) = d * c := by
    calc e1 * (d * e1 * c) = (e1 * d) * e1 * c := by group
      _ = (d * e1) * e1 * c := by rw [hcomm1]
      _ = d * (e1 * e1) * c := by group
      _ = d * c := by rw [hee, mul_one]
  refine fourClassesLarge_centralizer_of_pair fi23Kappa fi23Kappa_surjective
    (fun c' hc' => fi23Kappa_eq_one hc') fourClassesLarge_fi22J he1eq (r := d * e1 * c)
    (mul_self_of_isConj_t2 hrt) ?_ ?_ ?_ hne.symm ?_ ?_ ?_ ?_ ?_ hP hdP he1P
  · intro h1
    exact t2_ne_one (isConj_one_right.1 (h1 ▸ hrt).symm)
  · intro h1
    exact not_isConj_d_t2 (h1 ▸ hrt).symm
  · intro h1
    exact not_isConj_d_t2 (hD1.trans (h1 ▸ hrt).symm)
  · calc d * e1 * c * d = d * e1 * (c * d) := mul_assoc _ _ _
      _ = d * e1 * (d * c) := by rw [hcomm2]
      _ = d * (e1 * d) * c := by group
      _ = d * (d * e1) * c := by rw [hcomm1]
      _ = d * (d * e1 * c) := by group
  · calc d * e1 * c * e1 = d * e1 * (c * e1) := mul_assoc _ _ _
      _ = d * e1 * (e1 * c) := by rw [hcomm3]
      _ = d * (e1 * e1) * c := by group
      _ = d * c := by rw [hee, mul_one]
      _ = e1 * (d * e1 * c) := hea.symm
  · intro g hg
    rw [hda] at hg
    exact not_isConj_d_mul_d1_t2 ((hrt.trans (isConj_iff.2 ⟨g, hg⟩)).trans hbc.symm).symm
  · intro g hg
    rw [hea] at hg
    exact not_isConj_d_mul_d1_t2 ((hrt.trans (isConj_iff.2 ⟨g, hg⟩)).trans hbd.symm).symm
  · intro p hp
    obtain ⟨hpd, hpe, hpc⟩ := hcomm p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * (d * e1 * c) = (p * d) * e1 * c := by group
      _ = (d * p) * e1 * c := by rw [hpd]
      _ = d * (p * e1) * c := by group
      _ = d * (e1 * p) * c := by rw [hpe]
      _ = d * e1 * (p * c) := by group
      _ = d * e1 * (c * p) := by rw [hpc]
      _ = d * e1 * c * p := by group

end CFSG.EvenSporadicStandard.HypOne.Fi23
