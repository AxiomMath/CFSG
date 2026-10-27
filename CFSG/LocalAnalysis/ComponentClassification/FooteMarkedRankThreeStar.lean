module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
import CFSG.LocalAnalysis.ComponentClassification.GrSLitEverySource
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {B : Type} [Group B] [Finite B]

private theorem isComponent_subgroupOf_centralizer_of_commute {A : Subgroup B}
    (hRI : ∀ (a b : B) (K : Subgroup B), orderOf a = 2 →
      A ≤ centralizer ({a} : Set B) →
      IsComponent (A.subgroupOf (centralizer ({a} : Set B))) →
      GrSLit.GSWeakCorr a A b K → K = A)
    {a w : B} (ha : orderOf a = 2) (hw : orderOf w = 2) (haw : a * w = w * a)
    (hAa : A ≤ centralizer ({a} : Set B))
    (hA : IsComponent (A.subgroupOf (centralizer ({a} : Set B))))
    (hAw : A ≤ centralizer ({w} : Set B)) :
    IsComponent (A.subgroupOf (centralizer ({w} : Set B))) := by
  have hAc := hA
  obtain ⟨hAq0, hAsn0⟩ := hAc
  have hAq : IsQuasisimple ↥A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAa) hAq0
  have hApa : IsPComponent 2 (A.subgroupOf (centralizer ({a} : Set B))) :=
    CFSG.OddStandard.Solomon75.isPComponent_two_of_isQuasisimple_of_subnormal hAq hAa hAsn0
  have hwK : w ∈ ComponentClassification.UnbalancedLayer.coreActionKernel A :=
    FooteLit.mem_coreActionKernel_of_le_centralizer hAw
  obtain ⟨K, hcorr⟩ := GrSLit.exists_gsWeakCorr ha hAa hApa hw haw hwK
  have hcorr' := hcorr
  obtain ⟨-, -, -, -, -, -, hKp, -, -, -⟩ := hcorr'
  have hKA : K = A := hRI a w K ha hAa hA hcorr
  rw [hKA] at hKp
  obtain ⟨-, -, hKsn, -, -⟩ := hKp
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hAw).symm hAq, hKsn⟩

private theorem isComponent_subgroupOf_centralizer_conj {A : Subgroup B} {w d : B}
    (hd : d ∈ centralizer (A : Set B)) (hwA : A ≤ centralizer ({w} : Set B))
    (h : IsComponent (A.subgroupOf (centralizer ({w} : Set B)))) :
    A ≤ centralizer ({d * w * d⁻¹} : Set B) ∧
      IsComponent (A.subgroupOf (centralizer ({d * w * d⁻¹} : Set B))) := by
  let e : B ≃* B := MulAut.conj d
  have heinj : Function.Injective e.toMonoidHom := by simpa using e.injective
  have he : ∀ x : B, e x = d * x * d⁻¹ := fun x => by simp [e, MulAut.conj_apply]
  have hew : e w = d * w * d⁻¹ := he w
  let Cw : Subgroup B := centralizer ({w} : Set B)
  let Cw' : Subgroup B := centralizer ({e w} : Set B)
  let φ : ↥Cw ≃* ↥Cw' :=
    (Cw.equivMapOfInjective e.toMonoidHom heinj).trans
      (MulEquiv.subgroupCongr (centralizer_singleton_map e w))
  have hfix : ∀ x ∈ A, d * x * d⁻¹ = x := by
    intro x hx
    rw [← Subgroup.mem_centralizer_iff.mp hd x hx]
    group
  have hAw' : A ≤ Cw' := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxw : Commute x w :=
      (commute_iff_eq x w).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hwA hx))
    have hxd : Commute x d := (commute_iff_eq x d).mpr (by
      have h := congrArg (fun y => y * d) (hfix x hx)
      simpa [mul_assoc] using h.symm)
    have hxdw : Commute x (d * w * d⁻¹) :=
      (Commute.mul_right hxd hxw).mul_right hxd.inv_right
    rw [hew]
    exact hxdw.eq
  have hφval : ∀ x : ↥Cw, (φ x : B) = e (x : B) := by
    intro x
    change ((MulEquiv.subgroupCongr (centralizer_singleton_map e w))
      (Cw.equivMapOfInjective e.toMonoidHom heinj x) : B) = e (x : B)
    rw [MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have hmap : (A.subgroupOf Cw).map φ.toMonoidHom = A.subgroupOf Cw' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxA : (x : B) ∈ A := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      change (φ x : B) ∈ A
      rw [hφval x, he (x : B), hfix (x : B) hxA]
      exact hxA
    · intro hy
      have hyA : (y : B) ∈ A := Subgroup.mem_subgroupOf.mp hy
      have hyCw : (y : B) ∈ Cw := hwA hyA
      refine ⟨⟨(y : B), hyCw⟩, Subgroup.mem_subgroupOf.mpr hyA, ?_⟩
      apply Subtype.ext
      change (φ ⟨(y : B), hyCw⟩ : B) = (y : B)
      rw [hφval ⟨(y : B), hyCw⟩, he (y : B), hfix (y : B) hyA]
  obtain ⟨hq0, hsn0⟩ := h
  have hq : IsQuasisimple ↥(A.subgroupOf Cw') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hwA).trans
        (Subgroup.subgroupOfEquivOfLe hAw').symm) hq0
  have hsn : (A.subgroupOf Cw').IsSubnormal := by
    have h1 := Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hsn0
    rwa [hmap] at h1
  refine ⟨?_, ?_⟩
  · rwa [← hew]
  · rw [← hew]
    exact ⟨hq, hsn⟩

theorem isComponent_centralizer_of_relativeIdentity {A : Subgroup B}
    (hRI : ∀ (a b : B) (K : Subgroup B), orderOf a = 2 → A ≤ centralizer ({a} : Set B) →
      IsComponent (A.subgroupOf (centralizer ({a} : Set B))) → GrSLit.GSWeakCorr a A b K →
        K = A)
    {a : B} (ha : orderOf a = 2) (hAa : A ≤ centralizer ({a} : Set B))
    (hA : IsComponent (A.subgroupOf (centralizer ({a} : Set B))))
    {v : B} (hv : orderOf v = 2) (hvA : A ≤ centralizer ({v} : Set B)) :
    IsComponent (A.subgroupOf (centralizer ({v} : Set B))) := by
  classical
  let C : Subgroup B := centralizer (A : Set B)
  have haC : a ∈ C := by
    change a ∈ centralizer (A : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAa hx)
  have hvC : v ∈ C := by
    change v ∈ centralizer (A : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hvA hx)
  have haC2 : orderOf (⟨a, haC⟩ : C) = 2 :=
    (Subgroup.orderOf_coe (⟨a, haC⟩ : C)).symm.trans ha
  have h2a : IsPGroup 2 (Subgroup.zpowers (⟨a, haC⟩ : C)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, haC2, pow_one]
  obtain ⟨S, hSa⟩ := h2a.exists_le_sylow
  have haS : (⟨a, haC⟩ : C) ∈ (S : Subgroup C) := hSa (Subgroup.mem_zpowers _)
  have hSne : (S : Subgroup C) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨a, haC⟩ : C) ∈ (⊥ : Subgroup C) := by
      rw [← hbot]
      exact haS
    have h1 : (⟨a, haC⟩ : C) = 1 := by simpa using hmem
    rw [h1, orderOf_one] at haC2
    norm_num at haC2
  have hSnt : Nontrivial (S : Subgroup C) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup C)).mpr hSne
  letI : Nontrivial (S : Subgroup C) := hSnt
  have hS2 : IsPGroup 2 (S : Subgroup C) := S.isPGroup'
  have hZnt : Nontrivial ↥(Subgroup.center (S : Subgroup C)) := hS2.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center (S : Subgroup C)) := hS2.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
  have h2Z : 2 ∣ Nat.card (Subgroup.center (S : Subgroup C)) := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨zC, hzC⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (S : Subgroup C))) 2 h2Z
  let zS : (S : Subgroup C) := (zC : Subgroup.center (S : Subgroup C))
  let z : C := (zS : C)
  have hzmem : zS ∈ Subgroup.center (S : Subgroup C) := zC.2
  have hz2 : orderOf (z : B) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzC]
  have haz : a * (z : B) = (z : B) * a := by
    have h := Subgroup.mem_center_iff.mp hzmem ⟨⟨a, haC⟩, haS⟩
    exact congrArg (fun x : (S : Subgroup C) => ((x : C) : B)) h
  have hAz : A ≤ centralizer ({(z : B)} : Set B) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp z.property x hx
  have hAzComp : IsComponent (A.subgroupOf (centralizer ({(z : B)} : Set B))) :=
    isComponent_subgroupOf_centralizer_of_commute hRI ha hz2 haz hAa hA hAz
  have hSyl : ∃ P : Sylow 2 C,
      (P : Subgroup C) = ((S : Subgroup C).map C.subtype).subgroupOf C := by
    refine ⟨S, ?_⟩
    rw [← Subgroup.comap_subtype]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective (S : Subgroup C)).symm
  have h2v : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv, pow_one]
  obtain ⟨c, hcC, hcS⟩ :=
    CFSG.ComponentClassification.UnbalancedLayer.exists_conjugate_le_of_sylow
      hSyl (Subgroup.zpowers_le.mpr hvC) h2v
  have hcv : c⁻¹ * v * c ∈ conjugate (Subgroup.zpowers v) c := by
    rw [conjugate, Subgroup.mem_map]
    exact ⟨v, Subgroup.mem_zpowers v, by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨wC, hwS, hwval⟩ := Subgroup.mem_map.mp (hcS hcv)
  let w : B := c⁻¹ * v * c
  have hwval' : (wC : B) = w := hwval
  have hwC : w ∈ C := hwval' ▸ wC.2
  have hwS' : (⟨w, hwC⟩ : C) ∈ (S : Subgroup C) := by
    have hwCeq : wC = ⟨w, hwC⟩ := Subtype.ext hwval'
    rwa [hwCeq] at hwS
  have hw2 : orderOf w = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) v
    simpa [w, MulAut.conj_apply, mul_assoc] using h.trans hv
  have hzw : (z : B) * w = w * (z : B) := by
    have h := Subgroup.mem_center_iff.mp hzmem ⟨⟨w, hwC⟩, hwS'⟩
    exact (congrArg (fun x : (S : Subgroup C) => ((x : C) : B)) h).symm
  have hAw : A ≤ centralizer ({w} : Set B) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hwC x hx
  have hAwComp : IsComponent (A.subgroupOf (centralizer ({w} : Set B))) :=
    isComponent_subgroupOf_centralizer_of_commute hRI hz2 hw2 hzw hAz hAzComp hAw
  have hfin := isComponent_subgroupOf_centralizer_conj (A := A) (w := w) (d := c)
    hcC hAw hAwComp
  have hcw : c * w * c⁻¹ = v := by
    rw [show w = c⁻¹ * v * c from rfl]
    group
  rw [hcw] at hfin
  exact hfin.2

end CFSG.ComponentClassification.FooteMarked
