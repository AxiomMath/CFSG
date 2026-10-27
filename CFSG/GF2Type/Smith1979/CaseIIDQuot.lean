module

public import CFSG.GF2Type.Smith1979.CaseIIDCrit
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GF2Type.Smith1979.Case2

open scoped commutatorElement

section Quot

variable {M : Type*} [Group M] (E : Subgroup M) [E.Normal]

@[expose] noncomputable def inducedAut (t : M) : MulAut (E ⧸ Subgroup.center E) :=
  QuotientGroup.congr (Subgroup.center E) (Subgroup.center E) (MulAut.conjNormal t)
    (Subgroup.map_center_eq _)

theorem inducedAut_mk (t : M) (e : E) :
    inducedAut E t (QuotientGroup.mk e) = QuotientGroup.mk (MulAut.conjNormal t e) :=
  rfl

@[expose] def embedQuot (R : Subgroup M) (hRE : R ≤ E) : R →* E ⧸ Subgroup.center E :=
  (QuotientGroup.mk' (Subgroup.center E)).comp (Subgroup.inclusion hRE)

theorem embedQuot_apply (R : Subgroup M) (hRE : R ≤ E) (r : R) :
    embedQuot E R hRE r = QuotientGroup.mk (⟨r.1, hRE r.2⟩ : E) :=
  rfl

variable {E}

theorem conjNormal_conjNormal {t : M} (htt : t * t = 1) (e : E) :
    MulAut.conjNormal t (MulAut.conjNormal t e) = e := by
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply]
  calc t * (t * (e : M) * t⁻¹) * t⁻¹ = (t * t) * (e : M) * (t * t)⁻¹ := by group
    _ = e := by rw [htt]; group

theorem inducedAut_mul_self {t : M} (htt : t * t = 1) : inducedAut E t * inducedAut E t = 1 := by
  ext x
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
  show inducedAut E t (inducedAut E t (QuotientGroup.mk e)) = QuotientGroup.mk e
  rw [inducedAut_mk, inducedAut_mk, conjNormal_conjNormal htt]

theorem commutatorElement_mul_mul {H : Type*} [Group H] {r r' z z' : H} (h2 : z * r' = r' * z)
    (h3 : z' * r = r * z') (h5 : z * z' = z' * z) : ⁅r * z, r' * z'⁆ = ⁅r, r'⁆ := by
  have h3' : z' * r⁻¹ = r⁻¹ * z' := (Commute.inv_right (show Commute z' r from h3)).eq
  calc ⁅r * z, r' * z'⁆ = r * (z * r') * z' * z⁻¹ * r⁻¹ * z'⁻¹ * r'⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = r * (r' * z) * z' * z⁻¹ * r⁻¹ * z'⁻¹ * r'⁻¹ := by rw [h2]
    _ = r * r' * (z * z' * z⁻¹) * r⁻¹ * z'⁻¹ * r'⁻¹ := by group
    _ = r * r' * z' * r⁻¹ * z'⁻¹ * r'⁻¹ := by rw [h5]; group
    _ = r * r' * (z' * r⁻¹) * z'⁻¹ * r'⁻¹ := by group
    _ = r * r' * (r⁻¹ * z') * z'⁻¹ * r'⁻¹ := by rw [h3']
    _ = ⁅r, r'⁆ := by simp only [commutatorElement_def]; group

variable {t : M} {R : Subgroup M}

theorem embedQuot_injective (hRE : R ≤ E)
    (hRZ : ∀ r : R, (⟨r.1, hRE r.2⟩ : E) ∈ Subgroup.center E → r = 1) :
    Function.Injective (embedQuot E R hRE) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  exact hRZ r ((QuotientGroup.eq_one_iff _).mp hr)

theorem inducedAut_fix_iff (htt : t * t = 1) (hRE : R ≤ E)
    (hZ : ∀ z ∈ Subgroup.center E, z ^ 3 = 1)
    (hC1 : ∀ e : E, t * (e : M) * t⁻¹ = e → (e : M) ∈ R) (hC2 : ∀ r ∈ R, t * r * t⁻¹ = r)
    (x : E ⧸ Subgroup.center E) :
    inducedAut E t x = x ↔ x ∈ (embedQuot E R hRE).range := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    rw [inducedAut_mk] at h
    set φ : MulAut E := MulAut.conjNormal t
    have hφ2 : ∀ y : E, φ (φ y) = y := conjNormal_conjNormal htt
    obtain ⟨z, hz, h1⟩ : ∃ z ∈ Subgroup.center E, φ e = e * z :=
      ⟨e⁻¹ * φ e, QuotientGroup.eq.mp h.symm, by group⟩
    have h2 : z * φ z = 1 := by
      have h := hφ2 e
      rw [h1, map_mul, h1, mul_assoc] at h
      simpa using h
    have h3 : φ z = z⁻¹ := eq_inv_of_mul_eq_one_right h2
    have hz3 : z * z = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc z * z * z = z ^ 3 := (pow_three' z).symm
        _ = 1 := hZ z hz
    have h4 : φ (e * z⁻¹) = e * z⁻¹ := by
      rw [map_mul, map_inv, h3, inv_inv, h1, mul_assoc, hz3]
    have h5 : t * ((e * z⁻¹ : E) : M) * t⁻¹ = ((e * z⁻¹ : E) : M) :=
      congrArg Subtype.val h4
    refine ⟨⟨_, hC1 (e * z⁻¹) h5⟩, ?_⟩
    rw [embedQuot_apply]
    show QuotientGroup.mk (e * z⁻¹) = QuotientGroup.mk e
    refine QuotientGroup.eq.mpr ?_
    have : (e * z⁻¹)⁻¹ * e = z := by group
    rw [this]
    exact hz
  · rintro ⟨r, rfl⟩
    rw [embedQuot_apply, inducedAut_mk]
    congr 1
    exact Subtype.ext (by simpa [MulAut.conjNormal_apply] using hC2 r.1 r.2)

theorem inducedAut_ne_conj (htt : t * t = 1) (hRE : R ≤ E)
    (hZ : ∀ z ∈ Subgroup.center E, z ^ 3 = 1)
    (hC1 : ∀ e : E, t * (e : M) * t⁻¹ = e → (e : M) ∈ R) (hC2 : ∀ r ∈ R, t * r * t⁻¹ = r)
    (hperf : ⁅E, E⁆ = E) (hRc : ∀ r ∈ R, (∀ s ∈ R, s * r = r * s) → r = 1)
    (hRZ : ∀ r : R, (⟨r.1, hRE r.2⟩ : E) ∈ Subgroup.center E → r = 1) (hER : ¬ E ≤ R)
    (x : E ⧸ Subgroup.center E) : inducedAut E t ≠ MulAut.conj x := by
  intro hx
  have hinj := embedQuot_injective hRE hRZ
  have hfix := inducedAut_fix_iff htt hRE hZ hC1 hC2
  have hxfix : inducedAut E t x = x := by
    rw [hx, MulAut.conj_apply]
    group
  obtain ⟨r, hr⟩ := (hfix x).mp hxfix
  have hrc : ∀ s ∈ R, s * (r : M) = (r : M) * s := by
    intro s hs
    have h1 : inducedAut E t (embedQuot E R hRE ⟨s, hs⟩) = embedQuot E R hRE ⟨s, hs⟩ :=
      (hfix _).mpr ⟨_, rfl⟩
    rw [hx, MulAut.conj_apply, ← hr] at h1
    have h2 : embedQuot E R hRE (r * ⟨s, hs⟩) = embedQuot E R hRE (⟨s, hs⟩ * r) := by
      rw [map_mul, map_mul]
      exact mul_inv_eq_iff_eq_mul.mp h1
    exact (congrArg Subtype.val (hinj h2)).symm
  have hr1 : r = 1 := Subtype.ext (hRc r.1 r.2 hrc)
  have hx1 : x = 1 := by rw [← hr, hr1, map_one]
  have hσ1 : ∀ y, inducedAut E t y = y := fun y => by
    rw [hx, hx1, MulAut.conj_apply]
    group
  apply hER
  have hcomm : ⁅E, E⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨ra, hra⟩ := (hfix (QuotientGroup.mk ⟨a, ha⟩)).mp (hσ1 _)
    obtain ⟨rb, hrb⟩ := (hfix (QuotientGroup.mk ⟨b, hb⟩)).mp (hσ1 _)
    rw [embedQuot_apply] at hra hrb
    have hza := QuotientGroup.eq.mp hra
    have hzb := QuotientGroup.eq.mp hrb
    set RA : E := ⟨ra.1, hRE ra.2⟩
    set RB : E := ⟨rb.1, hRE rb.2⟩
    set A : E := ⟨a, ha⟩
    set B : E := ⟨b, hb⟩
    obtain ⟨ZA, hZA, hA⟩ : ∃ ZA ∈ Subgroup.center E, A = RA * ZA := ⟨RA⁻¹ * A, hza, by group⟩
    obtain ⟨ZB, hZB, hB⟩ : ∃ ZB ∈ Subgroup.center E, B = RB * ZB := ⟨RB⁻¹ * B, hzb, by group⟩
    have hAB : ⁅A, B⁆ = ⁅RA, RB⁆ := by
      rw [hA, hB]
      exact commutatorElement_mul_mul (Subgroup.mem_center_iff.mp hZA RB).symm
        (Subgroup.mem_center_iff.mp hZB RA).symm (Subgroup.mem_center_iff.mp hZB ZA)
    have hab : ⁅a, b⁆ = ⁅ra.1, rb.1⁆ :=
      calc ⁅a, b⁆ = E.subtype ⁅A, B⁆ := (map_commutatorElement E.subtype A B).symm
        _ = E.subtype ⁅RA, RB⁆ := by rw [hAB]
        _ = ⁅ra.1, rb.1⁆ := map_commutatorElement E.subtype RA RB
    rw [hab, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ra.2 rb.2) (inv_mem ra.2)) (inv_mem rb.2)
  rw [hperf] at hcomm
  exact hcomm

end Quot

end CFSG.GF2Type.Smith1979.Case2
