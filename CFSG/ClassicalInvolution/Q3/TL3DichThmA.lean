module

public import CFSG.ClassicalInvolution.Q3.TL3DichPre
public import CFSG.ClassicalInvolution.Q3.Q3TLTLayer
public import CFSG.ClassicalInvolution.Q3.TL3DichKap

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem t_mul_t (hd : TightDatum R S t) : t * t = 1 := by
  rw [← pow_two, ← hd.order, pow_orderOf_eq_one]

omit [Finite Y] in
theorem t_inv (hd : TightDatum R S t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (t_mul_t hd)

omit [Finite Y] in
theorem mul_t_comm_of_sq {r : Y} (hr : r * r = t) : r * t = t * r := by
  rw [← hr]; group

omit [Finite Y] in
theorem TightDatum.mem_normalizer_R_of_comm (hd : TightDatum R S t) {g : Y} (hg : g * t = t * g) :
    g ∈ Subgroup.normalizer (R : Set Y) :=
  hd.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hg)

omit [Finite Y] in
theorem TightDatum.comm_mem (hd : TightDatum R S t) {g r : Y} (hg : g * t = t * g) (hr : r ∈ R) :
    g * r * g⁻¹ * r⁻¹ ∈ R := by
  have h1 : g * r * g⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hd.mem_normalizer_R_of_comm hg) r).mp hr
  exact R.mul_mem h1 (R.inv_mem hr)

theorem comm_of_ne {A B : Subgroup Y} (hA : CFSG.IsComponent A) (hB : CFSG.IsComponent B)
    (hne : A ≠ B) {x y : Y} (hx : x ∈ A) (hy : y ∈ B) : x * y = y * x :=
  AscThmA.mul_comm_of_ne hA hB hne hx hy

theorem TightDatum.conjSub_t_eq (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) : conjSub t A = A := by
  by_contra htA
  have ht1 := t_mul_t hd
  have htinv := t_inv hd
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := hd.exists_S₀_pair hq8
  have key : ∀ r : Y, r * r = t → conjSub r A ≠ A := by
    intro r hrr heq
    apply htA
    rw [← hrr, conjSub_mul, heq, heq]
  have hex : ∃ r ∈ (S : Subgroup R).map R.subtype, conjSub r A ≠ A ∧ conjSub r A ≠ conjSub t A := by
    by_contra hno
    push Not at hno
    have e1 : conjSub r₁ A = conjSub t A := hno r₁ hr₁ (key r₁ h1)
    have e2 : conjSub r₂ A = conjSub t A := hno r₂ hr₂ (key r₂ h2)
    have hr12 : r₁ * r₂ ∈ (S : Subgroup R).map R.subtype := Subgroup.mul_mem _ hr₁ hr₂
    have e12 : conjSub (r₁ * r₂) A = conjSub t A := hno _ hr12 (key _ h12)
    apply htA
    have hr1t : r₁ * t = t * r₁ := mul_t_comm_of_sq h1
    symm
    calc A = conjSub (t * t) A := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub r₁ A) := by rw [conjSub_mul, e1]
      _ = conjSub (r₁ * t) A := by rw [← conjSub_mul, hr1t]
      _ = conjSub (r₁ * r₂) A := by rw [conjSub_mul, conjSub_mul, e2]
      _ = conjSub t A := e12
  obtain ⟨r, hrS, hrA, hrtA⟩ := hex
  have hrR : r ∈ R := hd.S₀_le hrS
  have hrsq : r * t = t * r := by
    rcases hd.S₀_cases hq8 hrS with h | h | h
    · rw [h]; group
    · rw [h]
    · exact mul_t_comm_of_sq h
  have hAt : CFSG.IsComponent (conjSub t A) := AscThmA.isComponent_conjSub hA t
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hArt : CFSG.IsComponent (conjSub (r * t) A) := AscThmA.isComponent_conjSub hA (r * t)
  have hrtne : conjSub (r * t) A ≠ A := by
    intro heq
    apply hrtA
    have h' : conjSub t (conjSub r A) = A := by rw [← conjSub_mul, ← hrsq, heq]
    calc conjSub r A = conjSub (t * t) (conjSub r A) := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub t (conjSub r A)) := conjSub_mul _ _ _
      _ = conjSub t A := by rw [h']
  refine TightA.false_of_solvable_covers hA.1 hd.isSolvable (W := R) fun x hx => ?_
  set d : Y := x * (t * x * t⁻¹) with hd_def
  have hxt : t * x * t⁻¹ ∈ conjSub t A := conj_mem_conjSub hx
  have hdt : d * t = t * d := by
    have hc : (t * x * t⁻¹) * x = x * (t * x * t⁻¹) := (comm_of_ne hAt hA htA hxt hx)
    rw [hd_def]
    calc x * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [hc]
      _ = t * (x * (t * x * t⁻¹)) := by rw [htinv]; group
  refine ⟨d * r * d⁻¹ * r⁻¹, hd.comm_mem hdt hrR, fun a ha => ?_⟩
  have hu1 : r * (t * x⁻¹ * t⁻¹) * r⁻¹ ∈ conjSub (r * t) A := by
    have := conj_mem_conjSub (n := r * t) (A.inv_mem hx)
    simpa [mul_assoc] using this
  have hu2 : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
  have hc1 := comm_of_ne hArt hA hrtne hu1 ha
  have hc2 := comm_of_ne hAr hA hrA hu2 ha
  have hc3 := comm_of_ne hAt hA htA hxt ha
  have e : d * r * d⁻¹ * r⁻¹ =
      x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) := by
    rw [hd_def]; group
  rw [e]
  calc x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) * a *
        (x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹))⁻¹
      = x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * ((r * x⁻¹ * r⁻¹) * a) *
          (r * x⁻¹ * r⁻¹)⁻¹ * (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        group
    _ = x * (t * x * t⁻¹) * ((r * (t * x⁻¹ * t⁻¹) * r⁻¹) * a) *
          (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc2]; group
    _ = x * ((t * x * t⁻¹) * a) * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc1]; group
    _ = x * a * x⁻¹ := by
        rw [hc3]; group

theorem TightDatum.not_centralizes (hd : TightDatum R S t) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrA : conjSub r A ≠ A) (htA : ∀ x ∈ A, x * t = t * x) : False := by
  have hrR : r ∈ R := hd.S₀_le hrS
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  refine TightA.false_of_solvable_covers hA.1 hd.isSolvable (W := R) fun x hx => ?_
  refine ⟨x * r * x⁻¹ * r⁻¹, hd.comm_mem (htA x hx) hrR, fun a ha => ?_⟩
  have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
  have hc := comm_of_ne hAr hA hrA hu ha
  calc x * r * x⁻¹ * r⁻¹ * a * (x * r * x⁻¹ * r⁻¹)⁻¹
      = x * ((r * x⁻¹ * r⁻¹) * a) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by group
    _ = x * a * x⁻¹ := by rw [hc]; group

end CFSG.ClassicalInvolution.Q3
