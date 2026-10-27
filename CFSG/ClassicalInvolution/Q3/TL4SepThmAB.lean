module

public import CFSG.ClassicalInvolution.Q3.TL4SepThmA
public import CFSG.ClassicalInvolution.Q3.TL3DichThmA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem comm_mul_mul_eq {G : Type*} [Group G] {a b c d : G} (hab : Commute a b)
    (had : Commute a d) (hcb : Commute c b) (hcd : Commute c d) :
    a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * c * a⁻¹ * c⁻¹ * (b * d * b⁻¹ * d⁻¹) := by
  have h1 : a * b * (c * d) = a * c * (b * d) := hcb.symm.mul_mul_mul_comm a d
  have h2 : (a * b)⁻¹ * (c * d)⁻¹ = b⁻¹ * d⁻¹ * (a⁻¹ * c⁻¹) := by
    rw [mul_inv_rev, mul_inv_rev]
    exact had.inv_inv.mul_mul_mul_comm b⁻¹ c⁻¹
  have hb : Commute b (a⁻¹ * c⁻¹) := hab.symm.inv_right.mul_right hcb.symm.inv_right
  have hd : Commute d (a⁻¹ * c⁻¹) := had.symm.inv_right.mul_right hcd.symm.inv_right
  have hX : Commute (b * d * b⁻¹ * d⁻¹) (a⁻¹ * c⁻¹) :=
    ((hb.mul_left hd).mul_left hb.inv_left).mul_left hd.inv_left
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹
      = (a * b * (c * d)) * ((a * b)⁻¹ * (c * d)⁻¹) := by group
    _ = a * c * (b * d) * (b⁻¹ * d⁻¹ * (a⁻¹ * c⁻¹)) := by rw [h1, h2]
    _ = a * c * ((b * d * b⁻¹ * d⁻¹) * (a⁻¹ * c⁻¹)) := by group
    _ = a * c * ((a⁻¹ * c⁻¹) * (b * d * b⁻¹ * d⁻¹)) := by rw [hX.eq]
    _ = a * c * a⁻¹ * c⁻¹ * (b * d * b⁻¹ * d⁻¹) := by group

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem odd_orderOf_of_not_mem (hd : TightDatum R S t) {H : Subgroup Y} (htH : t ∉ H) {c : Y}
    (hcR : c ∈ R) (hcH : c ∈ H) : Odd (orderOf c) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h2 := orderOf_pow_orderOf_div (orderOf_pos c).ne' (even_iff_two_dvd.mp hev)
  have := hd.eq_of_orderOf_eq_two (R.pow_mem hcR _) h2
  exact htH (this ▸ H.pow_mem hcH _)

theorem conjSub_t_eq_R (hd : TightDatum R S t) {A : Subgroup Y} (hA : CFSG.IsComponent A) :
    conjSub t A = A := by
  by_contra htA
  have ht1 := t_mul_t hd
  have htinv := t_inv hd
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := exists_S₀_pair_R hd
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
    have hr1t : r₁ * t = t * r₁ := mul_t_comm_of_mem_R hd (hd.S₀_le hr₁)
    symm
    calc A = conjSub (t * t) A := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub r₁ A) := by rw [conjSub_mul, e1]
      _ = conjSub (r₁ * t) A := by rw [← conjSub_mul, hr1t]
      _ = conjSub (r₁ * r₂) A := by rw [conjSub_mul, conjSub_mul, e2]
      _ = conjSub t A := e12
  obtain ⟨r, hrS, hrA, hrtA⟩ := hex
  have hrR : r ∈ R := hd.S₀_le hrS
  have hrsq : r * t = t * r := mul_t_comm_of_mem_R hd hrR
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

end CFSG.ClassicalInvolution.Q3.TL4
