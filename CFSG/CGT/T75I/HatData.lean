module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.T75I.AltRank

public section

namespace CFSG.CGT.T75I

open Equiv Equiv.Perm CFSG.Open CFSG.CGT.Timmesfeld75

structure HatData (k : ℕ) {Y : Type} [Group Y] (Z : Subgroup Y)
    (f : Y →* alternatingGroup (Fin k)) : Prop where
  central : Z ≤ Subgroup.center Y
  card_dvd : Nat.card Z ∣ 3
  surj : Function.Surjective f
  ker_eq : f.ker = Z

theorem IsHatA.exists_data {k : ℕ} {Y : Type} [Group Y] (h : IsHatA k Y) :
    commutator Y = ⊤ ∧ ∃ (Z : Subgroup Y) (f : Y →* alternatingGroup (Fin k)), HatData k Z f := by
  obtain ⟨hperf, Z, hZc, hZcard, hZn, ⟨φ⟩⟩ := h
  refine ⟨hperf, Z, φ.toMonoidHom.comp (QuotientGroup.mk' Z), hZc, hZcard, ?_, ?_⟩
  · exact φ.surjective.comp (QuotientGroup.mk'_surjective Z)
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff φ φ.injective]
    exact QuotientGroup.eq_one_iff x

section Data

variable {k : ℕ} {Y : Type} [Group Y] {Z : Subgroup Y} {f : Y →* alternatingGroup (Fin k)}

theorem HatData.eq_one_of_mem_of_sq (h : HatData k Z f) {z : Y} (hz : z ∈ Z) (hz2 : z * z = 1) :
    z = 1 := by
  have hd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  have hd3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard Z hz).trans h.card_dvd
  have hd1 : orderOf z ∣ 1 := by
    have := Nat.dvd_gcd hd2 hd3
    simpa using this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd1)

theorem HatData.map_ne_one (h : HatData k Z f) {x : Y} (hx : x ≠ 1) (hx2 : x * x = 1) :
    f x ≠ 1 := by
  intro h1
  apply hx
  have hxZ : x ∈ Z := by rw [← h.ker_eq]; exact h1
  exact h.eq_one_of_mem_of_sq hxZ hx2

theorem HatData.exists_conj_of_involutions (hk : k = 6 ∨ k = 7) (h : HatData k Z f) {x y : Y}
    (hx : x ≠ 1) (hx2 : x * x = 1) (hy : y ≠ 1) (hy2 : y * y = 1) :
    ∃ g : Y, g * x * g⁻¹ = y := by
  have hk6 : 6 ≤ k := by omega
  have hk7 : k ≤ 7 := by omega
  have hfx2 : f x * f x = 1 := by rw [← map_mul, hx2, map_one]
  have hfy2 : f y * f y = 1 := by rw [← map_mul, hy2, map_one]
  have hfx : (f x : Perm (Fin k)) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val hfx2
  have hfy : (f y : Perm (Fin k)) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val hfy2
  have hfx1 : (f x : Perm (Fin k)) ≠ 1 := fun h1 => h.map_ne_one hx hx2 (Subtype.ext h1)
  have hfy1 : (f y : Perm (Fin k)) ≠ 1 := fun h1 => h.map_ne_one hy hy2 (Subtype.ext h1)
  obtain ⟨g, hgs, hg⟩ := exists_even_conj_of_even_involutions hk6 hk7 hfx hfx1
    (Equiv.Perm.mem_alternatingGroup.1 (f x).2) hfy hfy1
    (Equiv.Perm.mem_alternatingGroup.1 (f y).2)
  let g' : alternatingGroup (Fin k) := ⟨g, Equiv.Perm.mem_alternatingGroup.2 hgs⟩
  obtain ⟨γ, hγ⟩ := h.surj g'
  have hconj : f (γ * x * γ⁻¹) = f y := by
    rw [map_mul, map_mul, map_inv, hγ]
    exact Subtype.ext hg
  have hz : (y⁻¹ * (γ * x * γ⁻¹)) ∈ Z := by
    rw [← h.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
  set z := y⁻¹ * (γ * x * γ⁻¹) with hzdef
  have hcz : y * z = z * y := Subgroup.mem_center_iff.1 (h.central hz) y
  have hsq : (γ * x * γ⁻¹) * (γ * x * γ⁻¹) = 1 := by
    calc γ * x * γ⁻¹ * (γ * x * γ⁻¹) = γ * (x * x) * γ⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hw : γ * x * γ⁻¹ = y * z := by rw [hzdef, mul_inv_cancel_left]
  have hzz : z * z = 1 := by
    have h1 : (y * z) * (y * z) = 1 := by rw [← hw]; exact hsq
    calc z * z = (y * y) * (z * z) := by rw [hy2, one_mul]
      _ = y * (y * z) * z := by group
      _ = y * (z * y) * z := by rw [hcz]
      _ = (y * z) * (y * z) := by group
      _ = 1 := h1
  have hz1 : z = 1 := h.eq_one_of_mem_of_sq hz hzz
  exact ⟨γ, by rw [hw, hz1, mul_one]⟩

end Data

end CFSG.CGT.T75I
