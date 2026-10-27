module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.ThreeLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section Kernel

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normal_of_le_center {Z : Subgroup X} (hZ : Z ≤ center X) : Z.Normal :=
  ⟨fun n hn g => by
    have h := mem_center_iff.1 (hZ hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩

theorem conj_eq_of_mod_zpowers {d : ThreeLocalData X} {o : X}
    (h : (d.t * o * d.t⁻¹)⁻¹ * o ∈ zpowers d.r) : d.t * o * d.t⁻¹ = o := by
  have ht2 : d.t * d.t = 1 := by rw [← pow_two, ← d.t_ord, pow_orderOf_eq_one]
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  set z := (d.t * o * d.t⁻¹)⁻¹ * o with hz
  have hzc : z ∈ center X := (zpowers_le.2 d.r_central) h
  have hz3 : z ^ 3 = 1 := by
    have h3 : orderOf z ∣ 3 := d.r_ord ▸ orderOf_dvd_of_mem_zpowers h
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hw : d.t * o * d.t⁻¹ = o * z := by
    have h1 : o = (d.t * o * d.t⁻¹) * z := by rw [hz]; group
    have h2 : d.t * o * d.t⁻¹ = (d.t * (d.t * o * d.t⁻¹) * d.t⁻¹) * (d.t * z * d.t⁻¹) := by
      conv_lhs => rw [h1]
      group
    have h3 : d.t * (d.t * o * d.t⁻¹) * d.t⁻¹ = o := by
      rw [htinv]; calc d.t * (d.t * o * d.t) * d.t = (d.t * d.t) * o * (d.t * d.t) := by group
        _ = o := by rw [ht2]; group
    have h4 : d.t * z * d.t⁻¹ = z := by
      rw [mem_center_iff.1 hzc d.t, mul_inv_cancel_right]
    rw [h2, h3, h4]
  have hzz : z * z = 1 := by
    have h1 : o = (d.t * o * d.t⁻¹) * z := by rw [hz]; group
    rw [hw] at h1
    have : o * (z * z) = o * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel this
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hzz]; simp
  rw [hw, hz1, mul_one]


theorem exists_kernel (d : ThreeLocalData X) :
    ∃ K : Subgroup X, K.Normal ∧ CFSG.oddCore X ≤ K ∧ (∀ c : X, ⁅c, d.t⁆ ∈ K) ∧
      ⁅K, K⁆ ≤ centralizer (CFSG.oddCore X : Set X) := by
  set O := CFSG.oddCore X with hO
  set Z : Subgroup X := zpowers d.r with hZ
  have hZc : Z ≤ center X := zpowers_le.2 d.r_central
  have : Z.Normal := normal_of_le_center hZc
  set ρ : X →* X ⧸ Z := QuotientGroup.mk' Z with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective Z
  set Ob : Subgroup (X ⧸ Z) := O.map ρ with hOb
  have : Ob.Normal := Subgroup.Normal.map inferInstance ρ hρs
  have ht2 : d.t * d.t = 1 := by rw [← pow_two, ← d.t_ord, pow_orderOf_eq_one]
  have htb2 : ρ d.t * ρ d.t = 1 := by rw [← map_mul, ht2, map_one]
  have htbinv : (ρ d.t)⁻¹ = ρ d.t := inv_eq_of_mul_eq_one_right htb2
  have hA : ∀ a ∈ Ob, ρ d.t * a * (ρ d.t)⁻¹ ∈ Ob := fun a ha =>
    Subgroup.Normal.conj_mem inferInstance a ha (ρ d.t)
  have hfix : ∀ a ∈ Ob, ρ d.t * a * (ρ d.t)⁻¹ = a → a = 1 := by
    rintro _ ⟨o, ho, rfl⟩ h
    have h1 : ρ (d.t * o * d.t⁻¹) = ρ o := by simpa [map_mul, map_inv] using h
    have h2 : (d.t * o * d.t⁻¹)⁻¹ * o ∈ Z := (QuotientGroup.eq).1 h1
    have h3 : d.t * o * d.t⁻¹ = o := conj_eq_of_mod_zpowers h2
    exact (QuotientGroup.eq_one_iff o).2 (d.cen_odd o ho h3)
  have hinv : ∀ a ∈ Ob, ρ d.t * a * (ρ d.t)⁻¹ = a⁻¹ := inv_of_fpf htb2 hA hfix
  have hcomm : ∀ a ∈ Ob, ∀ b ∈ Ob, a * b = b * a := comm_of_fpf htb2 hA hfix
  have hmemK : ∀ x : X, ρ x ∈ centralizer (Ob : Set (X ⧸ Z)) ↔ ∀ o ∈ O, ⁅x, o⁆ ∈ Z := by
    intro x
    rw [mem_centralizer_iff]
    constructor
    · intro h o ho
      have e : ρ ⁅x, o⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (h (ρ o) (Subgroup.mem_map_of_mem ρ ho)).symm
      exact (QuotientGroup.eq_one_iff _).1 e
    · intro h b hb
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hb
      have e : ρ ⁅x, o⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (h o ho)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at e
      exact e.symm
  refine ⟨(centralizer (Ob : Set (X ⧸ Z))).comap ρ, inferInstance, ?_, ?_, ?_⟩
  · intro o ho
    rw [Subgroup.mem_comap, mem_centralizer_iff]
    intro b hb
    exact hcomm b hb (ρ o) (Subgroup.mem_map_of_mem ρ ho)
  · intro c
    rw [Subgroup.mem_comap, mem_centralizer_iff]
    intro b hb
    have key : ∀ a ∈ Ob, ρ ⁅c, d.t⁆ * a * (ρ ⁅c, d.t⁆)⁻¹ = a := by
      intro a ha
      have hb' : (ρ c)⁻¹ * a⁻¹ * (ρ c) ∈ Ob := by
        have := Subgroup.Normal.conj_mem (inferInstance : Ob.Normal) a⁻¹ (Ob.inv_mem ha) (ρ c)⁻¹
        simpa using this
      have h1 : ρ d.t * a * ρ d.t = a⁻¹ := by
        have := hinv a ha
        rwa [htbinv] at this
      have h2 : ρ d.t * ((ρ c)⁻¹ * a⁻¹ * ρ c) * ρ d.t = (ρ c)⁻¹ * a * ρ c := by
        have := hinv _ hb'
        rw [htbinv] at this
        rw [this]
        group
      have e1 : ρ ⁅c, d.t⁆ = ρ c * ρ d.t * (ρ c)⁻¹ * ρ d.t := by
        simp only [commutatorElement_def, map_mul, map_inv, htbinv]
      have e2 : (ρ ⁅c, d.t⁆)⁻¹ = ρ d.t * ρ c * ρ d.t * (ρ c)⁻¹ := by
        rw [e1, mul_inv_rev, mul_inv_rev, mul_inv_rev, htbinv, inv_inv]
        group
      rw [e2]
      calc ρ ⁅c, d.t⁆ * a * (ρ d.t * ρ c * ρ d.t * (ρ c)⁻¹)
          = ρ c * ρ d.t * (ρ c)⁻¹ * (ρ d.t * a * ρ d.t) * ρ c * ρ d.t * (ρ c)⁻¹ := by
            rw [e1]; group
        _ = ρ c * (ρ d.t * ((ρ c)⁻¹ * a⁻¹ * ρ c) * ρ d.t) * (ρ c)⁻¹ := by rw [h1]; group
        _ = a := by rw [h2]; group
    have := key b hb
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · apply commutator_le_centralizer_of_central hZc
    intro x hx o ho
    exact (hmemK x).1 (by simpa [mem_centralizer_iff] using hx) o ho

end Kernel

end CFSG.EvenSporadicStandard.RuStd.S2.Close
