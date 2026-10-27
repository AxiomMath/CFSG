module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.ComponentClassification.GSThmB.X11.Sym

open Equiv Subgroup

theorem factorial_ne (k : ℕ) :
    k.factorial ≠ 25920 ∧ k.factorial ≠ 51840 ∧ k.factorial ≠ 103680 := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> decide
  · have h9 : Nat.factorial 9 ≤ k.factorial := Nat.factorial_le hk
    have : Nat.factorial 9 = 362880 := by decide
    omega

theorem card_le_two_of_inf_eq_bot {Z : Type*} [Fintype Z] [DecidableEq Z] {Y : Subgroup (Perm Z)}
    (h : Y ⊓ alternatingGroup Z = ⊥) : Nat.card Y ≤ 2 := by
  have hinj : Function.Injective (Perm.sign.comp Y.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    have : (y : Perm Z) ∈ Y ⊓ alternatingGroup Z := ⟨y.2, hy⟩
    rw [h, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext this)
  calc Nat.card Y ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

theorem false_of_subnormal_perm {Z : Type*} [Fintype Z] [DecidableEq Z] {Y : Subgroup (Perm Z)}
    (hY : Y.IsSubnormal) {Q : Type*} [Group Q] [Finite Q] (φ : ↥Y →* Q)
    (hφ : Function.Surjective φ) (hQ : Nat.card Q = 25920) : False := by
  have hQY : Nat.card Q ≤ Nat.card Y := Nat.card_le_card_of_surjective φ hφ
  have hYk : Nat.card Y ∣ (Fintype.card Z).factorial := by
    rw [← Fintype.card_perm, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card Y
  rcases Nat.lt_or_ge (Fintype.card Z) 5 with hk | hk
  · have h1 : (Fintype.card Z).factorial ≤ Nat.factorial 4 :=
      Nat.factorial_le (by omega)
    have h2 := Nat.le_of_dvd (Nat.factorial_pos _) hYk
    have : Nat.factorial 4 = 24 := by decide
    omega
  have : Nontrivial Z := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : IsSimpleGroup (alternatingGroup Z) := alternatingGroup.isSimpleGroup
    (by rw [Nat.card_eq_fintype_card]; exact hk)
  rcases (hY.subgroupOf (K := alternatingGroup Z)).eq_bot_or_top_of_isSimpleGroup hA with h | h
  · have h1 : Y ⊓ alternatingGroup Z = ⊥ := by
      rw [← subgroupOf_map_subtype, h, Subgroup.map_bot]
    have := card_le_two_of_inf_eq_bot h1
    omega
  · have hAY : alternatingGroup Z ≤ Y := by
      rw [← subgroupOf_eq_top]
      exact h
    set R : Subgroup (Perm Z) := φ.ker.map Y.subtype with hR
    have hRY : R ≤ Y := map_subtype_le _
    have hcardR : Nat.card R = Nat.card φ.ker :=
      Subgroup.card_map_of_injective Y.subtype_injective
    have hYQ : Nat.card Y = Nat.card Q * Nat.card R := by
      rw [hcardR, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
      exact φ.ker.card_eq_card_quotient_mul_card_subgroup
    have hRn : ((R ⊓ alternatingGroup Z).subgroupOf (alternatingGroup Z)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [mem_subgroupOf, mem_inf] at hx ⊢
      refine ⟨?_, (alternatingGroup Z).mul_mem ((alternatingGroup Z).mul_mem g.2 hx.2)
        ((alternatingGroup Z).inv_mem g.2)⟩
      obtain ⟨r, hr, hrx⟩ := hx.1
      have hgY : (g : Perm Z) ∈ Y := hAY g.2
      refine ⟨⟨g, hgY⟩ * r * ⟨g, hgY⟩⁻¹, (MonoidHom.normal_ker φ).conj_mem r hr _, ?_⟩
      simp [← hrx]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((R ⊓ alternatingGroup Z).subgroupOf (alternatingGroup Z)) with h2 | h2
    ·
      have h3 : R ⊓ alternatingGroup Z = ⊥ := by
        have := congrArg (Subgroup.map (alternatingGroup Z).subtype) h2
        rwa [subgroupOf_map_subtype, Subgroup.map_bot, inf_eq_left.mpr inf_le_right,
          inf_comm, inf_comm] at this
      have h4 := card_le_two_of_inf_eq_bot (Y := R) (by
        rw [← h3])
      have hAcard : 2 * Nat.card (alternatingGroup Z) = (Fintype.card Z).factorial := by
        rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm]
      have hAdvd : Nat.card (alternatingGroup Z) ∣ Nat.card Y := Subgroup.card_dvd_of_le hAY
      obtain ⟨m, hm⟩ := hAdvd
      obtain ⟨d, hd⟩ := hYk
      have hR1 : 1 ≤ Nat.card R := Nat.card_pos
      have hm2 : m ∣ 2 := by
        refine ⟨d, ?_⟩
        have hA0 : 0 < Nat.card (alternatingGroup Z) := Nat.card_pos
        have : Nat.card (alternatingGroup Z) * (m * d) = Nat.card (alternatingGroup Z) * 2 := by
          rw [← mul_assoc, ← hm, ← hd, ← hAcard, mul_comm]
        exact (Nat.eq_of_mul_eq_mul_left hA0 this).symm
      have hm' : m = 1 ∨ m = 2 := by
        have := Nat.le_of_dvd (by norm_num) hm2
        interval_cases m <;> simp_all
      obtain ⟨h5, h6, h7⟩ := factorial_ne (Fintype.card Z)
      rcases hm' with rfl | rfl <;>
        · have hR' : Nat.card R = 1 ∨ Nat.card R = 2 := by omega
          rcases hR' with hR' | hR' <;> rw [hQ, hR'] at hYQ <;> omega
    ·
      have h3 : alternatingGroup Z ≤ R := by
        intro x hx
        have : (⟨x, hx⟩ : alternatingGroup Z) ∈
            (R ⊓ alternatingGroup Z).subgroupOf (alternatingGroup Z) := h2 ▸ mem_top _
        exact (mem_inf.mp this).1
      have hAcard : 2 * Nat.card (alternatingGroup Z) = (Fintype.card Z).factorial := by
        rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm]
      have h4 : Nat.card (alternatingGroup Z) ≤ Nat.card R := Subgroup.card_le_of_le h3
      have h5 := Nat.le_of_dvd (Nat.factorial_pos _) hYk
      have hA0 : 0 < Nat.card (alternatingGroup Z) := Nat.card_pos
      have : Nat.card Q * Nat.card (alternatingGroup Z) ≤ 2 * Nat.card (alternatingGroup Z) := by
        calc Nat.card Q * Nat.card (alternatingGroup Z) ≤ Nat.card Q * Nat.card R :=
              Nat.mul_le_mul_left _ h4
          _ = Nat.card Y := hYQ.symm
          _ ≤ 2 * Nat.card (alternatingGroup Z) := by omega
      have := Nat.le_of_mul_le_mul_right this hA0
      omega

end CFSG.ComponentClassification.GSThmB.X11.Sym
