module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8JSearch
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8JSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CoverBase

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

theorem mul_rhoPerm_inv_mem
    {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43Ext)
    (hxP : x ∉ CFSG.EvenSporadicStandard.M24Std.CU43.P) :
    x * rhoPerm⁻¹ ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P := by
  rcases mem_U43Ext hx with h | ⟨g, hg, rfl⟩
  · exact absurd h hxP
  · simpa [mul_assoc] using hg

theorem card_U43Ext :
    Nat.card (U43Ext : Subgroup (Equiv.Perm (Fin 820))) = 6531840 := by
  classical
  have hP : Nat.card CFSG.EvenSporadicStandard.M24Std.CU43.P = 3265920 :=
    CFSG.EvenSporadicStandard.M24Std.CU43.card_P
  have hJ : Nat.card (TS8J.Jsub : Subgroup (Equiv.Perm (Fin 820))) = 256 := TS8J.card_Jsub
  have hB : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have hup : Nat.card ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))) ≤
      Nat.card (↥CFSG.EvenSporadicStandard.M24Std.CU43.P × Bool) := by
    let f : ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))) →
        (↥CFSG.EvenSporadicStandard.M24Std.CU43.P × Bool) := fun x =>
      if h : (x : Equiv.Perm (Fin 820)) ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P then
        (⟨(x : Equiv.Perm (Fin 820)), h⟩, false)
      else
        (⟨(x : Equiv.Perm (Fin 820)) * rhoPerm⁻¹, mul_rhoPerm_inv_mem x.2 h⟩, true)
    refine Nat.card_le_card_of_injective f ?_
    intro x y hxy
    by_cases hx : (x : Equiv.Perm (Fin 820)) ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P <;>
      by_cases hy : (y : Equiv.Perm (Fin 820)) ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P
    · simp only [f, dif_pos hx, dif_pos hy, Prod.mk.injEq] at hxy
      exact Subtype.ext (congrArg
        (fun p : ↥CFSG.EvenSporadicStandard.M24Std.CU43.P => (p : Equiv.Perm (Fin 820))) hxy.1)
    · simp only [f, dif_pos hx, dif_neg hy, Prod.mk.injEq] at hxy
      exact absurd hxy.2 (by simp)
    · simp only [f, dif_neg hx, dif_pos hy, Prod.mk.injEq] at hxy
      exact absurd hxy.2 (by simp)
    · simp only [f, dif_neg hx, dif_neg hy, Prod.mk.injEq] at hxy
      have h1 := congrArg
        (fun p : ↥CFSG.EvenSporadicStandard.M24Std.CU43.P => (p : Equiv.Perm (Fin 820))) hxy.1
      exact Subtype.ext (mul_right_cancel h1)
  rw [Nat.card_prod, hP, hB] at hup
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le
    (show CFSG.EvenSporadicStandard.M24Std.CU43.P ≤
      (U43Ext : Subgroup (Equiv.Perm (Fin 820))) from TS8J.P_le_U43Ext)
  rw [hP] at hk
  have hk2 : k ≤ 2 := by omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hpos : 0 < Nat.card ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))) := Nat.card_pos
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    have h256 : 256 ∣ Nat.card ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))) := by
      rw [← hJ]
      exact Subgroup.card_dvd_of_le TS8J.Jsub_le
    rw [hk] at h256
    norm_num at h256
  omega

theorem max_of_card {X : Type} [Group X] [Finite X] (hX : Nat.card X = 6531840)
    {H : Subgroup X} (hH : Nat.card H = 256) {R : Subgroup X} (hR : IsPGroup 2 R) (hHR : H ≤ R) :
    R ≤ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
  have h2 : Nat.card R ∣ Nat.card X := Subgroup.card_subgroup_dvd_card R
  rw [hn, hX] at h2
  have hn8 : n ≤ 8 := by
    by_contra h
    have h9 : 2 ^ 9 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h9.trans h2
    norm_num at this
  have hle : Nat.card R ≤ Nat.card H := by
    rw [hn, hH]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hn8) (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hHR hle).ge

theorem isPGroup_closure_seven {X : Type} [Group X] {ζ α t g₁ g₂ h₁ h₂ : X}
    (hζ : ζ * ζ = 1) (hA : IsPGroup 2 (closure ({α, t, g₁, g₂, h₁, h₂} : Set X)))
    (hζα : ζ * α * ζ⁻¹ = α * t) (hζt : ζ * t * ζ⁻¹ = t) (hh1 : h₁ = ζ * g₁ * ζ⁻¹)
    (hh2 : h₂ = ζ * g₂ * ζ⁻¹) :
    IsPGroup 2 (closure ({ζ, α, t, g₁, g₂, h₁, h₂} : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup X := closure ({α, t, g₁, g₂, h₁, h₂} : Set X) with hAdef
  have hζi : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ
  have key : ∀ y : X, ζ * (ζ * y * ζ⁻¹) * ζ⁻¹ = y := by
    intro y
    rw [hζi]
    calc ζ * (ζ * y * ζ) * ζ = (ζ * ζ) * y * (ζ * ζ) := by group
      _ = y := by rw [hζ]; group
  have hAB : A ≤ A.comap (MulAut.conj ζ).toMonoidHom := by
    rw [hAdef, closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ζ * y * ζ⁻¹ ∈ A
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h | h | h <;> rw [h]
    · rw [hζα]
      exact A.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · rw [hζt]
      exact subset_closure (by simp)
    · rw [← hh1]
      exact subset_closure (by simp)
    · rw [← hh2]
      exact subset_closure (by simp)
    · rw [hh1, key]
      exact subset_closure (by simp)
    · rw [hh2, key]
      exact subset_closure (by simp)
  have hnorm : ζ ∈ Subgroup.normalizer A := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h' := hAB hh
      rw [Subgroup.mem_comap] at h'
      exact h'
    · intro hh
      have h' := hAB hh
      rw [Subgroup.mem_comap] at h'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
      rwa [key] at h'
  have hZ : IsPGroup 2 ↥(zpowers ζ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hζ)
  have hS : IsPGroup 2 ↥(A ⊔ zpowers ζ : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hA hZ (zpowers_le.2 hnorm)
  refine IsPGroup.to_le hS ((closure_le _).2 ?_)
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have hA' : ∀ z ∈ ({α, t, g₁, g₂, h₁, h₂} : Set X), z ∈ (A ⊔ zpowers ζ : Subgroup X) :=
    fun z hz => Subgroup.mem_sup_left (subset_closure hz)
  rcases hy with h | h | h | h | h | h | h
  · rw [h]
    exact Subgroup.mem_sup_right (mem_zpowers ζ)
  · exact hA' y (by simp [h])
  · exact hA' y (by simp [h])
  · exact hA' y (by simp [h])
  · exact hA' y (by simp [h])
  · exact hA' y (by simp [h])
  · exact hA' y (by simp [h])

end CFSG.EvenSporadicStandard.Fin76b
