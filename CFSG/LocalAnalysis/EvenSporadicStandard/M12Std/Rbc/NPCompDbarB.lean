module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompBurnside
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompDbarA

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

variable {K : Type*} [Group K] {A : Subgroup K} [A.Normal]

theorem inf_centralizer_single_eq {w c : K} (hS : Alt5Pair A w c) :
    A ⊓ centralizer ({w} : Set K) = A ⊓ centralizer ({c} : Set K) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxA, hxw⟩
    refine ⟨hxA, ?_⟩
    have hxh : x * (c⁻¹ * w) = (c⁻¹ * w) * x :=
      Subgroup.mem_centralizer_iff.mp hS.h₀_mem x hxA
    have h : x * c * (c⁻¹ * w) = c * x * (c⁻¹ * w) := by
      have h1 : x * (c * (c⁻¹ * w)) = (c * (c⁻¹ * w)) * x := by
        rw [← hS.w_eq]
        exact hxw
      calc x * c * (c⁻¹ * w) = x * (c * (c⁻¹ * w)) := by group
        _ = (c * (c⁻¹ * w)) * x := h1
        _ = c * ((c⁻¹ * w) * x) := by group
        _ = c * (x * (c⁻¹ * w)) := by rw [← hxh]
        _ = c * x * (c⁻¹ * w) := by group
    exact mul_right_cancel h
  · rintro ⟨hxA, hxc⟩
    refine ⟨hxA, ?_⟩
    have hxh : x * (c⁻¹ * w) = (c⁻¹ * w) * x :=
      Subgroup.mem_centralizer_iff.mp hS.h₀_mem x hxA
    rw [hS.w_eq]
    calc x * (c * (c⁻¹ * w)) = x * c * (c⁻¹ * w) := by group
      _ = c * x * (c⁻¹ * w) := by rw [hxc]
      _ = c * (x * (c⁻¹ * w)) := by group
      _ = c * ((c⁻¹ * w) * x) := by rw [hxh]
      _ = (c * (c⁻¹ * w)) * x := by group

theorem card_inf_centralizer_h₀_le_two [Finite K] (e : ↥A ≃* alternatingGroup (Fin 5)) {w c : K}
    (hS : Alt5Pair A w c) (hcard : Nat.card ↥(centralizer ({w} : Set K)) ≤ 8) :
    Nat.card ↥(centralizer (A : Set K) ⊓ centralizer ({c⁻¹ * w} : Set K)) ≤ 2 := by
  let S : Subgroup K := A ⊓ centralizer ({c} : Set K)
  let T : Subgroup K := centralizer (A : Set K) ⊓ centralizer ({c⁻¹ * w} : Set K)
  have hcomm : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).1 x (Subgroup.mem_inf.mp hx).1
  have hbot : S ⊓ T = ⊥ := by
    apply le_bot_iff.mp
    have hle : S ⊓ T ≤ A ⊓ centralizer (A : Set K) := by
      intro x hx
      obtain ⟨hxS, hxT⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxS).1, (Subgroup.mem_inf.mp hxT).1⟩
    exact hle.trans (le_of_eq (inf_centralizer_eq_bot_of_alt5 e))
  have hcard_inf : Nat.card ↥(S ⊓ T) = 1 := by rw [hbot, Subgroup.card_bot]
  have hS4 : Nat.card ↥S = 4 := by
    show Nat.card ↥(A ⊓ centralizer ({c} : Set K)) = 4
    exact (card_inf_centralizer_single_of_alt5 e hS.mem hS.sq_c hS.ne_one).1
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S T hcomm).1
  have hle_w : S ⊔ T ≤ centralizer ({w} : Set K) := by
    apply sup_le
    · intro x hx
      have hxS : x ∈ A ⊓ centralizer ({c} : Set K) := hx
      have hxw : x ∈ A ⊓ centralizer ({w} : Set K) := by
        rw [inf_centralizer_single_eq hS]
        exact Subgroup.mem_inf.mpr hxS
      exact (Subgroup.mem_inf.mp hxw).2
    · intro t ht
      have htH : t ∈ centralizer (A : Set K) := (Subgroup.mem_inf.mp ht).1
      have hth : t * (c⁻¹ * w) = (c⁻¹ * w) * t :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht).2
      have htc : c * t = t * c := Subgroup.mem_centralizer_iff.mp htH c hS.mem
      rw [Subgroup.mem_centralizer_singleton_iff, hS.w_eq]
      calc t * (c * (c⁻¹ * w)) = t * c * (c⁻¹ * w) := by group
        _ = c * t * (c⁻¹ * w) := by rw [htc]
        _ = c * (t * (c⁻¹ * w)) := by group
        _ = c * ((c⁻¹ * w) * t) := by rw [hth]
        _ = (c * (c⁻¹ * w)) * t := by group
  have hcard_sup_le : Nat.card ↥(S ⊔ T) ≤ 8 :=
    (Subgroup.card_le_of_le hle_w).trans hcard
  have hT_le : Nat.card ↥T ≤ 2 := by
    have h1 : Nat.card ↥(S ⊔ T) = 4 * Nat.card ↥T := by
      have h := hprod
      rw [hcard_inf, hS4, mul_one] at h
      exact h
    have h2 : 4 * Nat.card ↥T ≤ 8 := by
      rw [h1] at hcard_sup_le
      exact hcard_sup_le
    omega
  exact hT_le

private theorem map_centralizer_singleton_subtype {K : Type*} [Group K] {H : Subgroup K} {g : K}
    (hg : g ∈ H) :
    (centralizer ({(⟨g, hg⟩ : ↥H)} : Set ↥H)).map H.subtype =
      H ⊓ centralizer ({g} : Set K) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_inf.mpr ⟨y.2, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)⟩
  · intro hx
    obtain ⟨hxH, hxg⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxg)

private theorem card_centralizer_singleton_subtype {K : Type*} [Group K] {H : Subgroup K} {g : K}
    (hg : g ∈ H) :
    Nat.card ↥(centralizer ({(⟨g, hg⟩ : ↥H)} : Set ↥H)) =
      Nat.card ↥(H ⊓ centralizer ({g} : Set K)) := by
  rw [← map_centralizer_singleton_subtype hg]
  exact (Subgroup.card_map_of_injective H.subtype_injective).symm

theorem card_centralizer_le_two [Finite K] (hO : CFSG.oddCore K = ⊥)
    (e : ↥A ≃* alternatingGroup (Fin 5)) {w c : K} (hS : Alt5Pair A w c)
    (hcard : Nat.card ↥(centralizer ({w} : Set K)) ≤ 8) :
    Nat.card ↥(centralizer (A : Set K)) ≤ 2 := by
  by_cases h0 : c⁻¹ * w = 1
  · have htop : centralizer ({c⁻¹ * w} : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_singleton_iff, h0]
      simp
    have h2 := card_inf_centralizer_h₀_le_two e hS hcard
    rw [htop, inf_top_eq] at h2
    exact h2
  · have hO' : CFSG.oddCore ↥(centralizer (A : Set K)) = ⊥ :=
      oddCore_eq_bot_of_normal hO (centralizer (A : Set K))
    let h : ↥(centralizer (A : Set K)) := ⟨c⁻¹ * w, hS.h₀_mem⟩
    have hh : h * h = 1 := Subtype.ext hS.h₀_sq
    have h1 : h ≠ 1 := fun heq => h0 (congrArg Subtype.val heq)
    have hcard_h :
        Nat.card ↥(centralizer ({h} : Set ↥(centralizer (A : Set K)))) ≤ 2 := by
      rw [card_centralizer_singleton_subtype h.2]
      exact card_inf_centralizer_h₀_le_two e hS hcard
    exact le_of_eq (card_eq_two_of_card_centralizer_le_two hO' hh h1 hcard_h)

theorem centralizer_le_center [Finite K] (hO : CFSG.oddCore K = ⊥)
    (e : ↥A ≃* alternatingGroup (Fin 5)) {w c : K} (hS : Alt5Pair A w c)
    (hcard : Nat.card ↥(centralizer ({w} : Set K)) ≤ 8) :
    centralizer (A : Set K) ≤ center K :=
  le_center_of_card_le_two _ (card_centralizer_le_two hO e hS hcard)

end CFSG.EvenSporadicStandard.M12Std.Rbc
