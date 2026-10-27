module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

private lemma sec8t84_mul_mul (W : Sec8T84Wr G t T1 T2) {x x' y y' : G} (hx : x ∈ T1)
    (hx' : x' ∈ T1) (hy : y ∈ T2) (hy' : y' ∈ T2) :
    (x * y) * (x' * y') = (x * x') * (y * y') :=
  Commute.mul_mul_mul_comm (W.comm x' hx' y hy).symm x y'

private lemma sec8t84_mul_inv (W : Sec8T84Wr G t T1 T2) {x y : G} (hx : x ∈ T1)
    (hy : y ∈ T2) : (x * y)⁻¹ = x⁻¹ * y⁻¹ :=
  Commute.mul_inv (W.comm x hx y hy)

theorem sec8t84_proj_split (W : Sec8T84Wr G t T1 T2) {A : Subgroup G} (hA : A ≤ T1 ⊔ T2)
    (he : CFSG.Open.IsElemAbelian 2 A) :
    ∃ A1 A2 : Subgroup G, A1 ≤ T1 ∧ A2 ≤ T2 ∧ CFSG.Open.IsElemAbelian 2 A1 ∧
      CFSG.Open.IsElemAbelian 2 A2 ∧ A ≤ A1 ⊔ A2 ∧ Nat.card A ≤ Nat.card A1 * Nat.card A2 ∧
      (∀ x ∈ T1, ∀ y ∈ T2, x * y ∈ A → x ∈ A1 ∧ y ∈ A2) ∧
      (∀ x ∈ A1, ∃ y ∈ T2, x * y ∈ A) ∧ (∀ y ∈ A2, ∃ x ∈ T1, x * y ∈ A) := by
  let A1 : Subgroup G :=
    { carrier := {x | x ∈ T1 ∧ ∃ y ∈ T2, x * y ∈ A}
      one_mem' := ⟨one_mem T1, 1, one_mem T2, by simpa using one_mem A⟩
      mul_mem' := by
        rintro x x' ⟨hxT1, y, hyT2, hxyA⟩ ⟨hx'T1, y', hy'T2, hx'y'A⟩
        refine ⟨mul_mem hxT1 hx'T1, y * y', mul_mem hyT2 hy'T2, ?_⟩
        rw [← sec8t84_mul_mul W hxT1 hx'T1 hyT2 hy'T2]
        exact mul_mem hxyA hx'y'A
      inv_mem' := by
        rintro x ⟨hxT1, y, hyT2, hxyA⟩
        refine ⟨inv_mem hxT1, y⁻¹, inv_mem hyT2, ?_⟩
        rw [← sec8t84_mul_inv W hxT1 hyT2]
        exact inv_mem hxyA }
  let A2 : Subgroup G :=
    { carrier := {y | y ∈ T2 ∧ ∃ x ∈ T1, x * y ∈ A}
      one_mem' := ⟨one_mem T2, 1, one_mem T1, by simpa using one_mem A⟩
      mul_mem' := by
        rintro y y' ⟨hyT2, x, hxT1, hxyA⟩ ⟨hy'T2, x', hx'T1, hx'y'A⟩
        refine ⟨mul_mem hyT2 hy'T2, x * x', mul_mem hxT1 hx'T1, ?_⟩
        rw [← sec8t84_mul_mul W hxT1 hx'T1 hyT2 hy'T2]
        exact mul_mem hxyA hx'y'A
      inv_mem' := by
        rintro y ⟨hyT2, x, hxT1, hxyA⟩
        refine ⟨inv_mem hyT2, x⁻¹, inv_mem hxT1, ?_⟩
        rw [← sec8t84_mul_inv W hxT1 hyT2]
        exact inv_mem hxyA }
  refine ⟨A1, A2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro y hy
    exact hy.1
  · refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      obtain ⟨y, hyT2, hxyA⟩ := a.2.2
      obtain ⟨y', hy'T2, hx'y'A⟩ := b.2.2
      have hcommA := CFSG.Open.IsElemAbelian.comm he hxyA hx'y'A
      rw [sec8t84_mul_mul W a.2.1 b.2.1 hyT2 hy'T2,
        sec8t84_mul_mul W b.2.1 a.2.1 hy'T2 hyT2] at hcommA
      exact (sec8t84_wr_unique W (mul_mem a.2.1 b.2.1) (mul_mem b.2.1 a.2.1)
        (mul_mem hyT2 hy'T2) (mul_mem hy'T2 hyT2) hcommA).1
    · intro x hx
      obtain ⟨y, hyT2, hxyA⟩ := hx.2
      have hsq := CFSG.Open.IsElemAbelian.mul_self_eq_one he hxyA
      have e : (x * x) * (y * y) = 1 := by
        rw [← sec8t84_mul_mul W hx.1 hx.1 hyT2 hyT2]
        exact hsq
      have hu := (sec8t84_wr_unique W (mul_mem hx.1 hx.1) (one_mem T1)
        (mul_mem hyT2 hyT2) (one_mem T2) (by rw [e, mul_one])).1
      rw [pow_two]
      exact hu
  · refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      obtain ⟨x, hxT1, hxyA⟩ := a.2.2
      obtain ⟨x', hx'T1, hx'y'A⟩ := b.2.2
      have hcommA := CFSG.Open.IsElemAbelian.comm he hxyA hx'y'A
      rw [sec8t84_mul_mul W hxT1 hx'T1 a.2.1 b.2.1,
        sec8t84_mul_mul W hx'T1 hxT1 b.2.1 a.2.1] at hcommA
      exact (sec8t84_wr_unique W (mul_mem hxT1 hx'T1) (mul_mem hx'T1 hxT1)
        (mul_mem a.2.1 b.2.1) (mul_mem b.2.1 a.2.1) hcommA).2
    · intro y hy
      obtain ⟨x, hxT1, hxyA⟩ := hy.2
      have hsq := CFSG.Open.IsElemAbelian.mul_self_eq_one he hxyA
      have e : (x * x) * (y * y) = 1 := by
        rw [← sec8t84_mul_mul W hxT1 hxT1 hy.1 hy.1]
        exact hsq
      have hu := (sec8t84_wr_unique W (mul_mem hxT1 hxT1) (one_mem T1)
        (mul_mem hy.1 hy.1) (one_mem T2) (by rw [e, mul_one])).2
      rw [pow_two]
      exact hu
  · intro a ha
    obtain ⟨x, hxT1, y, hyT2, haxy⟩ := sec8t84_wr_decomp W (hA ha)
    have hxyA : x * y ∈ A := haxy ▸ ha
    rw [haxy]
    exact Subgroup.mul_mem_sup ⟨hxT1, y, hyT2, hxyA⟩ ⟨hyT2, x, hxT1, hxyA⟩
  · have hP : ∀ a : ↥A, ∃ x ∈ T1, ∃ y ∈ T2, (a : G) = x * y :=
      fun a => sec8t84_wr_decomp W (hA a.2)
    let xc : ↥A → G := fun a => Classical.choose (hP a)
    have hxc : ∀ a : ↥A, xc a ∈ T1 ∧ ∃ y ∈ T2, (a : G) = xc a * y :=
      fun a => Classical.choose_spec (hP a)
    let yc : ↥A → G := fun a => Classical.choose (hxc a).2
    have hyc : ∀ a : ↥A, yc a ∈ T2 ∧ (a : G) = xc a * yc a :=
      fun a => Classical.choose_spec (hxc a).2
    let f : ↥A → ↥A1 × ↥A2 := fun a =>
      (⟨xc a, (hxc a).1, yc a, (hyc a).1, by rw [← (hyc a).2]; exact a.2⟩,
       ⟨yc a, (hyc a).1, xc a, (hxc a).1, by rw [← (hyc a).2]; exact a.2⟩)
    have hf : Function.Injective f := by
      intro a b hab
      have hxab : xc a = xc b :=
        Subtype.ext_iff.mp (congrArg (fun p : ↥A1 × ↥A2 => p.1) hab)
      have hyab : yc a = yc b :=
        Subtype.ext_iff.mp (congrArg (fun p : ↥A1 × ↥A2 => p.2) hab)
      apply Subtype.ext
      rw [(hyc a).2, (hyc b).2, hxab, hyab]
    have hcard := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod] at hcard
  · intro x hxT1 y hyT2 hxyA
    exact ⟨⟨hxT1, y, hyT2, hxyA⟩, ⟨hyT2, x, hxT1, hxyA⟩⟩
  · intro x hx
    exact hx.2
  · intro y hy
    exact hy.2

end CFSG.OddStandard.SmallF3.Omega
