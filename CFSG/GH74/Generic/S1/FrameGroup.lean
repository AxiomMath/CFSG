module

public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

section Bar

variable {C : Type*} [Group C] {K : Subgroup C} {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

@[expose] def kconj (vb : C) (k : ↥K) : C := (k : C) * vb * (k : C)⁻¹

theorem kconj_mul_self {vb : C} (hvb2 : vb * vb = 1) (k : ↥K) : kconj vb k * kconj vb k = 1 := by
  unfold kconj
  calc (k : C) * vb * (k : C)⁻¹ * ((k : C) * vb * (k : C)⁻¹) = (k : C) * (vb * vb) * (k : C)⁻¹ := by
        group
    _ = 1 := by rw [hvb2]; group

theorem kconj_not_mem [K.Normal] {vb : C} (hvbK : vb ∉ K) (k : ↥K) : kconj vb k ∉ K := by
  intro h
  apply hvbK
  have : (k : C)⁻¹ * kconj vb k * (k : C) ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
  unfold kconj at this
  simpa [mul_assoc] using this

theorem kconj_mul_kconj {vb : C} (hvb2 : vb * vb = 1) {α : MulAut ↥K}
    (hα : ∀ n : ↥K, ((α n : ↥K) : C) = vb * n * vb⁻¹) (k k' : ↥K) :
    kconj vb k * kconj vb k' = ((k * α (k⁻¹ * k') * k'⁻¹ : ↥K) : C) := by
  unfold kconj
  have h1 : ((α (k⁻¹ * k') : ↥K) : C) = vb * ((k : C)⁻¹ * (k' : C)) * vb⁻¹ := by
    rw [hα]; simp
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
  have h2 : vb⁻¹ = vb := inv_eq_of_mul_eq_one_right hvb2
  calc (k : C) * vb * (k : C)⁻¹ * ((k' : C) * vb * (k' : C)⁻¹)
      = (k : C) * (vb * ((k : C)⁻¹ * (k' : C)) * vb⁻¹) * (vb * vb) * (k' : C)⁻¹ := by
        rw [h2]; simp only [mul_assoc]; rw [← mul_assoc vb vb]; rw [hvb2]; simp
    _ = (k : C) * (vb * ((k : C)⁻¹ * (k' : C)) * vb⁻¹) * (k' : C)⁻¹ := by rw [hvb2]; group

theorem kconj_mul_mul_inv {vb : C} {α : MulAut ↥K}
    (hα : ∀ n : ↥K, ((α n : ↥K) : C) = vb * n * vb⁻¹) (k n : ↥K) :
    kconj vb k * (n : C) * (kconj vb k)⁻¹ = ((k * α (k⁻¹ * n * k) * k⁻¹ : ↥K) : C) := by
  unfold kconj
  have h1 : ((α (k⁻¹ * n * k) : ↥K) : C) = vb * ((k : C)⁻¹ * (n : C) * (k : C)) * vb⁻¹ := by
    rw [hα]; simp
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
  group

end Bar

section Main

variable {G : Type} [Group G] {x : G}

theorem frame_in_bar {K : Subgroup (CentralizerBar x)} [K.Normal] {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) {S : Subgroup (GL (Fin 4) F)} (e : ↥K ≃* ↥S) {vb : CentralizerBar x}
    (hvb2 : vb * vb = 1) (hvbK : vb ∉ K) {α : MulAut ↥K}
    (hα : ∀ n : ↥K, ((α n : ↥K) : CentralizerBar x) = vb * n * vb⁻¹)
    (hact : ∀ n : ↥K, ((e (α n) : ↥S) : GL (Fin 4) F) =
      reflDiag F 3 * ((e n : ↥S) : GL (Fin 4) F) * (reflDiag F 3)⁻¹)
    (m : Fin 4 → ↥S)
    (hm : ∀ i, ((m i : ↥S) : GL (Fin 4) F) * reflDiag F 3 * ((m i : ↥S) : GL (Fin 4) F)⁻¹ =
      reflDiag F i)
    (hxK : xbar x ∈ K) (hxe : ((e ⟨xbar x, hxK⟩ : ↥S) : GL (Fin 4) F) = -1) :
    ∃ w : Fin 4 → CentralizerBar x, (∀ i, w i * w i = 1) ∧ (∀ i, w i ∉ K) ∧
      (∀ i j, w i * w j = w j * w i) ∧ w 0 * w 1 * w 2 * w 3 = xbar x ∧
      (∀ i j, i ≠ j → w i ≠ w j) ∧ (∀ i, ∃ k : ↥K, w i = kconj vb k) ∧
      ∀ i, ActsAsReflOn e (w i) (reflDiag F i) := by
  set r : Fin 4 → GL (Fin 4) F := reflDiag F with hr
  have hr2 : ∀ i, r i * r i = 1 := reflDiag_mul_self F
  have hrinv : ∀ i, (r i)⁻¹ = r i := fun i => inv_eq_of_mul_eq_one_right (hr2 i)
  have hrc : ∀ i j, r i * r j = r j * r i := reflDiag_comm F
  set kh : Fin 4 → ↥K := fun i => e.symm (m i) with hkh
  have hekh : ∀ i, ((e (kh i) : ↥S) : GL (Fin 4) F) = (m i : GL (Fin 4) F) := fun i => by
    simp [hkh]
  have hW : ∀ i j, ((e (kh i * α ((kh i)⁻¹ * kh j) * (kh j)⁻¹) : ↥S) : GL (Fin 4) F) =
      r i * r j := by
    intro i j
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hact,
      map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hekh, hekh]
    have h1 : (m i : GL (Fin 4) F) * (r 3 * ((m i : GL (Fin 4) F)⁻¹ * (m j : GL (Fin 4) F)) *
        (r 3)⁻¹) * (m j : GL (Fin 4) F)⁻¹ =
        ((m i : GL (Fin 4) F) * r 3 * (m i : GL (Fin 4) F)⁻¹) *
          ((m j : GL (Fin 4) F) * r 3 * (m j : GL (Fin 4) F)⁻¹)⁻¹ := by group
    rw [h1, hm i, hm j, hrinv]
  refine ⟨fun i => kconj vb (kh i), fun i => kconj_mul_self hvb2 _, fun i => kconj_not_mem hvbK _,
    ?_, ?_, ?_, fun i => ⟨kh i, rfl⟩, ?_⟩
  · intro i j
    rw [kconj_mul_kconj hvb2 hα, kconj_mul_kconj hvb2 hα]
    congr 1
    apply e.injective
    apply Subtype.ext
    rw [hW, hW, hrc]
  ·
    set W01 : ↥K := kh 0 * α ((kh 0)⁻¹ * kh 1) * (kh 1)⁻¹ with hW01
    set W23 : ↥K := kh 2 * α ((kh 2)⁻¹ * kh 3) * (kh 3)⁻¹ with hW23
    have hprod : (kconj vb (kh 0) * kconj vb (kh 1)) * (kconj vb (kh 2) * kconj vb (kh 3)) =
        ((W01 : ↥K) : CentralizerBar x) * ((W23 : ↥K) : CentralizerBar x) := by
      rw [kconj_mul_kconj hvb2 hα, kconj_mul_kconj hvb2 hα]
    have hK : W01 * W23 = ⟨xbar x, hxK⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hW01, hW23, hW, hW, hxe]
      have := reflDiag_prod F
      calc r 0 * r 1 * (r 2 * r 3) = r 0 * r 1 * r 2 * r 3 := by simp only [mul_assoc]
        _ = -1 := this
    calc kconj vb (kh 0) * kconj vb (kh 1) * kconj vb (kh 2) * kconj vb (kh 3)
        = (kconj vb (kh 0) * kconj vb (kh 1)) * (kconj vb (kh 2) * kconj vb (kh 3)) := by
          simp only [mul_assoc]
      _ = ((W01 : ↥K) : CentralizerBar x) * ((W23 : ↥K) : CentralizerBar x) := hprod
      _ = ((W01 * W23 : ↥K) : CentralizerBar x) := (Subgroup.coe_mul K W01 W23).symm
      _ = xbar x := by rw [hK]
  ·
    intro i j hij hw
    have hw' : kconj vb (kh i) = kconj vb (kh j) := hw
    have hij' : kconj vb (kh i) * kconj vb (kh j) = 1 := by
      rw [hw']
      exact kconj_mul_self hvb2 _
    rw [kconj_mul_kconj hvb2 hα] at hij'
    have h1 : (kh i * α ((kh i)⁻¹ * kh j) * (kh j)⁻¹ : ↥K) = 1 := Subtype.ext hij'
    have h3 : r i * r j = 1 := by
      have := congrArg (fun a : ↥K => ((e a : ↥S) : GL (Fin 4) F)) h1
      simp only [hW, map_one, Subgroup.coe_one] at this
      exact this
    have h4 : r i = r j := by
      have := mul_eq_one_iff_eq_inv.mp h3
      rw [this, hrinv]
    exact hij (reflDiag_injective F h2 h4)
  ·
    intro i k k' hk
    have h1 := kconj_mul_mul_inv hα (kh i) k
    rw [h1] at hk
    have hk' : k' = kh i * α ((kh i)⁻¹ * k * kh i) * (kh i)⁻¹ := (Subtype.ext hk).symm
    rw [hk', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hact,
      map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hekh]
    have h5 : (m i : GL (Fin 4) F) * (r 3 * ((m i : GL (Fin 4) F)⁻¹ * ((e k : ↥S) : GL (Fin 4) F) *
        (m i : GL (Fin 4) F)) * (r 3)⁻¹) * (m i : GL (Fin 4) F)⁻¹ =
        ((m i : GL (Fin 4) F) * r 3 * (m i : GL (Fin 4) F)⁻¹) * ((e k : ↥S) : GL (Fin 4) F) *
          ((m i : GL (Fin 4) F) * r 3 * (m i : GL (Fin 4) F)⁻¹)⁻¹ := by group
    rw [h5, hm i]

end Main

end CFSG.GH74.Generic.S1
