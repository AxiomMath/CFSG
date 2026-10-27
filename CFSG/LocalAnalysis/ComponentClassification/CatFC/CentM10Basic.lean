module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt6_no_order_six (g : alternatingGroup (Fin 6)) : orderOf g ≠ 6 := by
  have hfin : ∀ h : alternatingGroup (Fin 6), h ^ 6 = 1 → h ^ 2 = 1 ∨ h ^ 3 = 1 := by
    decide +kernel
  intro h6
  have hpow : g ^ 6 = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [h6] at h
  rcases hfin g hpow with h2 | h3
  · exact absurd h2 (pow_ne_one_of_lt_orderOf (by norm_num) (by simp [h6]))
  · exact absurd h3 (pow_ne_one_of_lt_orderOf (by norm_num) (by simp [h6]))

theorem no_order_six {F : Type} [Group F] [Finite F] (D : Subgroup F) [D.Normal]
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hF : Nat.card F ≤ 720)
    (hinv : ∀ x : F, orderOf x = 2 → x ∈ D) : ∀ x : F, orderOf x ≠ 6 := by
  obtain ⟨e⟩ := hD
  have hDcard : Nat.card D = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hidx : D.index * 360 = Nat.card F := by
    rw [← hDcard]
    exact Subgroup.index_mul_card (H := D)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hcases : D.index = 1 ∨ D.index = 2 := by
    have h0 : D.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hidx
      omega
    omega
  have hmul_self : ∀ y : F, y * y ∈ D := by
    rcases hcases with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      intro y
      rw [h1]
      exact Subgroup.mem_top _
    · exact fun y => Subgroup.mul_self_mem_of_index_two h2 y
  intro x hx6
  have hd3 : (3 : ℕ) ∣ orderOf x := by
    rw [hx6]
    norm_num
  have h3 : orderOf (x ^ 3) = 2 := by
    have h := orderOf_pow_of_dvd (x := x) (n := 3) (by norm_num) hd3
    rw [hx6] at h
    simpa using h
  have hx3 : x ^ 3 ∈ D := hinv (x ^ 3) h3
  have hx2 : x ^ 2 ∈ D := by
    rw [pow_two]
    exact hmul_self x
  have hxD : x ∈ D := by
    have hmem : x ^ 3 * (x ^ 2)⁻¹ ∈ D := D.mul_mem hx3 (D.inv_mem hx2)
    have heq : x ^ 3 * (x ^ 2)⁻¹ = x := by group
    rwa [heq] at hmem
  have hyD : orderOf (⟨x, hxD⟩ : D) = 6 := by
    rw [← Subgroup.orderOf_coe]
    exact hx6
  have himg : orderOf (e ⟨x, hxD⟩) = 6 := by
    rw [MulEquiv.orderOf_eq]
    exact hyD
  exact alt6_no_order_six (e ⟨x, hxD⟩) himg

theorem mulEquiv_prod_of_central {G : Type} [Group G] [Finite G] (D : Subgroup G) [D.Normal] {z : G}
    (hz : orderOf z = 2) (hzc : z ∈ center G) (hzD : z ∉ D) (hcard : Nat.card G = 2 * Nat.card D) :
    Nonempty (G ≃* Multiplicative (ZMod 2) × ↥D) := by
  have hval : ∀ a b : ZMod 2, z ^ (a + b).val = z ^ a.val * z ^ b.val := by
    intro a b
    rw [ZMod.val_add, ← pow_add]
    have h := pow_mod_orderOf z (a.val + b.val)
    rw [hz] at h
    exact h
  have hcomm : ∀ (n : ℕ) (g : G), g * z ^ n = z ^ n * g := by
    intro n g
    exact ((show Commute g z from Subgroup.mem_center_iff.mp hzc g).pow_right n).eq
  have hkey : ∀ (m n : ℕ) (x y : G), z ^ m * x * (z ^ n * y) = z ^ (m + n) * (x * y) := by
    intro m n x y
    rw [pow_add]
    calc z ^ m * x * (z ^ n * y) = z ^ m * (x * z ^ n) * y := by simp only [mul_assoc]
      _ = z ^ m * (z ^ n * x) * y := by rw [hcomm n x]
      _ = z ^ m * z ^ n * (x * y) := by simp only [mul_assoc]
  obtain ⟨φ, hφ⟩ : ∃ φ : Multiplicative (ZMod 2) × D →ₙ* G,
      ∀ p, φ p = z ^ (Multiplicative.toAdd p.1).val * (p.2 : G) :=
    ⟨{ toFun := fun p => z ^ (Multiplicative.toAdd p.1).val * (p.2 : G)
       map_mul' := by
         rintro ⟨a, d⟩ ⟨b, d'⟩
         show z ^ (Multiplicative.toAdd (a * b)).val * ((d * d' : D) : G) =
           (z ^ (Multiplicative.toAdd a).val * (d : G)) *
             (z ^ (Multiplicative.toAdd b).val * (d' : G))
         rw [toAdd_mul, hval, Subgroup.coe_mul, hkey, pow_add] }, fun p => rfl⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, d⟩ ⟨b, d'⟩ h
    have h' : z ^ (Multiplicative.toAdd a).val * (d : G) =
        z ^ (Multiplicative.toAdd b).val * (d' : G) := by
      have h0 := h
      rw [hφ, hφ] at h0
      exact h0
    have hm : (Multiplicative.toAdd a).val < 2 := ZMod.val_lt _
    have hn : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
    have hmn : (Multiplicative.toAdd a).val = (Multiplicative.toAdd b).val := by
      by_contra hne
      apply hzD
      rcases (by omega : (Multiplicative.toAdd a).val = 0 ∧ (Multiplicative.toAdd b).val = 1 ∨
          (Multiplicative.toAdd a).val = 1 ∧ (Multiplicative.toAdd b).val = 0) with
        ⟨h0, h1⟩ | ⟨h1, h0⟩
      · rw [h0, h1, pow_zero, one_mul, pow_one] at h'
        have hz_eq : z = (d : G) * (d' : G)⁻¹ := by
          rw [h']
          group
        rw [hz_eq]
        exact D.mul_mem d.2 (D.inv_mem d'.2)
      · rw [h1, h0, pow_zero, one_mul, pow_one] at h'
        have hz_eq : z = (d' : G) * (d : G)⁻¹ := by
          rw [← h']
          group
        rw [hz_eq]
        exact D.mul_mem d'.2 (D.inv_mem d.2)
    have hab : a = b := Multiplicative.toAdd.injective (ZMod.val_injective 2 hmn)
    rw [hmn] at h'
    have hdd : d = d' := Subtype.ext (mul_left_cancel h')
    rw [hab, hdd]
  have hcard' : Nat.card (Multiplicative (ZMod 2) × D) = Nat.card G := by
    rw [Nat.card_prod, hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (le_of_eq hcard'.symm)
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem exists_normal_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (D : Subgroup H)
    [D.Normal] (hA : Nonempty (↥D ≃* alternatingGroup (Fin 6))) :
    ∃ D' : Subgroup G, D'.Normal ∧ Nonempty (↥D' ≃* alternatingGroup (Fin 6)) ∧
      ∀ x, x ∈ D' ↔ e x ∈ D := by
  obtain ⟨φ⟩ := hA
  have hmap : (D.comap (e : G →* H)).map (e : G →* H) = D :=
    Subgroup.map_comap_eq_self_of_surjective (f := (e : G →* H)) e.surjective D
  refine ⟨D.comap (e : G →* H), Subgroup.Normal.comap inferInstance _, ?_, fun x => Iff.rfl⟩
  exact ⟨((MulEquiv.subgroupMap e (D.comap (e : G →* H))).trans
    (MulEquiv.subgroupCongr hmap)).trans φ⟩

end CFSG.ComponentClassification.CatFC
