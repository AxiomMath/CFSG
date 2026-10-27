module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartFour

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup
open scoped commutatorElement

section General

variable {X : Type} [Group X]

theorem normalizer_le_normalizer_centerOf (W : Subgroup X) :
    normalizer (W : Set X) ≤ normalizer (AschbacherTheorem3.centerOf W : Set X) := by
  have key : ∀ g ∈ normalizer (W : Set X), ∀ z ∈ AschbacherTheorem3.centerOf W,
      g * z * g⁻¹ ∈ AschbacherTheorem3.centerOf W := by
    intro g hg z hz
    obtain ⟨hzW, hzc⟩ := hz
    refine ⟨(mem_normalizer_iff.mp hg z).mp hzW, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ W := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hg) w).mp hw
      simpa using h1
    have hc := mem_centralizer_iff.mp hzc _ hw'
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * w := by group
  intro g hg
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key g hg z, fun h => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using h1

theorem commutatorElement_mem_of_mem_sup {N B : Subgroup X} (hBN : B ≤ normalizer (N : Set X))
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) {x y : X} (hx : x ∈ N ⊔ B) (hy : y ∈ N ⊔ B) :
    ⁅x, y⁆ ∈ N := by
  obtain ⟨n, hn, b, hb, rfl⟩ := NormalizedProduct.coordinates N B hBN x hx
  obtain ⟨n', hn', b', hb', rfl⟩ := NormalizedProduct.coordinates N B hBN y hy
  have h1 : b * n' * b⁻¹ ∈ N := (mem_normalizer_iff.mp (hBN hb) n').mp hn'
  have h2 : b' * n * b'⁻¹ ∈ N := (mem_normalizer_iff.mp (hBN hb') n).mp hn
  have heq : ⁅n * b, n' * b'⁆ =
      n * (b * n' * b⁻¹) * (b * b') * (b' * b)⁻¹ * (n' * (b' * n * b'⁻¹))⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [heq, hB b hb b' hb', mul_inv_cancel_right]
  exact mul_mem (mul_mem hn h1) (inv_mem (mul_mem hn' h2))

theorem isMulCommutative_of_le_sup [Finite X] {A L P : Subgroup X} (hA2 : IsPGroup 2 A)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hAL : ∀ a ∈ A, ∀ b ∈ L, a * b = b * a)
    (hL : ∀ B : Subgroup X, B ≤ L → IsPGroup 2 B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hP2 : IsPGroup 2 P) (hP : P ≤ A ⊔ L) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have hLA : L ≤ normalizer (A : Set X) := fun b hb => by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hAL a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have h1 : b * a * b⁻¹ * b = b * a := by group
      have h2 := hAL _ ha b hb
      rw [h1] at h2
      have h3 : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [← h2]
          _ = b * a * b⁻¹ := by group
      rw [h3]
      exact ha
  have hAN : A ⊔ L ≤ normalizer (A : Set X) := sup_le le_normalizer hLA
  have hAP2 : IsPGroup 2 (A ⊔ P : Subgroup X) := hA2.to_sup_of_normal_left' hP2 (hP.trans hAN)
  have hB := hL (L ⊓ (A ⊔ P)) inf_le_left hAP2.to_inf_right
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := NormalizedProduct.coordinates A L hLA x (hP hx)
  obtain ⟨a', ha', b', hb', rfl⟩ := NormalizedProduct.coordinates A L hLA y (hP hy)
  have hbB : b ∈ L ⊓ (A ⊔ P) := ⟨hb, by
    have h1 := mul_mem (mem_sup_left (inv_mem ha) : a⁻¹ ∈ A ⊔ P) (mem_sup_right hx)
    simpa using h1⟩
  have hbB' : b' ∈ L ⊓ (A ⊔ P) := ⟨hb', by
    have h1 := mul_mem (mem_sup_left (inv_mem ha') : a'⁻¹ ∈ A ⊔ P) (mem_sup_right hy)
    simpa using h1⟩
  have hab' : b * a' = a' * b := (hAL a' ha' b hb).symm
  have hab : b' * a = a * b' := (hAL a ha b' hb').symm
  have h1 : a * b * (a' * b') = a * a' * (b * b') := by
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hab']
      _ = a * a' * (b * b') := by group
  have h2 : a' * b' * (a * b) = a' * a * (b' * b) := by
    calc a' * b' * (a * b) = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [hab]
      _ = a' * a * (b' * b) := by group
  rw [h1, h2, hAc a ha a' ha', hB b hbB b' hbB']

end General

section Dihedral

open DihedralGroup

@[expose] def rotations (m : ℕ) : Subgroup (DihedralGroup m) where
  carrier := {x | ∃ j, x = r j}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, r_mul_r i j⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, inv_r i⟩

theorem normal_of_le_rotations {m : ℕ} {C : Subgroup (DihedralGroup m)} (h : C ≤ rotations m) :
    C.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨j, rfl⟩ := h hx
  rcases g with i | i
  · have heq : r i * r j * (r i)⁻¹ = r j := by
      rw [inv_r, r_mul_r, r_mul_r]
      congr 1
      ring
    rw [heq]
    exact hx
  · have heq : sr i * r j * (sr i)⁻¹ = (r j)⁻¹ := by
      rw [inv_sr, sr_mul_r, sr_mul_sr, inv_r]
      congr 1
      ring
    rw [heq]
    exact inv_mem hx

theorem le_rotations_of_isCyclic {m : ℕ} {C : Subgroup (DihedralGroup m)} [Finite C]
    (hC : IsCyclic C) (h2 : 2 < Nat.card C) : C ≤ rotations m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have htop : zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hg])
  have hgr : (g : DihedralGroup m) ∈ rotations m := by
    rcases hgv : (g : DihedralGroup m) with k | k
    · exact ⟨k, rfl⟩
    · exfalso
      have h1 : orderOf (g : DihedralGroup m) = 2 := by rw [hgv]; exact orderOf_sr k
      rw [Subgroup.orderOf_coe, hg] at h1
      omega
  intro x hx
  have hmem : (⟨x, hx⟩ : C) ∈ zpowers g := htop ▸ mem_top _
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmem
  have hx' : x = (g : DihedralGroup m) ^ n := by
    rw [← Subgroup.coe_zpow, hn]
  rw [hx']
  exact zpow_mem hgr n

theorem card_center_dihedralGroup {m : ℕ} (heven : Even m) (hm2 : m ≠ 2) (hm0 : m ≠ 0) :
    Nat.card (center (DihedralGroup m)) = 2 := by
  rw [center_eq_closure_of_even_ne_two heven hm2, Nat.card_zpowers]
  obtain ⟨k, rfl⟩ := heven
  have hk : 0 < k := by omega
  have hdiv : (k + k) / 2 = k := by omega
  rw [hdiv]
  apply orderOf_eq_prime
  · rw [r_pow, one_def]
    congr 1
    have h1 : ((k : ZMod (k + k)) * ((2 : ℕ) : ZMod (k + k))) = ((k + k : ℕ) : ZMod (k + k)) := by
      push_cast
      ring
    rw [h1, ZMod.natCast_self]
  · rw [one_def]
    intro h
    have h1 : ((k : ℕ) : ZMod (k + k)) = 0 := r.inj h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd hk h1
    omega

end Dihedral

section Quaternion

open QuaternionGroup

variable {X : Type*} [Group X]

theorem card_le_two_of_quaternion {m : ℕ} [NeZero m] {P E : Subgroup X}
    (e : P ≃* QuaternionGroup m) (hEP : E ≤ P) (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  set E' := (E.subgroupOf P).map e.toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E := by
    rw [hE', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv]
  have hE'2 : ∀ y ∈ E', y ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x ^ 2 = 1 := Subtype.ext (by simpa using hE x hx)
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, h1, map_one]
  have hle : E' ≤ zpowers (a 1 : QuaternionGroup m) := by
    intro y hy
    rcases y with i | i
    · refine mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, a_one_pow, ZMod.natCast_zmod_val]
    · exfalso
      have h1 := hE'2 _ hy
      rw [xa_sq, ← a_zero] at h1
      have h2 : ((m : ℕ) : ZMod (2 * m)) = 0 := a.inj h1
      rw [ZMod.natCast_eq_zero_iff] at h2
      have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      have := Nat.le_of_dvd hm h2
      omega
  rw [← hcard]
  exact card_le_two_of_isCyclic hle (isCyclic_zpowers _) hE'2

end Quaternion

end CFSG.ComponentClassification.Asc76.Lemma22
