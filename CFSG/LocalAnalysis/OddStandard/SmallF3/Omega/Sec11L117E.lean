module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_isElemAbelianMod_mono {z : G} {U V : Subgroup G} (hVU : V ≤ U)
    (hU : IsElemAbelianMod z U) : IsElemAbelianMod z V :=
  fun a ha b hb => hU a (hVU ha) b (hVU hb)

theorem sec11_isElemAbelianMod_closure {z : G} {S : Set G} (hzS : ∀ a ∈ S, a * z = z * a)
    (hsq : ∀ a ∈ S, a * a ∈ zpowers z)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) :
    IsElemAbelianMod z (Subgroup.closure S) := by
  have hzc : ∀ x ∈ Subgroup.closure S, x * z = z * x := by
    intro x hx
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzS a ha)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hNc : ∀ n ∈ zpowers z, ∀ x ∈ Subgroup.closure S, x * n = n * x := by
    intro n hn x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((show Commute x z from hzc x hx).zpow_right k).eq
  have hNconj : ∀ n ∈ zpowers z, ∀ x ∈ Subgroup.closure S, x * n * x⁻¹ = n := by
    intro n hn x hx
    rw [hNc n hn x hx, mul_inv_cancel_right]
  have stage1 : ∀ a ∈ S, ∀ y ∈ Subgroup.closure S, a * y * a⁻¹ * y⁻¹ ∈ zpowers z := by
    intro a ha y hy
    refine Subgroup.closure_induction
      (p := fun y _ => a * y * a⁻¹ * y⁻¹ ∈ zpowers z) ?_ ?_ ?_ ?_ hy
    · intro b hb
      exact hcomm a ha b hb
    · simp
    · intro y1 y2 hy1 hy2 h1 h2
      have e : a * (y1 * y2) * a⁻¹ * (y1 * y2)⁻¹ =
          (a * y1 * a⁻¹ * y1⁻¹) * (y1 * (a * y2 * a⁻¹ * y2⁻¹) * y1⁻¹) := by group
      rw [e, hNconj _ h2 y1 hy1]
      exact Subgroup.mul_mem _ h1 h2
    · intro y1 hy1 h1
      have e : a * y1⁻¹ * a⁻¹ * (y1⁻¹)⁻¹ =
          y1⁻¹ * (a * y1 * a⁻¹ * y1⁻¹)⁻¹ * (y1⁻¹)⁻¹ := by group
      have h' : (a * y1 * a⁻¹ * y1⁻¹)⁻¹ ∈ zpowers z := Subgroup.inv_mem _ h1
      rw [e, hNconj _ h' y1⁻¹ (Subgroup.inv_mem _ hy1)]
      exact h'
  have stage2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S,
      x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
    intro x hx y hy
    refine Subgroup.closure_induction
      (p := fun x _ => x * y * x⁻¹ * y⁻¹ ∈ zpowers z) ?_ ?_ ?_ ?_ hx
    · intro a ha
      exact stage1 a ha y hy
    · simp
    · intro x1 x2 hx1 hx2 h1 h2
      have e : x1 * x2 * y * (x1 * x2)⁻¹ * y⁻¹ =
          (x1 * (x2 * y * x2⁻¹ * y⁻¹) * x1⁻¹) * (x1 * y * x1⁻¹ * y⁻¹) := by group
      rw [e, hNconj _ h2 x1 hx1]
      exact Subgroup.mul_mem _ h2 h1
    · intro x1 hx1 h1
      have e : x1⁻¹ * y * (x1⁻¹)⁻¹ * y⁻¹ =
          x1⁻¹ * (x1 * y * x1⁻¹ * y⁻¹)⁻¹ * (x1⁻¹)⁻¹ := by group
      have h' : (x1 * y * x1⁻¹ * y⁻¹)⁻¹ ∈ zpowers z := Subgroup.inv_mem _ h1
      rw [e, hNconj _ h' x1⁻¹ (Subgroup.inv_mem _ hx1)]
      exact h'
  have hsqc : ∀ x ∈ Subgroup.closure S, x * x ∈ zpowers z := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x * x ∈ zpowers z) ?_ ?_ ?_ ?_ hx
    · exact hsq
    · simp
    · intro x1 x2 hx1 hx2 h1 h2
      have hc := stage2 x2 hx2 x1 hx1
      have e1 : x2 * x1 = (x2 * x1 * x2⁻¹ * x1⁻¹) * (x1 * x2) := by group
      have e : x1 * x2 * (x1 * x2) =
          (x2 * x1 * x2⁻¹ * x1⁻¹) * (x1 * x1) * (x2 * x2) := by
        calc x1 * x2 * (x1 * x2) = x1 * (x2 * x1) * x2 := by group
          _ = x1 * ((x2 * x1 * x2⁻¹ * x1⁻¹) * (x1 * x2)) * x2 := by rw [← e1]
          _ = (x1 * (x2 * x1 * x2⁻¹ * x1⁻¹)) * x1 * x2 * x2 := by group
          _ = ((x2 * x1 * x2⁻¹ * x1⁻¹) * x1) * x1 * x2 * x2 := by rw [hNc _ hc x1 hx1]
          _ = (x2 * x1 * x2⁻¹ * x1⁻¹) * (x1 * x1) * (x2 * x2) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc h1) h2
    · intro x1 hx1 h1
      rw [← mul_inv_rev]
      exact Subgroup.inv_mem _ h1
  exact fun a ha b hb => ⟨stage2 a ha b hb, hsqc a ha⟩

theorem sec11_isElemAbelianMod_sup {z : G} {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hzA : ∀ a ∈ A, a * z = z * a)
    (hzB : ∀ b ∈ B, b * z = z * b) (hA : IsElemAbelianMod z A) (hB : IsElemAbelianMod z B) :
    IsElemAbelianMod z (A ⊔ B) := by
  have hsup : A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup]
  refine sec11_isElemAbelianMod_closure ?_ ?_ ?_
  · rintro a (ha | hb)
    · exact hzA a ha
    · exact hzB a hb
  · rintro a (ha | hb)
    · exact (hA a ha a ha).2
    · exact (hB a hb a hb).2
  · rintro a (ha | ha) b (hb | hb)
    · exact (hA a ha b hb).1
    · have e : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hcomm a ha b hb]; group
      rw [e]
      exact Subgroup.one_mem _
    · have e : a * b * a⁻¹ * b⁻¹ = 1 := by rw [← hcomm b hb a ha]; group
      rw [e]
      exact Subgroup.one_mem _
    · exact (hB a ha b hb).1

theorem sec11_isElemAbelianMod_map {z m : G} (hmz : m * z * m⁻¹ = z) {U : Subgroup G}
    (hU : IsElemAbelianMod z U) :
    IsElemAbelianMod z (U.map (MulAut.conj m).toMonoidHom) := by
  have hz : ∀ w ∈ zpowers z, m * w * m⁻¹ ∈ zpowers z := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← conj_zpow, hmz]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  intro a' ha' b' hb'
  obtain ⟨a, haU, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b, hbU, rfl⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨hc, hs⟩ := hU a haU b hbU
  refine ⟨?_, ?_⟩
  · show (m * a * m⁻¹) * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ ∈ zpowers z
    have e : (m * a * m⁻¹) * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ =
        m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ := by group
    rw [e]
    exact hz _ hc
  · show (m * a * m⁻¹) * (m * a * m⁻¹) ∈ zpowers z
    have e : (m * a * m⁻¹) * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
    rw [e]
    exact hz _ hs

theorem sec11_isPGroup_of_isElemAbelianMod [Finite G] {z : G} (hz2 : z * z = 1) {U : Subgroup G}
    (hU : IsElemAbelianMod z U) : IsPGroup 2 U := by
  intro g
  refine ⟨2, ?_⟩
  have hs : (g : G) * g ∈ zpowers z := (hU g g.2 g g.2).2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hz2z : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  have h4 : (g : G) ^ 4 = 1 := by
    have e : (g : G) ^ 4 = ((g : G) * g) * ((g : G) * g) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e, ← hk, ← zpow_add, ← two_mul, zpow_mul, hz2z, one_zpow]
  apply Subtype.ext
  simpa using h4

end CFSG.OddStandard.SmallF3.Omega
