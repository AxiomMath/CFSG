module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Dichotomy.Generic

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup
open scoped commutatorElement

namespace ZTwoAux

variable {G : Type} [Group G]

theorem inv_eq_self_of_sq_eq_one {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h)

theorem comm_of_sq_eq_one {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have h1 := inv_eq_self_of_sq_eq_one hab
  rw [mul_inv_rev, inv_eq_self_of_sq_eq_one ha, inv_eq_self_of_sq_eq_one hb] at h1
  exact h1.symm

theorem comm_of_exp_two {U : Subgroup G} (hU : ∀ u ∈ U, u ^ 2 = 1) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) : a * b = b * a :=
  comm_of_sq_eq_one (hU a ha) (hU b hb) (hU _ (U.mul_mem ha hb))

theorem mem_zpowers_iff_of_sq_eq_one {g h : G} (hg : g ^ 2 = 1) :
    h ∈ zpowers g ↔ h = 1 ∨ h = g := by
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · left
      rw [zpow_mul]
      simp [hg]
    · right
      rw [zpow_add, zpow_mul]
      simp [hg]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem zpowers_le_normalizer_zpowers {a b : G} (h : a * b = b * a) :
    zpowers a ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
  intro g hg
  refine A3Dich.mem_normalizer_of_forall_comm fun c hc => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((Commute.zpow_zpow (show Commute a b from h) m n))

theorem mem_conj_self {A : Subgroup G} {g a : G} (ha : a ∈ A) :
    g⁻¹ * a * g ∈ conjSubgroup A g := by
  have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  rw [mem_conjSubgroup_iff, e]
  exact ha

theorem conj_eq_of_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b * a = b := by
  calc a⁻¹ * b * a = a⁻¹ * (b * a) := by rw [mul_assoc]
    _ = a⁻¹ * (a * b) := by rw [h]
    _ = b := by group

theorem mem_normalizer_zpowers_of_comm {g y : G} (hg : g * y = y * g) :
    g ∈ normalizer ((zpowers y : Subgroup G) : Set G) :=
  A3Dich.mem_normalizer_of_forall_comm fun b hb => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute g y from hg) n).eq

theorem exp_conjSubgroup {A : Subgroup G} (hA : ∀ a ∈ A, a ^ 2 = 1) (g : G) :
    ∀ v ∈ conjSubgroup A g, v ^ 2 = 1 := by
  intro v hv
  rw [mem_conjSubgroup_iff] at hv
  have h1 := hA _ hv
  rw [pow_two] at h1 ⊢
  have h2 : g * (v * v) * g⁻¹ = 1 := by rw [← h1]; group
  have h3 : v * v = g⁻¹ * (g * (v * v) * g⁻¹) * g := by group
  rw [h3, h2]
  group

variable [Finite G]

theorem eq_zpowers_sup_zpowers {U : Subgroup G} (hU : Nat.card U = 4) (hexp : ∀ u ∈ U, u ^ 2 = 1)
    {z w : G} (hz : z ∈ U) (hw : w ∈ U) (hz1 : z ≠ 1) (hwz : w ∉ zpowers z) :
    U = zpowers z ⊔ zpowers w := by
  have hzc : z * w = w * z := comm_of_exp_two hexp hz hw
  have hle : zpowers z ≤ normalizer ((zpowers w : Subgroup G) : Set G) :=
    zpowers_le_normalizer_zpowers hzc
  have hz2 : z ^ 2 = 1 := hexp z hz
  have hw2 : w ^ 2 = 1 := hexp w hw
  have hcz : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ one_mem _)
  have hcw : Nat.card (zpowers w) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hw2 hw1
  have hinf : zpowers z ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rcases (mem_zpowers_iff_of_sq_eq_one hz2).mp hg.1 with h | h
    · exact h
    · exfalso
      rcases (mem_zpowers_iff_of_sq_eq_one hw2).mp hg.2 with h' | h'
      · exact hz1 (h.symm.trans h')
      · have : w = z := h'.symm.trans h
        exact hwz (by rw [this]; exact mem_zpowers z)
  have hprod := A3Gen.card_sup_mul_card_inf_of_le_normalizer' hle
  rw [hinf, Subgroup.card_bot, hcz, hcw] at hprod
  have hV : Nat.card ↥(zpowers z ⊔ zpowers w) = 4 := by omega
  have hVU : zpowers z ⊔ zpowers w ≤ U := sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hw)
  exact (Subgroup.eq_of_le_of_card_ge hVU (by omega)).symm

theorem mem_klein_iff {U : Subgroup G} (hU : Nat.card U = 4) (hexp : ∀ u ∈ U, u ^ 2 = 1)
    {z w : G} (hz : z ∈ U) (hw : w ∈ U) (hz1 : z ≠ 1) (hwz : w ∉ zpowers z) {g : G} :
    g ∈ U ↔ g = 1 ∨ g = z ∨ g = w ∨ g = z * w := by
  have hzc : z * w = w * z := comm_of_exp_two hexp hz hw
  have hle : zpowers z ≤ normalizer ((zpowers w : Subgroup G) : Set G) :=
    zpowers_le_normalizer_zpowers hzc
  have hz2 : z ^ 2 = 1 := hexp z hz
  have hw2 : w ^ 2 = 1 := hexp w hw
  rw [eq_zpowers_sup_zpowers hU hexp hz hw hz1 hwz, A3Dich.mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases (mem_zpowers_iff_of_sq_eq_one hz2).mp ha with rfl | rfl <;>
      rcases (mem_zpowers_iff_of_sq_eq_one hw2).mp hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
    · exact ⟨g, mem_zpowers g, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, g, mem_zpowers g, by simp⟩
    · exact ⟨z, mem_zpowers z, w, mem_zpowers w, rfl⟩

theorem mem_normalizer_of_conjSubgroup_le {A : Subgroup G} {n : G} (h : conjSubgroup A n ≤ A) :
    n ∈ normalizer (A : Set G) := by
  have hc : conjSubgroup A n = A :=
    Subgroup.eq_of_le_of_card_ge h (by rw [A3Dich.card_conjSubgroup])
  exact conjSubgroup_eq_iff_mem_normalizer.mp hc

omit [Finite G] in
theorem le_normalizer_of_commutator_le {T K : Subgroup G} (hKT : K ≤ T) (hc : ⁅T, T⁆ ≤ K) :
    T ≤ normalizer (K : Set G) := by
  have key : ∀ g ∈ T, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have h1 : ⁅g, k⁆ ∈ K := hc (Subgroup.commutator_mem_commutator hg (hKT hk))
    have e : g * k * g⁻¹ = ⁅g, k⁆ * k := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem h1 hk
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact key g hg k hk
  · intro hk
    have := key g⁻¹ (T.inv_mem hg) _ hk
    simpa [mul_assoc] using this

end ZTwoAux

end CFSG.QuasithinUnique
