module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure CentFacts (D : Type) [Group D] : Prop where
  not_dvd : ¬ 2 ^ 12 ∣ Nat.card D
  core : ∃ N : Subgroup D, N.Normal ∧
    (∀ (R : Type) [Group R] [Finite R], Nat.card R ≤ 23040 → ∀ f : ↥N →* R, f = 1) ∧
    (∃ S : Subgroup D, S ≤ N ∧ IsPGroup 2 S ∧
      ∀ M : Subgroup D, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S) ∧
    (7 ∣ Nat.card N ∨ 11 ∣ Nat.card N) ∧
    (∀ M : Subgroup D, M.Normal → 4 < Nat.card M → N ≤ M)

structure CentConfig (X : Type) [Group X] [Finite X] (a b : X) (E : Subgroup X)
    (Fus : X → Prop) : Prop where
  a_sq : a * a = 1
  a_ne : a ≠ 1
  b_sq : b * b = 1
  b_ne : b ≠ 1
  b_mem : b ∈ E
  b_central : b ∈ center X
  cent_a : centralizer ({a} : Set X) = zpowers a ⊔ E
  disj : Disjoint (zpowers a) E
  E_two : IsTwoSp62 ↥E
  kgroupCat : CFSG.SectionRank.IsKGroupCat X
  oddCore : standardComponentOddCore X = ⊥
  two_pow : 2 ^ 12 ∣ Nat.card X
  fus_a : Fus a
  fus_b : ¬ Fus b
  fus : ∀ w, Fus w → w * w = 1 ∧ w ≠ 1 ∧ CentFacts ↥(centralizer ({w} : Set X))

@[expose] def TransferWitness (X : Type) [Group X] [Finite X] (a : X) (Fus : X → Prop) : Prop :=
  ∃ S : Sylow 2 X, a ∈ (S : Subgroup X) ∧ ∃ U : Subgroup X, U ≤ (S : Subgroup X) ∧
    U.relIndex (S : Subgroup X) = 2 ∧ a ∉ U ∧ ∀ w ∈ U, ¬ Fus w

@[expose] def FixLarge (K : Type) [Group K] : Prop :=
  ∀ ζ : MulAut K, ζ * ζ = 1 → 4 < Nat.card (fixedSubgroup ζ)

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

private theorem zpowers_sq_eq_one_or {x : X} (hx : x * x = 1) {c : X}
    (hc : c ∈ zpowers x) : c = 1 ∨ c = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem exists_mul_of_mem_sup_of_le_centralizer {T C : Subgroup X}
    (hC : C ≤ centralizer (T : Set X)) {x : X} (hx : x ∈ T ⊔ C) :
    ∃ t ∈ T, ∃ c ∈ C, x = t * c := by
  have hTC : T ≤ normalizer (C : Set X) := fun t ht =>
    centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hC) ht)
  have hx' : x ∈ ((T ⊔ C : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T C hTC] at hx'
  obtain ⟨t, ht, c, hc, rfl⟩ := hx'
  exact ⟨t, ht, c, hc, rfl⟩

theorem a_comm (h : CentConfig X a b E Fus) {e : X} (he : e ∈ E) : e * a = a * e := by
  have he' : e ∈ centralizer ({a} : Set X) := by
    rw [h.cent_a]
    exact Subgroup.mem_sup_right he
  exact Subgroup.mem_centralizer_singleton_iff.mp he'

private theorem E_le_centralizer_zpowers (h : CentConfig X a b E Fus) :
    E ≤ centralizer (zpowers a : Set X) := by
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_iff.mpr fun e he => h.a_comm he

theorem center_E (h : CentConfig X a b E Fus) {y : X} (hy : y ∈ E)
    (hc : ∀ x ∈ E, x * y = y * x) : y = 1 ∨ y = b := by
  let yE : ↥E := ⟨y, hy⟩
  let bE : ↥E := ⟨b, h.b_mem⟩
  have hcard : Nat.card (Subgroup.center ↥E) = 2 := h.E_two.2.1
  have hyc : yE ∈ Subgroup.center ↥E :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  have hbc : bE ∈ Subgroup.center ↥E :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_center_iff.mp h.b_central (g : X))
  have hb_ne : (⟨bE, hbc⟩ : Subgroup.center ↥E) ≠ 1 := by
    intro hh
    have h1 : bE = 1 := Subtype.ext_iff.mp hh
    exact h.b_ne (by simpa [bE] using congrArg (fun z : ↥E => (z : X)) h1)
  obtain ⟨w, _hw_ne, hw_unique⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.center ↥E)).mp hcard
  by_cases hy1 : (⟨yE, hyc⟩ : Subgroup.center ↥E) = 1
  · left
    have h1 : yE = 1 := Subtype.ext_iff.mp hy1
    simpa [yE] using congrArg (fun z : ↥E => (z : X)) h1
  · right
    have hyw : (⟨yE, hyc⟩ : Subgroup.center ↥E) = w := hw_unique _ hy1
    have hbw : (⟨bE, hbc⟩ : Subgroup.center ↥E) = w := hw_unique _ hb_ne
    have h1 : (⟨yE, hyc⟩ : Subgroup.center ↥E) = ⟨bE, hbc⟩ := by rw [hyw, hbw]
    have h2 : yE = bE := Subtype.ext_iff.mp h1
    simpa [yE, bE] using congrArg (fun z : ↥E => (z : X)) h2

theorem cent_cent_E (h : CentConfig X a b E Fus) {x : X} (hxa : x * a = a * x)
    (hxE : ∀ e ∈ E, x * e = e * x) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hx_cent : x ∈ centralizer ({a} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxa
  have hx_sup : x ∈ zpowers a ⊔ E := by
    rw [← h.cent_a]
    exact hx_cent
  obtain ⟨c, hc, e, he, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (E_le_centralizer_zpowers h) hx_sup
  have hcE : c ∈ centralizer (E : Set X) :=
    (Subgroup.le_centralizer_iff.mp (E_le_centralizer_zpowers h)) hc
  have hec : ∀ z ∈ E, z * e = e * z := by
    intro z hz
    have h1 : e * z = z * e := by
      apply mul_left_cancel (a := c)
      have h0 : (c * e) * z = z * (c * e) := hxE z hz
      have h2 : z * c = c * z := Subgroup.mem_centralizer_iff.mp hcE z hz
      calc c * (e * z) = (c * e) * z := (mul_assoc c e z).symm
        _ = z * (c * e) := h0
        _ = (z * c) * e := (mul_assoc z c e).symm
        _ = (c * z) * e := by rw [h2]
        _ = c * (z * e) := mul_assoc c z e
    exact h1.symm
  rcases h.center_E he hec with he1 | heb
  · rcases zpowers_sq_eq_one_or h.a_sq hc with hc1 | hca
    · left; rw [hc1, he1, one_mul]
    · right; left; rw [hca, he1, mul_one]
  · rcases zpowers_sq_eq_one_or h.a_sq hc with hc1 | hca
    · right; right; left; rw [hc1, heb, one_mul]
    · right; right; right; rw [hca, heb]

theorem card_le_four (h : CentConfig X a b E Fus) {W : Subgroup X}
    (hWa : W ≤ centralizer ({a} : Set X)) (hWE : W ≤ centralizer (E : Set X)) :
    Nat.card W ≤ 4 := by
  have hsub : (W : Set X) ⊆ ({1, a, b, a * b} : Set X) := by
    intro x hx
    have hxa : x * a = a * x := by
      have h' := hWa hx
      rwa [Subgroup.mem_centralizer_singleton_iff] at h'
    have hxE : ∀ e ∈ E, x * e = e * x := by
      intro e he
      have h' := hWE hx
      rw [Subgroup.mem_centralizer_iff] at h'
      exact (h' e he).symm
    rcases h.cent_cent_E hxa hxE with rfl | rfl | rfl | rfl <;> simp
  calc Nat.card W = (W : Set X).ncard := rfl
    _ ≤ ({1, a, b, a * b} : Set X).ncard := Set.ncard_le_ncard hsub
    _ ≤ 4 := by
      show (insert (1 : X) (insert a (insert b ({a * b} : Set X)))).ncard ≤ 4
      have h1 := Set.ncard_insert_le (1 : X) (insert a (insert b ({a * b} : Set X)))
      have h2 := Set.ncard_insert_le (a : X) (insert b ({a * b} : Set X))
      have h3 := Set.ncard_insert_le (b : X) ({a * b} : Set X)
      rw [Set.ncard_singleton] at h3
      omega

theorem normal_subgroupOf (h : CentConfig X a b E Fus) :
    (E.subgroupOf (centralizer ({a} : Set X))).Normal := by
  have hEK : E ≤ centralizer ({a} : Set X) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.a_comm he)
  refine (Subgroup.normal_subgroupOf_iff hEK).mpr fun n k hn hk => ?_
  have hk_sup : k ∈ zpowers a ⊔ E := by
    rw [← h.cent_a]
    exact hk
  obtain ⟨c, hc, e, he, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (E_le_centralizer_zpowers h) hk_sup
  have hcE : c ∈ centralizer (E : Set X) :=
    (Subgroup.le_centralizer_iff.mp (E_le_centralizer_zpowers h)) hc
  have hm : e * n * e⁻¹ ∈ E := E.mul_mem (E.mul_mem he hn) (E.inv_mem he)
  have hcomm : (e * n * e⁻¹) * c = c * (e * n * e⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hcE _ hm
  have heq : (c * e) * n * (c * e)⁻¹ = e * n * e⁻¹ := by
    rw [mul_inv_rev]
    calc (c * e) * n * (e⁻¹ * c⁻¹)
        = c * (e * n * e⁻¹) * c⁻¹ := by group
      _ = (e * n * e⁻¹) * c * c⁻¹ := by rw [← hcomm]
      _ = e * n * e⁻¹ := by group
  rw [heq]
  exact hm

theorem isQuasisimple_E (h : CentConfig X a b E Fus) : CFSG.Open.IsQuasisimple ↥E := by
  refine ⟨h.E_two.1, ?_⟩
  exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h.E_two.2.2

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
