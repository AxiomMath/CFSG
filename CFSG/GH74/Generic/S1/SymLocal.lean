module

public import CFSG.GH74.Generic.S1.SymCore
public import CFSG.GH74.Generic.S1.Props

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

section Bar

variable {G : Type} [Group G]

theorem barOf_mul {x u v : G} (hu : u ∈ centralizer ({x} : Set G))
    (hv : v ∈ centralizer ({x} : Set G)) :
    barOf hu * barOf hv = barOf (mul_mem hu hv) := rfl

theorem barOf_self (x : G) (hx : x ∈ centralizer ({x} : Set G)) : barOf hx = xbar x := rfl

theorem eq_one_or_eq_of_mem_zpowers {C : Type*} [Group C] {a z : C} (ha : a * a = 1)
    (hz : z ∈ Subgroup.zpowers a) : z = 1 ∨ z = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact ha
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [_root_.zpow_mul]
    simp [ha2]
  · right
    rw [_root_.zpow_add, _root_.zpow_mul]
    simp [ha2]

variable [Finite G]

theorem eq_one_of_barOf_eq_one {x u : G} (hu : u ∈ centralizer ({x} : Set G)) (hu2 : u * u = 1)
    (h : barOf hu = 1) : u = 1 := by
  have hodd := proj_odd x ⟨u, hu⟩ h
  have hdvd : orderOf (⟨u, hu⟩ : ↥(centralizer ({x} : Set G))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext hu2)
  have h1 : orderOf (⟨u, hu⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)

theorem barOf_ne_xbar {x v : G} (hx : orderOf x = 2) (hv : v ∈ centralizer ({x} : Set G))
    (hv2 : v * v = 1) (hvx : v ≠ x) : barOf hv ≠ xbar x := by
  intro h
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hxm : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hvx' : v * x = x * v := mem_centralizer_singleton_iff.1 hv
  have h1 : barOf (mul_mem hv hxm) = 1 := by
    rw [← barOf_mul hv hxm, h, barOf_self x hxm]
    exact xbar_mul_self hx
  have h2 : (v * x) * (v * x) = 1 := by
    calc v * x * (v * x) = v * (x * v) * x := by group
      _ = v * (v * x) * x := by rw [hvx']
      _ = (v * v) * (x * x) := by group
      _ = 1 := by rw [hv2, hxx, one_mul]
  have h3 := eq_one_of_barOf_eq_one (mul_mem hv hxm) h2 h1
  apply hvx
  calc v = v * x * x⁻¹ := by group
    _ = x⁻¹ := by rw [h3, one_mul]
    _ = x := inv_eq_of_mul_eq_one_right hxx

end Bar

variable {G : Type} [Group G] [Finite G]

theorem barOf_notMem {y : G} {K : Subgroup (CentralizerBar y)} (hset : S1Setup G y K)
    (hfront : S1Front G y K) {v : G} (hv : v ∈ centralizer ({y} : Set G)) (hv2 : v * v = 1)
    (hconj : IsConj y v) (hvy : v ≠ y) : barOf hv ∉ K := fun hmem =>
  hfront.b5 v hv hv2 hmem (barOf_ne_xbar hset.inv hv hv2 hvy) hconj

theorem sym_local {y : G} {K : Subgroup (CentralizerBar y)} [K.Normal] (hset : S1Setup G y K)
    (hfront : S1Front G y K) {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}
    (ops : ModelOps F S) (e : ↥K ≃* ↥S) (w : Fin 4 → G)
    (hw : ∀ j, w j ∈ centralizer ({y} : Set G)) (hw2 : ∀ j, w j * w j = 1)
    (hwc : ∀ j k, w j * w k = w k * w j) (hwconj : ∀ j, IsConj y (w j)) (hwne : ∀ j, w j ≠ y)
    (hind2 : ∀ j k, j ≠ k → w j * w k ≠ 1) (hind3 : ∀ j k, j ≠ k → w j * w k * y ≠ 1)
    (hprod : w 0 * w 1 * w 2 * w 3 = y)
    (hR : ∀ j, IsReflection S (MulAut.congr e (MulAut.conjNormal (barOf (hw j)) : MulAut ↥K))) :
    (∀ j, IsConj y (w j) ∧ w j * w j = 1 ∧ barOf (hw j) ∉ K) ∧
      (∀ j k, w j * w k = w k * w j) ∧ w 0 * w 1 * w 2 * w 3 = y ∧
        (∀ j k, j ≠ k → w j ≠ w k) ∧
          ∃ e'' : ↥K ≃* ↥S, ∀ j, ActsAsReflOn e'' (barOf (hw j)) (reflDiag F j) := by
  classical
  have hy2 : orderOf y = 2 := hset.inv
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have hym : y ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hnotK : ∀ j, barOf (hw j) ∉ K := fun j =>
    barOf_notMem hset hfront (hw j) (hw2 j) (hwconj j) (hwne j)
  have hbinv : ∀ j, (barOf (hw j))⁻¹ = barOf (hw j) := fun j =>
    inv_eq_of_mul_eq_one_right (barOf_mul_self (hw j) (hw2 j))
  have hnormal : ∀ j, ∀ n : ↥K, barOf (hw j) * (n : CentralizerBar y) * (barOf (hw j))⁻¹ ∈ K :=
    fun j n => (inferInstance : K.Normal).conj_mem n n.2 (barOf (hw j))
  have hrefl : ∀ j, ∃ ρ : GL (Fin 4) F, ρ * ρ = 1 ∧ ((ρ : Matrix (Fin 4) (Fin 4) F)).det = -1 ∧
      ∀ n n' : ↥K, barOf (hw j) * (n : CentralizerBar y) * (barOf (hw j))⁻¹ = (n' : CentralizerBar y) →
        ((e n' : ↥S) : GL (Fin 4) F) = ρ * ((e n : ↥S) : GL (Fin 4) F) * ρ⁻¹ := by
    intro j
    obtain ⟨ρ, hρ2, hρdet, hρact⟩ := hR j
    refine ⟨ρ, hρ2, hρdet, fun n n' hn => ?_⟩
    have h1 : (MulAut.conjNormal (barOf (hw j)) : MulAut ↥K) n = n' := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      exact hn)
    have h2 := hρact (e n)
    have h3 : (MulAut.congr e (MulAut.conjNormal (barOf (hw j)) : MulAut ↥K)) (e n) = e n' := by
      simp [MulAut.congr_apply, h1]
    rw [h3] at h2
    exact h2
  have hcomm : ∀ j k, barOf (hw j) * barOf (hw k) = barOf (hw k) * barOf (hw j) := by
    intro j k
    rw [barOf_mul, barOf_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (hwc j k))
  have hyc : ∀ j, w j * y = y * w j := fun j => mem_centralizer_singleton_iff.1 (hw j)
  have hdist : ∀ j k, j ≠ k → ∃ n : ↥K, barOf (hw j) * (n : CentralizerBar y) * (barOf (hw j))⁻¹ ≠
      barOf (hw k) * (n : CentralizerBar y) * (barOf (hw k))⁻¹ := by
    intro j k hjk
    by_contra hcon
    push Not at hcon
    have hkk : barOf (hw k) * barOf (hw k) = 1 := barOf_mul_self (hw k) (hw2 k)
    have hz : barOf (hw k) * barOf (hw j) ∈ Subgroup.centralizer (K : Set (CentralizerBar y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := hcon ⟨n, hn⟩
      change barOf (hw j) * n * (barOf (hw j))⁻¹ = barOf (hw k) * n * (barOf (hw k))⁻¹ at h1
      symm
      calc barOf (hw k) * barOf (hw j) * n
          = barOf (hw k) * (barOf (hw j) * n * (barOf (hw j))⁻¹) * barOf (hw j) := by group
        _ = barOf (hw k) * (barOf (hw k) * n * (barOf (hw k))⁻¹) * barOf (hw j) := by rw [h1]
        _ = (barOf (hw k) * barOf (hw k)) * n * (barOf (hw k))⁻¹ * barOf (hw j) := by group
        _ = n * (barOf (hw k) * barOf (hw j)) := by rw [hkk, one_mul, hbinv k, mul_assoc]
    rw [hfront.cent_eq] at hz
    have hsq : (w k * w j) * (w k * w j) = 1 := by
      calc w k * w j * (w k * w j) = w k * (w j * w k) * w j := by group
        _ = w k * (w k * w j) * w j := by rw [hwc j k]
        _ = (w k * w k) * (w j * w j) := by group
        _ = 1 := by rw [hw2 k, hw2 j, one_mul]
    rcases eq_one_or_eq_of_mem_zpowers (xbar_mul_self hy2) hz with h1 | h1
    · rw [barOf_mul] at h1
      exact hind2 k j (Ne.symm hjk) (eq_one_of_barOf_eq_one _ hsq h1)
    · rw [barOf_mul] at h1
      have h2 : barOf (mul_mem (mul_mem (hw k) (hw j)) hym) = 1 := by
        rw [← barOf_mul (mul_mem (hw k) (hw j)) hym, h1, barOf_self y hym]
        exact xbar_mul_self hy2
      have hycomm : y * (w k * w j) = (w k * w j) * y := by
        calc y * (w k * w j) = (y * w k) * w j := (mul_assoc _ _ _).symm
          _ = (w k * y) * w j := by rw [hyc k]
          _ = w k * (y * w j) := mul_assoc _ _ _
          _ = w k * (w j * y) := by rw [hyc j]
          _ = (w k * w j) * y := (mul_assoc _ _ _).symm
      have h3 : (w k * w j * y) * (w k * w j * y) = 1 := by
        calc w k * w j * y * (w k * w j * y) = (w k * w j) * (y * (w k * w j)) * y := by group
          _ = (w k * w j) * ((w k * w j) * y) * y := by rw [hycomm]
          _ = ((w k * w j) * (w k * w j)) * (y * y) := by group
          _ = 1 := by rw [hsq, hyy, one_mul]
      exact hind3 k j (Ne.symm hjk) (eq_one_of_barOf_eq_one _ h3 h2)
  obtain ⟨e'', he''⟩ := sym_core ops e (fun j => barOf (hw j)) hnormal hrefl hcomm hdist
  refine ⟨fun j => ⟨hwconj j, hw2 j, hnotK j⟩, hwc, hprod, ?_, e'', fun j n n' hn => he'' j n n' hn⟩
  intro j k hjk heq
  apply hind2 j k hjk
  rw [← heq]
  exact hw2 j

end CFSG.GH74.Generic.S1
