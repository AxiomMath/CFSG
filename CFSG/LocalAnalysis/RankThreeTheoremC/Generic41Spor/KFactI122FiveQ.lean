module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Int.Interval

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

private theorem pow_mul_formula_aux {G : Type*} [Group G] (n w z : G)
    (hzn : Commute z n) (hzw : Commute z w) (hwn : w * n = z * n * w) (k : ℕ) :
    (n * w) ^ k = z ^ (k.choose 2) * n ^ k * w ^ k := by
  have hw : ∀ m : ℕ, w ^ m * n = z ^ m * n * w ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hc : w * z ^ m = z ^ m * w := ((hzw.pow_left m).eq).symm
      calc w ^ (m + 1) * n = w * (w ^ m * n) := by rw [pow_succ', mul_assoc]
        _ = w * (z ^ m * n * w ^ m) := by rw [ih]
        _ = (w * z ^ m) * n * w ^ m := by simp only [mul_assoc]
        _ = (z ^ m * w) * n * w ^ m := by rw [hc]
        _ = z ^ m * (w * n) * w ^ m := by simp only [mul_assoc]
        _ = z ^ m * (z * n * w) * w ^ m := by rw [hwn]
        _ = (z ^ m * z) * n * (w * w ^ m) := by simp only [mul_assoc]
        _ = z ^ (m + 1) * n * w ^ (m + 1) := by rw [← pow_succ, ← pow_succ']
  induction k with
  | zero => simp
  | succ k ih =>
    have hC : (k + 1).choose 2 = k.choose 2 + k := by
      rw [show (k + 1).choose 2 = k.choose 1 + k.choose 2 from Nat.choose_succ_succ' k 1,
        Nat.choose_one_right]
      omega
    have hnz : n ^ k * z ^ k = z ^ k * n ^ k := ((hzn.pow_left k).pow_right k).eq.symm
    rw [pow_succ (n * w) k, ih, hC]
    calc z ^ k.choose 2 * n ^ k * w ^ k * (n * w)
        = z ^ k.choose 2 * n ^ k * (w ^ k * n) * w := by simp only [mul_assoc]
      _ = z ^ k.choose 2 * n ^ k * (z ^ k * n * w ^ k) * w := by rw [hw k]
      _ = z ^ k.choose 2 * (n ^ k * z ^ k) * n * (w ^ k * w) := by simp only [mul_assoc]
      _ = z ^ k.choose 2 * (z ^ k * n ^ k) * n * (w ^ k * w) := by rw [hnz]
      _ = z ^ (k.choose 2 + k) * n ^ (k + 1) * w ^ (k + 1) := by
          rw [pow_add, pow_succ n k, pow_succ w k]; simp only [mul_assoc]

private theorem cyc_gen {X : Type*} [Group X] (C : Subgroup X) (hC : IsCyclic C)
    (hcard : Nat.card C = 25) :
    ∃ c : X, c ∈ C ∧ orderOf c = 25 ∧ ∀ x ∈ C, ∃ s : ℤ, x = c ^ s := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  refine ⟨(g : X), g.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  · intro x hx
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨s, ?_⟩
    have h := congrArg Subtype.val hs
    rw [Subgroup.coe_zpow] at h
    exact h.symm

private theorem conj_pow_five_comm {X : Type*} [Group X] (C : Subgroup X) (c : X)
    (hcC : c ∈ C) (hord : orderOf c = 25) (hgen : ∀ x ∈ C, ∃ s : ℤ, x = c ^ s)
    (y : X) (hy5 : y ^ 5 = 1) (hyC : ∀ x ∈ C, y * x * y⁻¹ ∈ C) :
    ∀ x ∈ C, (y * x * y⁻¹ * x⁻¹) ^ 5 = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, y * c * y⁻¹ = c ^ m := by
    obtain ⟨m, hm⟩ := hgen _ (hyC c hcC)
    exact ⟨m, hm⟩
  have hpow : ∀ k : ℕ, y ^ k * c * (y ^ k)⁻¹ = c ^ (m ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * c * (y ^ (k + 1))⁻¹
          = y * (y ^ k * c * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * c ^ (m ^ k) * y⁻¹ := by rw [ih]
        _ = (y * c * y⁻¹) ^ (m ^ k) := by rw [conj_zpow]
        _ = c ^ (m ^ (k + 1)) := by rw [hm, ← zpow_mul, pow_succ']
  have h5 : c ^ (m ^ 5) = c := by
    have h := hpow 5
    rw [hy5, one_mul, inv_one, mul_one] at h
    exact h.symm
  have h25 : (25 : ℤ) ∣ m ^ 5 - 1 := by
    have h1 : c ^ (m ^ 5 - 1) = 1 := by
      rw [zpow_sub, h5, zpow_one]
      simp
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at h2
    exact_mod_cast h2
  have h5m : (5 : ℤ) ∣ m - 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h3 : ((m ^ 5 - 1 : ℤ) : ZMod 5) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_trans (by norm_num) h25
    push_cast at h3
    have hm5 : (m : ZMod 5) ^ 5 = 1 := sub_eq_zero.mp h3
    rw [ZMod.pow_card] at hm5
    have h4 : ((m - 1 : ℤ) : ZMod 5) = 0 := by
      push_cast
      rw [hm5, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h4
    exact_mod_cast h4
  obtain ⟨u, hu⟩ := h5m
  intro x hx
  obtain ⟨s, rfl⟩ := hgen x hx
  have e1 : y * c ^ s * y⁻¹ = (y * c * y⁻¹) ^ s := conj_zpow.symm
  have e2 : y * c ^ s * y⁻¹ * (c ^ s)⁻¹ = c ^ (5 * u * s) := by
    rw [e1, hm, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    have hm' : m = 5 * u + 1 := by omega
    rw [hm']
    ring
  rw [e2, ← zpow_natCast, ← zpow_mul]
  apply orderOf_dvd_iff_zpow_eq_one.mp
  rw [hord]
  exact ⟨u * s, by push_cast; ring⟩

private theorem gen_five_torsion {X : Type*} [Group X] (C : Subgroup X) (c : X)
    (hord : orderOf c = 25) (hgen : ∀ x ∈ C, ∃ s : ℤ, x = c ^ s) (x : X) (hx : x ∈ C)
    (hx5 : x ^ 5 = 1) : ∃ i : ℤ, 0 ≤ i ∧ i < 5 ∧ x = c ^ (5 * i) := by
  obtain ⟨s, rfl⟩ := hgen x hx
  rw [← zpow_natCast, ← zpow_mul] at hx5
  have hdvd : (orderOf c : ℤ) ∣ s * ((5 : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr hx5
  rw [hord] at hdvd
  push_cast at hdvd
  have h5s : (5 : ℤ) ∣ s := by omega
  refine ⟨(s / 5) % 5, by omega, by omega, ?_⟩
  have e1 : s = 5 * (s / 5) := by omega
  have e2 : 5 * ((s / 5) % 5) = (5 * (s / 5)) % (orderOf c : ℤ) := by
    rw [hord]; push_cast; omega
  rw [e2, zpow_mod_orderOf, ← e1]

private theorem mem_sup_pairs {X : Type*} [Group X] (A B : Subgroup X)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by simp only [mul_assoc]
          _ = a1 * (a2 * b1) * b2 := by rw [hcomm a2 ha2 b1 hb1]
          _ = a1 * a2 * (b1 * b2) := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (show Commute a b from hcomm a ha b hb)).eq.symm }
  have memP : ∀ x, x ∈ P ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := fun x => Iff.rfl
  have hle : A ⊔ B ≤ P :=
    sup_le (fun a ha => (memP a).mpr ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => (memP b).mpr ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  intro x hx
  exact (memP x).mp (hle hx)

theorem fiveShape_exists_elem {X : Type*} [Group X] (Q A B : Subgroup X) (y : X)
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (hAc : IsCyclic A) (hBc : IsCyclic B)
    (hA : Nat.card A = 5 ^ 2) (hB : Nat.card B = 5 ^ 2) (hAB : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hyQ : y ∈ Q) (hy : orderOf y = 5)
    (hyAB : y ∉ A ⊔ B) (hgen : (A ⊔ B) ⊔ Subgroup.zpowers y = Q)
    (hyA : y ∈ Subgroup.normalizer (A : Set X)) (hyB : y ∈ Subgroup.normalizer (B : Set X))
    (hZ : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) ↔ (z ∈ A ⊔ B ∧ z ^ 5 = 1)) :
    ∃ E : Subgroup X, E ≤ Q ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ Nat.card E ≤ 5 ^ 3 ∧
      (∀ g ∈ Q, g ^ 5 = 1 → g ∈ E) ∧ ¬ (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) := by
  classical
  have hA25 : Nat.card A = 25 := by rw [hA]; norm_num
  have hB25 : Nat.card B = 25 := by rw [hB]; norm_num
  have hABQ : A ⊔ B ≤ Q := sup_le hAQ hBQ
  have hy5 : y ^ 5 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  obtain ⟨a, haA, hord_a, hgen_a⟩ := cyc_gen A hAc hA25
  obtain ⟨b, hbB, hord_b, hgen_b⟩ := cyc_gen B hBc hB25
  have hyA' : ∀ x ∈ A, y * x * y⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_set_normalizer_iff.mp hyA x).mp hx
  have hyB' : ∀ x ∈ B, y * x * y⁻¹ ∈ B := fun x hx =>
    (Subgroup.mem_set_normalizer_iff.mp hyB x).mp hx
  have hcycA := conj_pow_five_comm A a haA hord_a hgen_a y hy5 hyA'
  have hcycB := conj_pow_five_comm B b hbB hord_b hgen_b y hy5 hyB'
  have hdec := mem_sup_pairs A B hcomm
  have hcenter : ∀ z ∈ A ⊔ B, z ^ 5 = 1 → ∀ q ∈ Q, q * z = z * q := fun z hz hz5 =>
    (hZ z (hABQ hz)).mpr ⟨hz, hz5⟩
  have hcomm_d : ∀ n ∈ A ⊔ B, ∃ u ∈ A, ∃ v ∈ B,
      y * n * y⁻¹ * n⁻¹ = u * v ∧ u ^ 5 = 1 ∧ v ^ 5 = 1 := by
    intro n hn
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec n hn
    have hv : y * b' * y⁻¹ * b'⁻¹ ∈ B := B.mul_mem (hyB' b' hb') (B.inv_mem hb')
    have hc : a'⁻¹ * (y * b' * y⁻¹ * b'⁻¹) = (y * b' * y⁻¹ * b'⁻¹) * a'⁻¹ :=
      hcomm a'⁻¹ (A.inv_mem ha') _ hv
    refine ⟨y * a' * y⁻¹ * a'⁻¹, A.mul_mem (hyA' a' ha') (A.inv_mem ha'),
      y * b' * y⁻¹ * b'⁻¹, hv, ?_, hcycA a' ha', hcycB b' hb'⟩
    calc y * (a' * b') * y⁻¹ * (a' * b')⁻¹
        = (y * a' * y⁻¹) * ((y * b' * y⁻¹ * b'⁻¹) * a'⁻¹) := by group
      _ = (y * a' * y⁻¹) * (a'⁻¹ * (y * b' * y⁻¹ * b'⁻¹)) := by rw [hc]
      _ = (y * a' * y⁻¹ * a'⁻¹) * (y * b' * y⁻¹ * b'⁻¹) := by group
  have hyN : y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
    refine Subgroup.mem_set_normalizer_iff.mpr (fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
    · obtain ⟨a', ha', b', hb', rfl⟩ := hdec n hn
      have e : y * (a' * b') * y⁻¹ = (y * a' * y⁻¹) * (y * b' * y⁻¹) := by group
      rw [e]
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (hyA' a' ha'))
        (Subgroup.mem_sup_right (hyB' b' hb'))
    · obtain ⟨a', ha', b', hb', hab⟩ := hdec (y * n * y⁻¹) hn
      have ha'' : y⁻¹ * a' * y ∈ A := by
        refine (Subgroup.mem_set_normalizer_iff.mp hyA (y⁻¹ * a' * y)).mpr ?_
        rw [show y * (y⁻¹ * a' * y) * y⁻¹ = a' by group]
        exact ha'
      have hb'' : y⁻¹ * b' * y ∈ B := by
        refine (Subgroup.mem_set_normalizer_iff.mp hyB (y⁻¹ * b' * y)).mpr ?_
        rw [show y * (y⁻¹ * b' * y) * y⁻¹ = b' by group]
        exact hb'
      have e : n = (y⁻¹ * a' * y) * (y⁻¹ * b' * y) := by
        calc n = y⁻¹ * (y * n * y⁻¹) * y := by group
          _ = y⁻¹ * (a' * b') * y := by rw [hab]
          _ = (y⁻¹ * a' * y) * (y⁻¹ * b' * y) := by group
      rw [e]
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha'') (Subgroup.mem_sup_right hb'')
  have hconj : ∀ j : ℤ, ∀ n ∈ A ⊔ B, y ^ j * n * (y ^ j)⁻¹ ∈ A ⊔ B := fun j n hn =>
    (Subgroup.mem_set_normalizer_iff.mp
      ((Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X)).zpow_mem hyN j) n).mp hn
  let S : Subgroup X :=
    { carrier := {g | ∃ n ∈ A ⊔ B, ∃ j : ℤ, g = n * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨n1, hn1, j1, rfl⟩ ⟨n2, hn2, j2, rfl⟩
        refine ⟨n1 * (y ^ j1 * n2 * (y ^ j1)⁻¹), (A ⊔ B).mul_mem hn1 (hconj j1 n2 hn2),
          j1 + j2, ?_⟩
        rw [zpow_add]
        group
      one_mem' := ⟨1, (A ⊔ B).one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, j, rfl⟩
        refine ⟨y ^ (-j) * n⁻¹ * (y ^ (-j))⁻¹, hconj (-j) n⁻¹ ((A ⊔ B).inv_mem hn), -j, ?_⟩
        group }
  have memS : ∀ g, g ∈ S ↔ ∃ n ∈ A ⊔ B, ∃ j : ℤ, g = n * y ^ j := fun g => Iff.rfl
  have hQS : ∀ g ∈ Q, ∃ n ∈ A ⊔ B, ∃ j : ℤ, g = n * y ^ j := by
    have hle : (A ⊔ B) ⊔ Subgroup.zpowers y ≤ S := by
      refine sup_le (fun n hn => (memS n).mpr ⟨n, hn, 0, by simp⟩) ?_
      rw [Subgroup.zpowers_le]
      exact (memS y).mpr ⟨1, (A ⊔ B).one_mem, 1, by simp⟩
    intro g hg
    rw [← hgen] at hg
    exact (memS g).mp (hle hg)
  have hnat : ∀ j : ℤ, ∃ l : ℕ, y ^ j = y ^ l := by
    intro j
    refine ⟨(j % 5).toNat, ?_⟩
    have h1 : y ^ j = y ^ (j % 5) := by
      have h := zpow_mod_orderOf y j
      rw [hy] at h
      push_cast at h
      exact h.symm
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  let E : Subgroup X :=
    { carrier := {g | ∃ z ∈ A ⊔ B, z ^ 5 = 1 ∧ ∃ j : ℤ, g = z * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨z1, hz1, hz15, j1, rfl⟩ ⟨z2, hz2, hz25, j2, rfl⟩
        have c12 : Commute z1 z2 := (hcenter z1 hz1 hz15 z2 (hABQ hz2)).symm
        have hyz2 : y ^ j1 * z2 = z2 * y ^ j1 :=
          hcenter z2 hz2 hz25 (y ^ j1) (Q.zpow_mem hyQ j1)
        refine ⟨z1 * z2, (A ⊔ B).mul_mem hz1 hz2, ?_, j1 + j2, ?_⟩
        · rw [c12.mul_pow, hz15, hz25, one_mul]
        · calc z1 * y ^ j1 * (z2 * y ^ j2) = z1 * (y ^ j1 * z2) * y ^ j2 := by
                simp only [mul_assoc]
            _ = z1 * (z2 * y ^ j1) * y ^ j2 := by rw [hyz2]
            _ = z1 * z2 * (y ^ j1 * y ^ j2) := by simp only [mul_assoc]
            _ = z1 * z2 * y ^ (j1 + j2) := by rw [zpow_add]
      one_mem' := ⟨1, (A ⊔ B).one_mem, by simp, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨z, hz, hz5, j, rfl⟩
        have hz5' : (z⁻¹) ^ 5 = 1 := by rw [inv_pow, hz5, inv_one]
        refine ⟨z⁻¹, (A ⊔ B).inv_mem hz, hz5', -j, ?_⟩
        rw [mul_inv_rev, ← zpow_neg]
        exact hcenter z⁻¹ ((A ⊔ B).inv_mem hz) hz5' (y ^ (-j)) (Q.zpow_mem hyQ (-j)) }
  have memE : ∀ g, g ∈ E ↔ ∃ z ∈ A ⊔ B, z ^ 5 = 1 ∧ ∃ j : ℤ, g = z * y ^ j := fun g => Iff.rfl
  have hEQ : E ≤ Q := by
    intro g hg
    obtain ⟨z, hz, _, j, rfl⟩ := (memE g).mp hg
    exact Q.mul_mem (hABQ hz) (Q.zpow_mem hyQ j)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro g1 hg1 g2 hg2
    obtain ⟨z1, hz1, hz15, j1, rfl⟩ := (memE g1).mp hg1
    obtain ⟨z2, hz2, hz25, j2, rfl⟩ := (memE g2).mp hg2
    have c1 : Commute z1 z2 := (hcenter z1 hz1 hz15 z2 (hABQ hz2)).symm
    have c2 : Commute z1 (y ^ j2) := (hcenter z1 hz1 hz15 (y ^ j2) (Q.zpow_mem hyQ j2)).symm
    have c3 : Commute (y ^ j1) z2 := hcenter z2 hz2 hz25 (y ^ j1) (Q.zpow_mem hyQ j1)
    have c4 : Commute (y ^ j1) (y ^ j2) := by
      show y ^ j1 * y ^ j2 = y ^ j2 * y ^ j1
      rw [← zpow_add, ← zpow_add, add_comm]
    exact (Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)).eq
  let T : Finset X := (Finset.Ico (0 : ℤ) 5 ×ˢ Finset.Ico (0 : ℤ) 5 ×ˢ Finset.Ico (0 : ℤ) 5).image
    (fun p => a ^ (5 * p.1) * b ^ (5 * p.2.1) * y ^ p.2.2)
  have hsub : (E : Set X) ⊆ (T : Set X) := by
    intro g hg
    obtain ⟨z, hz, hz5, j, rfl⟩ := (memE g).mp hg
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec z hz
    have hcab : Commute a' b' := hcomm a' ha' b' hb'
    have hpow5 : a' ^ 5 * b' ^ 5 = 1 := by
      rw [← hcab.mul_pow]; exact hz5
    have ha5 : a' ^ 5 = 1 := by
      have hmem : a' ^ 5 ∈ A ⊓ B := by
        refine Subgroup.mem_inf.mpr ⟨A.pow_mem ha' 5, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hpow5]
        exact B.inv_mem (B.pow_mem hb' 5)
      rw [hAB] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb5 : b' ^ 5 = 1 := by
      rw [ha5, one_mul] at hpow5
      exact hpow5
    obtain ⟨i, hi0, hi5, rfl⟩ := gen_five_torsion A a hord_a hgen_a a' ha' ha5
    obtain ⟨k, hk0, hk5, rfl⟩ := gen_five_torsion B b hord_b hgen_b b' hb' hb5
    have hj : y ^ j = y ^ (j % 5) := by
      have h := zpow_mod_orderOf y j
      rw [hy] at h
      push_cast at h
      exact h.symm
    have hmem : a ^ (5 * i) * b ^ (5 * k) * y ^ (j % 5) ∈ T := by
      refine Finset.mem_image.mpr ⟨(i, k, j % 5), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨hi0, hi5⟩, ⟨hk0, hk5⟩, by omega, by omega⟩
    rw [hj]
    exact Finset.mem_coe.mpr hmem
  have hcardE : Nat.card E ≤ 5 ^ 3 := by
    have h1 : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq (E : Set X)
    rw [h1]
    calc (E : Set X).ncard ≤ (T : Set X).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet T)
      _ = T.card := Set.ncard_coe_finset T
      _ ≤ (Finset.Ico (0 : ℤ) 5 ×ˢ Finset.Ico (0 : ℤ) 5 ×ˢ Finset.Ico (0 : ℤ) 5).card :=
          Finset.card_image_le
      _ = 5 ^ 3 := by simp [Finset.card_product, Int.card_Ico]
  have hpow_formula : ∀ n ∈ A ⊔ B, ∀ l : ℕ, (n * y ^ l) ^ 5 = n ^ 5 := by
    intro n hn l
    obtain ⟨u, hu, v, hv, hdn, hu5, hv5⟩ := hcomm_d n hn
    obtain ⟨d, hd⟩ : ∃ d : X, d = y * n * y⁻¹ * n⁻¹ := ⟨_, rfl⟩
    rw [← hd] at hdn
    have hdAB : d ∈ A ⊔ B := by
      rw [hdn]
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv)
    have hd5 : d ^ 5 = 1 := by
      rw [hdn, (show Commute u v from hcomm u hu v hv).mul_pow, hu5, hv5, one_mul]
    have hdQ : d ∈ Q := by
      rw [hd]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem hyQ (hABQ hn)) (Q.inv_mem hyQ))
        (Q.inv_mem (hABQ hn))
    have hdc : ∀ q ∈ Q, q * d = d * q := (hZ d hdQ).mpr ⟨hdAB, hd5⟩
    have hyd : Commute y d := hdc y hyQ
    have hnd : Commute d n := (hdc n (hABQ hn)).symm
    have e : y * n = d * n * y := by rw [hd]; group
    have hyn : ∀ m : ℕ, y ^ m * n = d ^ m * n * y ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc y ^ (m + 1) * n = y * (y ^ m * n) := by rw [pow_succ', mul_assoc]
          _ = y * (d ^ m * n * y ^ m) := by rw [ih]
          _ = (y * d ^ m) * n * y ^ m := by simp only [mul_assoc]
          _ = (d ^ m * y) * n * y ^ m := by rw [(hyd.pow_right m).eq]
          _ = d ^ m * (y * n) * y ^ m := by simp only [mul_assoc]
          _ = d ^ m * (d * n * y) * y ^ m := by rw [e]
          _ = (d ^ m * d) * n * (y * y ^ m) := by simp only [mul_assoc]
          _ = d ^ (m + 1) * n * y ^ (m + 1) := by rw [← pow_succ, ← pow_succ']
    have hzn : Commute (d ^ l) n := hnd.pow_left l
    have hzw : Commute (d ^ l) (y ^ l) := (hyd.symm).pow_pow l l
    have hform := pow_mul_formula_aux n (y ^ l) (d ^ l) hzn hzw (hyn l) 5
    have h10 : Nat.choose 5 2 = 10 := by decide
    have hdl : (d ^ l) ^ 10 = 1 := by
      rw [← pow_mul, show l * 10 = 5 * (2 * l) by ring, pow_mul, hd5, one_pow]
    have hyl : (y ^ l) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hy5, one_pow]
    rw [h10, hdl, hyl, one_mul, mul_one] at hform
    exact hform
  have hEall : ∀ g ∈ Q, g ^ 5 = 1 → g ∈ E := by
    intro g hg hg5
    obtain ⟨n, hn, j, rfl⟩ := hQS g hg
    obtain ⟨l, hl⟩ := hnat j
    rw [hl] at hg5
    have hn5 : n ^ 5 = 1 := by
      rw [← hpow_formula n hn l]
      exact hg5
    exact (memE _).mpr ⟨n, hn, hn5, j, rfl⟩
  refine ⟨E, hEQ, hEcomm, hcardE, hEall, ?_⟩
  intro hcommQ
  exact hyAB ((hZ y hyQ).mp (fun q hq => hcommQ q hq y hyQ)).1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
