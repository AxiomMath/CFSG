module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Lift

public section

namespace CFSG.EvenSporadicStandard.Induction.Cover

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {X : Type} [Group X]

abbrev bar (K : Subgroup X) : Subgroup (X ⧸ center X) := K.map (QuotientGroup.mk' (center X))

theorem mem_bar {K : Subgroup X} {y : X ⧸ center X} :
    y ∈ bar K ↔ ∃ k ∈ K, (k : X ⧸ center X) = y := by
  simp [bar, Subgroup.mem_map]

theorem mk_mem_bar_of_mem {K : Subgroup X} {k : X} (hk : k ∈ K) : (k : X ⧸ center X) ∈ bar K :=
  ⟨k, hk, rfl⟩

theorem mem_bar_iff_exists_mem_mul {K : Subgroup X} {x : X} :
    (x : X ⧸ center X) ∈ bar K ↔ ∃ k ∈ K, ∃ z ∈ center X, x = k * z := by
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k, hk, k⁻¹ * x, QuotientGroup.eq.1 hkx, by group⟩
  · rintro ⟨k, hk, z, hz, rfl⟩
    refine ⟨k, hk, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]

theorem mem_of_mk_mem [Finite X] (hodd : Odd (Nat.card (center X))) {K : Subgroup X} {u : X}
    (hu : u * u = 1) (h : (u : X ⧸ center X) ∈ bar K) : u ∈ K := by
  obtain ⟨k, hk, hku⟩ := mem_bar.1 h
  set m := Nat.card (center X) with hm
  obtain ⟨j, hj⟩ := hodd
  have hkk : k * k ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hku, ← QuotientGroup.mk_mul, hu]
    rfl
  have hz : (k * k) ^ m = 1 := by
    have := pow_card_eq_one' (G := ↥(center X)) (x := ⟨k * k, hkk⟩)
    exact congrArg Subtype.val this
  have hk2 : (k ^ m) * (k ^ m) = 1 := by
    rw [← (Commute.refl k).mul_pow m]
    exact hz
  have hu1 : (u : X ⧸ center X) * (u : X ⧸ center X) = 1 := by
    rw [← QuotientGroup.mk_mul, hu]
    rfl
  have hpow : (u : X ⧸ center X) ^ m = (u : X ⧸ center X) := by
    rw [hj, pow_succ, pow_mul, sq, hu1, one_pow, one_mul]
  have hmk : ((k ^ m : X) : X ⧸ center X) = (u : X ⧸ center X) := by
    rw [QuotientGroup.mk_pow, hku, hpow]
  have heq : k ^ m = u :=
    Closing.eq_of_mk_eq_of_sq (hodd := ⟨j, hj⟩) hk2 hu hmk
  rw [← heq]
  exact pow_mem hk m

theorem card_mul_bar (K : Subgroup X) :
    Nat.card ((center X).subgroupOf K) * Nat.card (bar K) = Nat.card K := by
  let f : K →* X ⧸ center X := (QuotientGroup.mk' (center X)).comp K.subtype
  have hker : f.ker = (center X).subgroupOf K := by
    ext k
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = bar K := by
    simp [f, MonoidHom.range_comp, Subgroup.range_subtype]
  have := Subgroup.card_ker_mul_card_range f
  rwa [hker, hrange] at this

theorem card_subgroupOf_center_dvd (K : Subgroup X) :
    Nat.card ((center X).subgroupOf K) ∣ Nat.card (center X) := by
  have h1 : ((center X).subgroupOf K).map K.subtype ≤ center X := by
    rintro _ ⟨k, hk, rfl⟩
    exact hk
  rw [← Subgroup.card_map_of_injective K.subtype_injective]
  exact Subgroup.card_dvd_of_le h1

theorem odd_card_subgroupOf_center (hodd : Odd (Nat.card (center X))) (K : Subgroup X) :
    Odd (Nat.card ((center X).subgroupOf K)) :=
  hodd.of_dvd_nat (card_subgroupOf_center_dvd K)

theorem twoAdic_bar [Finite X] (hodd : Odd (Nat.card (center X))) (K : Subgroup X) :
    twoAdic (bar K) = twoAdic K := by
  have h := card_mul_bar K
  have ho := odd_card_subgroupOf_center hodd K
  have h0 : Nat.card ((center X).subgroupOf K) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (bar K) ≠ 0 := Nat.card_pos.ne'
  have h2 : ¬ 2 ∣ Nat.card ((center X).subgroupOf K) := fun hd =>
    (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hd)
  unfold twoAdic
  rw [← h, Nat.factorization_mul h0 h1, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2, zero_add]

theorem commutatorElement_mul_central_left {a z b : X} (hz : z ∈ center X) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b * z⁻¹ = b := by
    rw [← Subgroup.mem_center_iff.1 hz b, mul_inv_cancel_right]
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h, commutatorElement_def]

theorem commutatorElement_mul_central_right {a z b : X} (hz : z ∈ center X) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.1 hz a⁻¹, mul_inv_cancel_right]
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h, commutatorElement_def]

theorem mem_sup_central {K Z' : Subgroup X} (hZ : Z' ≤ center X) {x : X} :
    x ∈ K ⊔ Z' ↔ ∃ k ∈ K, ∃ z ∈ Z', k * z = x := by
  have : Z'.Normal := Subgroup.normal_of_le_center hZ
  exact Subgroup.mem_sup_of_normal_right

theorem commutator_sup_central_le {K Z' : Subgroup X} (hZ : Z' ≤ center X) :
    ⁅K ⊔ Z', K ⊔ Z'⁆ ≤ ⁅K, K⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := (mem_sup_central hZ).1 hx
  obtain ⟨k', hk', z', hz', rfl⟩ := (mem_sup_central hZ).1 hy
  rw [commutatorElement_mul_central_left (hZ hz), commutatorElement_mul_central_right (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

theorem commutator_le_self (K : Subgroup X) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)

theorem le_of_perfect_le_sup_central {K Z' P : Subgroup X} (hZ : Z' ≤ center X)
    (hP : ⁅P, P⁆ = P) (hPK : P ≤ K ⊔ Z') : P ≤ K := by
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅K ⊔ Z', K ⊔ Z'⁆ := Subgroup.commutator_mono hPK hPK
    _ ≤ ⁅K, K⁆ := commutator_sup_central_le hZ
    _ ≤ K := commutator_le_self K

theorem le_of_isPGroup_le_sup_central [Finite X] {K Z' S : Subgroup X} (hZ : Z' ≤ center X)
    (hodd : Odd (Nat.card Z')) (hS : IsPGroup 2 S) (hSK : S ≤ K ⊔ Z') : S ≤ K := by
  intro x hxS
  obtain ⟨k, hk, z, hz, rfl⟩ := (mem_sup_central hZ).1 (hSK hxS)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hS ⟨k * z, hxS⟩
  have hx : (k * z) ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hcomm : Commute k z := (Subgroup.mem_center_iff.1 (hZ hz) k)
  have hz2 : z ^ (2 ^ a) ∈ K := by
    have h1 : k ^ (2 ^ a) * z ^ (2 ^ a) = 1 := by rw [← hcomm.mul_pow]; exact hx
    have : z ^ (2 ^ a) = (k ^ (2 ^ a))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact K.inv_mem (pow_mem hk _)
  have hord : orderOf z ∣ Nat.card Z' := by
    have := Subgroup.orderOf_dvd_natCard Z' hz
    exact this
  have hodd' : Odd (orderOf z) := hodd.of_dvd_nat hord
  have hcop : Nat.Coprime (orderOf z) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hodd')
  have hzmem : z ∈ Subgroup.zpowers (z ^ (2 ^ a)) := by
    have hle : Subgroup.zpowers (z ^ (2 ^ a)) ≤ Subgroup.zpowers z :=
      Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers z) _)
    have hcard : Nat.card (Subgroup.zpowers (z ^ (2 ^ a))) = Nat.card (Subgroup.zpowers z) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    rw [heq]
    exact Subgroup.mem_zpowers z
  have hzK : z ∈ K := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzmem
    rw [← hn]
    exact zpow_mem hz2 n
  exact K.mul_mem hk hzK

end CFSG.EvenSporadicStandard.Induction.Cover
