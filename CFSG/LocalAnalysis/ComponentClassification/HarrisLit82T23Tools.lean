module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T23

open CFSG Subgroup Assembly.LowTwoRank

variable {H : Type} [Group H]

theorem mem_sup_of_commute {S T : Subgroup H} (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : H}
    (hx : x ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ s ∈ S, ∃ t ∈ T, s * t = x) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  · exact ⟨1, S.one_mem, 1, T.one_mem, one_mul 1⟩
  · rintro x y - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    refine ⟨s * s', S.mul_mem hs hs', t * t', T.mul_mem ht ht', ?_⟩
    calc s * s' * (t * t') = s * (s' * t) * t' := by group
      _ = s * (t * s') * t' := by rw [hc s' hs' t ht]
      _ = s * t * (s' * t') := by group
  · rintro x - ⟨s, hs, t, ht, rfl⟩
    refine ⟨s⁻¹, S.inv_mem hs, t⁻¹, T.inv_mem ht, ?_⟩
    calc s⁻¹ * t⁻¹ = (t * s)⁻¹ := by group
      _ = (s * t)⁻¹ := by rw [hc s hs t ht]

theorem mem_of_mem_sup_of_pow_two_pow [Finite H] {A N : Subgroup H} [N.Normal]
    (hNA : N ≤ normalizer (A : Set H)) (hodd : Odd (Nat.card ↥N)) {x : H} (hx : x ∈ A ⊔ N)
    {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x ∈ A := by
  set S := A ⊔ N with hS
  have hSA : S ≤ normalizer (A : Set H) := sup_le le_normalizer hNA
  have : (A.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSA
  set π := QuotientGroup.mk' (A.subgroupOf S)
  let ι : ↥N →* ↥S := Subgroup.inclusion le_sup_right
  have hsurj : Function.Surjective (π.comp ι) := by
    intro q
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨a, ha, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hs
    refine ⟨⟨m, hm⟩, ?_⟩
    have ha' : (⟨a, mem_sup_left ha⟩ : ↥S) ∈ A.subgroupOf S := ha
    have h1 : π ⟨a, mem_sup_left ha⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha'
    have hmul : (⟨a * m, hs⟩ : ↥S) = ⟨a, mem_sup_left ha⟩ * ⟨m, mem_sup_right hm⟩ := rfl
    change π ⟨m, mem_sup_right hm⟩ = π ⟨a * m, hs⟩
    rw [hmul, map_mul, h1, one_mul]
  have hQodd : Odd (Nat.card (↥S ⧸ A.subgroupOf S)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)
  have h1 : orderOf (π ⟨x, hx⟩) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥S) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this, map_one]
  have h2 : orderOf (π ⟨x, hx⟩) ∣ Nat.card (↥S ⧸ A.subgroupOf S) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (↥S ⧸ A.subgroupOf S)) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hQodd)
  have h3 : orderOf (π ⟨x, hx⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_involution_lift [Finite H] {a : H ⧸ pPrimeCore 2 H} (ha : a * a = 1)
    (ha1 : a ≠ 1) : ∃ k : H, k * k = 1 ∧ k ≠ 1 ∧ (QuotientGroup.mk k : H ⧸ pPrimeCore 2 H) = a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hx2 : x ^ 2 ∈ pPrimeCore 2 H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, sq]
    exact ha
  set m := orderOf (x ^ 2) with hm
  have hmodd : Odd m := by
    have hdvd : orderOf (⟨x ^ 2, hx2⟩ : ↥(pPrimeCore 2 H)) ∣ Nat.card ↥(pPrimeCore 2 H) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have hodd : Odd (Nat.card ↥(pPrimeCore 2 H)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hodd.of_dvd_nat hdvd
  obtain ⟨j, hj⟩ := hmodd
  have hk2 : x ^ m * x ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hm, pow_orderOf_eq_one]
  have hkmk : (QuotientGroup.mk (x ^ m) : H ⧸ pPrimeCore 2 H) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_pow, hj, pow_succ, pow_mul, sq, ha, one_pow, one_mul]
  refine ⟨x ^ m, hk2, fun h1 => ha1 ?_, hkmk⟩
  rw [← hkmk, h1, QuotientGroup.mk_one]

theorem centralizer_inf_mul {w k : H} :
    centralizer ({w} : Set H) ⊓ centralizer {w * k} = centralizer {w} ⊓ centralizer {k} := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 : w * (x * k) = w * (k * x) := by
      rw [← mul_assoc, ← h1, mul_assoc, h2, mul_assoc]
    exact mul_left_cancel h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * (w * k) = (x * w) * k := (mul_assoc _ _ _).symm
      _ = (w * x) * k := by rw [h1]
      _ = w * (x * k) := mul_assoc _ _ _
      _ = w * (k * x) := by rw [h2]
      _ = w * k * x := (mul_assoc _ _ _).symm

theorem isMTypeSchur_of_slTwo [Finite H] (hGA : TBLit.GriessMultipliersAllModels)
    (hA : Group.IsPerfect H) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (h5 : 5 ≤ p ^ k) (hsl : IsSLTwoOver (p ^ k) (H ⧸ pPrimeCore 2 H)) : IsMTypeSchur p H := by
  obtain ⟨hq, hZ, hm, hO⟩ := Lemma47.sl2_facts hp hp2 hk h5 hsl
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  exact isMTypeSchur_of_surjective (TBLit.GriessMultipliersOdd.of_allModels hGA) hp hp2
    (QuotientGroup.mk' (pPrimeCore 2 H)) (QuotientGroup.mk'_surjective _) hker hA hq hO hZ hm

end CFSG.ComponentClassification.HarrisLit.T23
