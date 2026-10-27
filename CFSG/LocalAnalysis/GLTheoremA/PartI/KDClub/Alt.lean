module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Reduce
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

private theorem natCard_centralizer_dvd_72 {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (a : Equiv.Perm (Fin n)) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    Nat.card (Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n)))) ∣ 72 := by
  have h3 : ∀ m ∈ a.cycleType, m = 3 := by
    intro m hm
    have h1 : m ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one ha3)
    have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
    exact ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left (by omega)
  obtain ⟨k, hk⟩ : ∃ k, a.cycleType = Multiset.replicate k 3 :=
    ⟨_, Multiset.eq_replicate_card.2 h3⟩
  have hk0 : k ≠ 0 := by
    intro h0
    apply ha1
    rw [← Equiv.Perm.cycleType_eq_zero, hk, h0, Multiset.replicate_zero]
  have hsum : k * 3 ≤ n := by
    have h := Equiv.Perm.sum_cycleType_le a
    rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    exact h
  have hcard : Nat.card (Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n)))) =
      Nat.factorial (n - k * 3) * 3 ^ k * Nat.factorial k := by
    rw [Equiv.Perm.nat_card_centralizer, hk, Multiset.sum_replicate, Multiset.prod_replicate,
      Multiset.toFinset_replicate, if_neg hk0, Finset.prod_singleton,
      Multiset.count_replicate_self, Fintype.card_fin, smul_eq_mul]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hk2 : k ≤ 2 := by omega
  rw [hcard]
  rcases hn with rfl | rfl | rfl <;> interval_cases k <;> first | omega | norm_num [Nat.factorial]

private theorem isSolvable_centralizer_alt {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (a : alternatingGroup (Fin n)) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) := by
  classical
  have hf : Function.Injective ((alternatingGroup (Fin n)).subtype :
      alternatingGroup (Fin n) →* Equiv.Perm (Fin n)) := Subtype.val_injective
  have hle : (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))).map
      (alternatingGroup (Fin n)).subtype ≤
        Subgroup.centralizer ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun y : alternatingGroup (Fin n) => (y : Equiv.Perm (Fin n))) hx
    simpa using h
  have ha1' : (a : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    apply ha1
    exact Subtype.val_injective (by simpa using h)
  have ha3' : (a : Equiv.Perm (Fin n)) ^ 3 = 1 := by
    have h := congrArg (fun y : alternatingGroup (Fin n) => (y : Equiv.Perm (Fin n))) ha3
    simpa using h
  have hdvd : Nat.card ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) ∣ 72 := by
    rw [← Subgroup.card_map_of_injective hf]
    exact (Subgroup.card_dvd_of_le hle).trans (natCard_centralizer_dvd_72 hn _ ha1' ha3')
  have h72 : (2 : ℕ) ^ 3 * 3 ^ 2 = 72 := by norm_num
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 (h72 ▸ hdvd)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
  have hcard : Fintype.card ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n)))) =
      2 ^ i * 3 ^ j := by
    rw [← Nat.card_eq_fintype_card, hyz]
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hcard

theorem kdClubAt_alternating (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) :
    KDClubAt (alternatingGroup (Fin n)) := by
  apply kdClubAt_of_solvable
  intro α hα1 hα3
  have hn5 : 5 ≤ n := by omega
  have hOut := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn5
  have hne : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) ≠ 0 := fun h => by
    rw [h] at hOut
    norm_num at hOut
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) := Nat.finite_of_card_ne_zero hne
  have hq3 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n))) α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hord3 := orderOf_dvd_of_pow_eq_one hq3
  have hord4 := (orderOf_dvd_natCard (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n))) α)).trans hOut
  have hord1 : orderOf (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n))) α) = 1 := by
    have h := Nat.dvd_gcd hord3 hord4
    exact Nat.dvd_one.1 (by simpa using h)
  have hq1 := orderOf_eq_one_iff.1 hord1
  have hαin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin n)) := by
    rw [QuotientGroup.mk'_apply] at hq1
    exact (QuotientGroup.eq_one_iff α).1 hq1
  obtain ⟨a, rfl⟩ : ∃ a : alternatingGroup (Fin n), MulAut.conj a = α := hαin
  have ha1 : a ≠ 1 := by
    intro h
    apply hα1
    rw [h, map_one]
  have hc : MulAut.conj (a ^ 3) = 1 := by
    rw [map_pow]
    exact hα3
  have hcen : a ^ 3 ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun hc g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rw [hZ, Subgroup.mem_bot] at hcen
  have hfix : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (MulAut.conj a) =
      Subgroup.centralizer ({a} : Set (alternatingGroup (Fin n))) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.mem_fixSub, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  rw [hfix]
  exact isSolvable_centralizer_alt hn a ha1 hcen

end CFSG.LocalAnalysis.GLTheoremA
