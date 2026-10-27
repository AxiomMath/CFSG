module

public import CFSG.ClassicalInvolution.Q3.Q3TJPSUCore
public import CFSG.ClassicalInvolution.Q3.Q3TJU
public import CFSG.ClassicalInvolution.Q3.Q3TJTri

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification

variable {X : Type} [Group X]

theorem exists_eq_conj_of_forall_pow_two_pow {G : Type*} [Group G] {k : ℕ}
    (h : ∀ a : OuterAutomorphisms.Outer G, a ^ (2 ^ k) = 1) (α : MulAut G)
    (hodd : Odd (orderOf α)) : ∃ g : G, α = MulAut.conj g := by
  set a : OuterAutomorphisms.Outer G := (α : MulAut G ⧸ OuterAutomorphisms.inner G) with ha
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (h a)
  have h2 : orderOf a ∣ orderOf α := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd' : Odd (orderOf a) := hodd.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).mp hj
  exact ⟨g, hg.symm⟩

theorem lineNormalizer_quotient_pow_sixteen {K : Type} [Field K] {r ε : ℕ}
    (h : UnitaryFieldData 3 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1) (hn3 : 3 ≤ 2 * r + ε)
    (q : lineNormalizer h r ε ⧸
      (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε)) : q ^ 16 = 1 := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    SubgroupClass.coe_pow]
  rw [lineNormalizer_eq_semilinearPointGroup h (by norm_num) hr hε hn3] at hy
  obtain ⟨x, rfl⟩ := hy
  exact semilinearPointAction_pow_sixteen_mem x

theorem outer_pow_sixteen_of_PSU {H : Type} [Group H] {n : ℕ}
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU n 3 1) :
    ∀ a : OuterAutomorphisms.Outer H, a ^ (2 ^ 4) = 1 := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hn3 : 3 ≤ 2 * r + ε := hH.1.2.2.1
  have hr : 1 ≤ r := by omega
  obtain ⟨⟨K, _, h, ⟨e⟩⟩, hall⟩ := unitary_classical_model_outer_normalizer hH
  obtain ⟨-, ⟨E⟩, -⟩ := hall K h e
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  obtain ⟨j, hj⟩ := exists_transportLines h hR
  obtain ⟨E₂⟩ := nonempty_normalizerQuotient_mulEquiv j (hypProjTransport h hR) hj
  have F := E.trans E₂.symm
  intro a
  have h1 := lineNormalizer_quotient_pow_sixteen h hr hε hn3 (F a)
  have h2 : orderOf (F a) ∣ 16 := orderOf_dvd_of_pow_eq_one h1
  rw [MulEquiv.orderOf_eq] at h2
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem exists_eq_conj_PSU {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n 3 1)
    (hZ : Subgroup.center X = ⊥) (f : (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  let S := LieType.Universal.Unitary.SU
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) n
  let f' : S →* X := f
  have hker' : f'.ker ≤ Subgroup.center S := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' (Subgroup.center S)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨hadm', K, i1, i2, hK, ⟨e'⟩⟩ :=
    LieType.Universal.Unitary.statedClassicalModel_center_quotient hadm hF
  have hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU n 3 1 :=
    ⟨hadm', K, i1, i2, hK, ⟨e.trans e'⟩⟩
  exact exists_eq_conj_of_forall_pow_two_pow (outer_pow_sixteen_of_PSU hT) α hodd

theorem steinbergOddAut3PSU_proved : SteinbergOddAut3PSU :=
  fun _ hadm _ _ _ _ hZ f hf hker α hodd => exists_eq_conj_PSU hadm hZ f hf hker α hodd

theorem modelOddAutRigid_of_D4 (hD4 : D4OddAutInner3) : ModelOddAutRigid :=
  modelOddAutRigid_of_PSU steinbergOddAut3PSU_proved hD4 trialityD4OddAutInner3_proved

end CFSG.ClassicalInvolution.Q3.Q3T
