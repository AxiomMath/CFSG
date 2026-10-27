module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_zpowers_of_pow_two {u : X} {k : ℕ} (hu : u ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers u) := by
  have hd : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

omit [Finite X] in
theorem isPGroup_zpowers_conj {u : X} (hu : IsPGroup 2 (zpowers u)) (g : X) :
    IsPGroup 2 (zpowers (g * u * g⁻¹)) := by
  have h := hu.map (MulAut.conj g).toMonoidHom
  rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem exists_conj_of_inv_mul_mem {N : Subgroup X} [hNn : N.Normal] (hN : Odd (Nat.card N))
    {u v : X} (hu : IsPGroup 2 (zpowers u)) (hv : IsPGroup 2 (zpowers v)) (h : u⁻¹ * v ∈ N) :
    ∃ m ∈ N, m * v * m⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : zpowers u ⊓ N = ⊥ := CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hu hN
  have hSyl : IsSylowOf 2 (zpowers u) (N ⊔ zpowers u) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hu, fun h2 => ?_⟩
    rw [relIndex_sup_eq_relIndex_of_normal] at h2
    have h3 : (zpowers u).relIndex N ∣ Nat.card N :=
      Subgroup.index_dvd_card ((zpowers u).subgroupOf N)
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h2.trans h3))
  have hvM : v ∈ N ⊔ zpowers u := by
    have e : v = u * (u⁻¹ * v) := by group
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers u)) (mem_sup_left h)
  obtain ⟨c, hcM, hc⟩ := CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf hSyl
    (zpowers_le.2 hvM) hv
  have hcM' : c ∈ ((N ⊔ zpowers u : Subgroup X) : Set X) := hcM
  rw [Subgroup.normal_mul] at hcM'
  obtain ⟨n, hn, y, hy, rfl⟩ := hcM'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  set m := (u ^ k)⁻¹ * n * u ^ k with hm
  have hmN : m ∈ N := by
    have := hNn.conj_mem n hn (u ^ k)⁻¹
    rwa [inv_inv] at this
  have hmv : m * v * m⁻¹ ∈ zpowers u := by
    have h1 := hc v (mem_zpowers v)
    have e : m * v * m⁻¹ = (u ^ k)⁻¹ * (n * u ^ k * v * (n * u ^ k)⁻¹) * u ^ k := by
      rw [hm]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (zpow_mem (mem_zpowers u) _)) h1) (zpow_mem (mem_zpowers u) _)
  have hNm : u⁻¹ * (m * v * m⁻¹) ∈ N := by
    have e : u⁻¹ * (m * v * m⁻¹) = (u⁻¹ * v) * (v⁻¹ * m * v) * m⁻¹ := by group
    rw [e]
    have h2 := hNn.conj_mem m hmN v⁻¹
    rw [inv_inv] at h2
    exact mul_mem (mul_mem h h2) (inv_mem hmN)
  have hz : u⁻¹ * (m * v * m⁻¹) ∈ zpowers u ⊓ N :=
    mem_inf.2 ⟨mul_mem (inv_mem (mem_zpowers u)) hmv, hNm⟩
  rw [hbot, mem_bot] at hz
  exact ⟨m, hmN, (inv_mul_eq_one.1 hz).symm⟩

theorem isConj_of_isConj_mk {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {u v : X}
    (hu : IsPGroup 2 (zpowers u)) (hv : IsPGroup 2 (zpowers v))
    (h : IsConj (u : X ⧸ N) (v : X ⧸ N)) : IsConj u v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hmem : v⁻¹ * (g * u * g⁻¹) ∈ N := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc.symm
  obtain ⟨m, -, hm⟩ := exists_conj_of_inv_mul_mem hN hv (isPGroup_zpowers_conj hu g) hmem
  exact isConj_iff.2 ⟨m * g, by rw [← hm]; group⟩

theorem orderOf_mk_eq {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {u : X}
    (hu : IsPGroup 2 (zpowers u)) : orderOf (u : X ⧸ N) = orderOf u := by
  have hker : Odd (Nat.card (QuotientGroup.mk' N).ker) := by rwa [QuotientGroup.ker_mk']
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd (QuotientGroup.mk' N) hker hu
  have h := orderOf_injective _ hinj ⟨u, mem_zpowers u⟩
  rw [Subgroup.orderOf_mk] at h
  exact h

theorem exists_lift_orderOf_two {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {a : X ⧸ N} (ha : orderOf a = 2) : ∃ u : X, orderOf u = 2 ∧ (u : X ⧸ N) = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hker : Odd (Nat.card (QuotientGroup.mk' N).ker) := by rwa [QuotientGroup.ker_mk']
  obtain ⟨A, -, hAE, hinj⟩ := CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker (zpowers a) hE
  have haA : a ∈ A.map (QuotientGroup.mk' N) := hAE ▸ mem_zpowers a
  obtain ⟨u, huA, hu⟩ := haA
  refine ⟨u, ?_, hu⟩
  have h := orderOf_injective _ hinj ⟨u, huA⟩
  rw [Subgroup.orderOf_mk] at h
  rw [← h, ← ha]
  exact congrArg orderOf hu

theorem isConj_mk_of_oneClass {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    (hone : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    ∀ a b : X ⧸ N, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  intro a b ha hb
  obtain ⟨u, hu, rfl⟩ := exists_lift_orderOf_two hN ha
  obtain ⟨v, hv, rfl⟩ := exists_lift_orderOf_two hN hb
  exact (QuotientGroup.mk' N).map_isConj (hone u v hu hv)

theorem exists_sylow_quot_equiv {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {S : Type*} [Group S] (T : Sylow 2 X) (e : Nonempty ((T : Subgroup X) ≃* S)) :
    ∃ T' : Sylow 2 (X ⧸ N), Nonempty ((T' : Subgroup (X ⧸ N)) ≃* S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := e
  have hker : Odd (Nat.card (QuotientGroup.mk' N).ker) := by rwa [QuotientGroup.ker_mk']
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd (QuotientGroup.mk' N) hker
    T.isPGroup'
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective N), ⟨?_⟩⟩
  have hr : ((QuotientGroup.mk' N).comp (T : Subgroup X).subtype).range =
      ((T.mapSurjective (QuotientGroup.mk'_surjective N) : Sylow 2 (X ⧸ N)) :
        Subgroup (X ⧸ N)) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MulEquiv.subgroupCongr hr).symm.trans ((MonoidHom.ofInjective hinj).symm.trans e)

theorem pPrimeCore_two_facts :
    pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ ∧ Odd (Nat.card (pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨pPrimeCore_quotient_eq_bot Nat.prime_two,
    Nat.coprime_two_left.mp pPrimeCore_coprime_card⟩

end CFSG.ComponentClassification.GrSLit.ONanBal
