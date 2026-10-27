module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

namespace OddCentralCover

variable {A P : Type*} [Group A] [Group P] {ρ : A →* P}

theorem exists_lift_pow_two_pow (h : OddCentralCover ρ) {a : A} {k : ℕ}
    (hk : (ρ a) ^ (2 ^ k) = 1) : ∃ m : ℕ, ρ (a ^ m) = ρ a ∧ (a ^ m) ^ (2 ^ k) = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr h.odd_card_ker)
  obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨m, ?_, ?_⟩
  · rw [map_pow]
    have hord : orderOf (ρ a) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    calc (ρ a) ^ m = (ρ a) ^ 1 := pow_eq_pow_iff_modEq.mpr (hm1.of_dvd hord)
      _ = ρ a := pow_one _
  · have hker : a ^ (2 ^ k) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk
    have hN : (a ^ (2 ^ k)) ^ Nat.card ρ.ker = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hker)
    obtain ⟨t, ht⟩ := Nat.modEq_zero_iff_dvd.mp hm2
    calc (a ^ m) ^ (2 ^ k) = (a ^ (2 ^ k)) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((a ^ (2 ^ k)) ^ Nat.card ρ.ker) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [hN, one_pow]

end OddCentralCover

theorem mem_pCore_two_of_nilpotent_normal {A : Type} [Group A] [Finite A] (N : Subgroup A)
    [hN : N.Normal] (hnil : Group.IsNilpotent ↥N) {x : A} (hx : x ∈ N) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1) : x ∈ CFSG.pCore 2 A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x' : ↥N := ⟨x, hx⟩
  have hord : orderOf x' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hxk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hzp : IsPGroup 2 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  have hxS : x' ∈ (S : Subgroup ↥N) := hS (Subgroup.mem_zpowers x')
  exact Sylow.map_le_pCore hN hnil 2 S ⟨x', hxS, rfl⟩

namespace OddCentralCover

variable {A P : Type} [Group A] [Group P] {ρ : A →* P}

theorem subgroupComap (h : OddCentralCover ρ) (X : Subgroup P) :
    OddCentralCover (ρ.subgroupComap X) := by
  refine ⟨MonoidHom.subgroupComap_surjective ρ X h.surjective, h.subgroupComap_ker_le_center X, ?_⟩
  have hle : ((ρ.subgroupComap X).ker).map (X.comap ρ).subtype ≤ ρ.ker := by
    rintro _ ⟨p, hp, rfl⟩
    exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hp))
  have hcard : Nat.card (ρ.subgroupComap X).ker =
      Nat.card (((ρ.subgroupComap X).ker).map (X.comap ρ).subtype) :=
    Nat.card_congr (((ρ.subgroupComap X).ker).equivMapOfInjective _
      (X.comap ρ).subtype_injective).toEquiv
  rw [hcard]
  exact h.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem isSL23Mod_comap [Finite A] [Finite P] (h : OddCentralCover ρ) {K : Subgroup P}
    (hK : Nonempty (↥K ≃* SL2F3)) : IsSL23Mod ↥(K.comap ρ) := by
  obtain ⟨f⟩ := hK
  have hc := h.subgroupComap K
  have hbot : oddCore ↥K = ⊥ :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      f.symm oddCore_sl2f3
  have hker : oddCore ↥(K.comap ρ) = (ρ.subgroupComap K).ker := hc.oddCore_eq_ker hbot
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hc.surjective)).trans f⟩

end OddCentralCover

theorem commutatorElement_mul_central {A : Type*} [Group A] (a b n : A) (hn : n ∈ center A) :
    ⁅a * n, b⁆ = ⁅a, b⁆ := by
  have h1 : n * b * n⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hn b).symm
  calc ⁅a * n, b⁆ = a * (n * b * n⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h1]
    _ = ⁅a, b⁆ := (commutatorElement_def a b).symm

theorem commutatorElement_mul_central_right {A : Type*} [Group A] (a b n : A)
    (hn : n ∈ center A) : ⁅a, b * n⁆ = ⁅a, b⁆ := by
  have h1 : n * a⁻¹ = a⁻¹ * n := (Subgroup.mem_center_iff.mp hn a⁻¹).symm
  calc ⁅a, b * n⁆ = a * b * (n * a⁻¹) * n⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * (a⁻¹ * n) * n⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group
    _ = ⁅a, b⁆ := (commutatorElement_def a b).symm

theorem eq_top_of_map_eq_top {A P : Type*} [Group A] [Group P] (ρ : A →* P)
    (hker : ρ.ker ≤ center A) (hperf : commutator A = ⊤) {M : Subgroup A}
    (hM : ⊤ ≤ M.map ρ) : M = ⊤ := by
  have hlift : ∀ g : A, ∃ m ∈ M, ∃ n ∈ center A, g = m * n := by
    intro g
    obtain ⟨m, hm, hmg⟩ := hM (Subgroup.mem_top (ρ g))
    refine ⟨m, hm, m⁻¹ * g, hker (MonoidHom.mem_ker.mpr ?_), by group⟩
    rw [map_mul, map_inv, hmg, inv_mul_cancel]
  have hcomm : commutator A ≤ M := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨m₁, hm₁, n₁, hn₁, rfl⟩ := hlift g₁
    obtain ⟨m₂, hm₂, n₂, hn₂, rfl⟩ := hlift g₂
    rw [commutatorElement_mul_central _ _ _ hn₁, commutatorElement_mul_central_right _ _ _ hn₂,
      commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)
  rw [hperf] at hcomm
  exact eq_top_iff.mpr hcomm

end CFSG.OddStandard.SmallF3.Omega
