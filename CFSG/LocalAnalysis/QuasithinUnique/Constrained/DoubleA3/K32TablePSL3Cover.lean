module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBound2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.projectiveSL)

theorem k32cov_center_eq_pCore {K N : Type} [Group K] [Group N] (hq : CFSG.IsQuasisimple K)
    (e : (K ⧸ CFSG.pCore 2 K) ≃* N) (hN : Subgroup.center N = ⊥) (hN1 : Nontrivial N) :
    Subgroup.center K = CFSG.pCore 2 K := by
  have hCO : Subgroup.center K ≤ CFSG.pCore 2 K := by
    intro c hc
    have hcen : ∀ y : K ⧸ CFSG.pCore 2 K,
        y * (c : K ⧸ CFSG.pCore 2 K) = (c : K ⧸ CFSG.pCore 2 K) * y := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H z =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subgroup.mem_center_iff.mp hc z)
    have h2 : e (c : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hcen y]
    rw [hN, Subgroup.mem_bot] at h2
    have h3 : (c : K ⧸ CFSG.pCore 2 K) = 1 := e.injective (by rw [h2, map_one])
    exact (QuotientGroup.eq_one_iff c).mp h3
  refine le_antisymm hCO ?_
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  have hnorm : ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hnorm
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)))) with h | h
  · intro x hx
    have : QuotientGroup.mk' (Subgroup.center K) x ∈
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have htop : CFSG.pCore 2 K = ⊤ := by
      rw [eq_top_iff]
      intro k _
      have : QuotientGroup.mk' (Subgroup.center K) k ∈
          (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hxk⟩ := this
      have hkx : x⁻¹ * k ∈ Subgroup.center K := by
        rw [← QuotientGroup.eq]
        exact hxk
      have : k = x * (x⁻¹ * k) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx (hCO hkx)
    obtain ⟨a, b, hab⟩ := exists_pair_ne N
    have h1 : e.symm a = e.symm b := by
      have h2 : ∀ y : K ⧸ CFSG.pCore 2 K, y = 1 := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H z => exact (QuotientGroup.eq_one_iff z).mpr (htop ▸ Subgroup.mem_top z)
      rw [h2 (e.symm a), h2 (e.symm b)]
    exact hab (e.symm.injective h1)

theorem k32cov_two_pow_factorization {N k i : ℕ} (h : N = 2 ^ k * i) (hi : Odd i) :
    2 ^ N.factorization 2 = 2 ^ k := by
  have hi0 : i ≠ 0 := hi.pos.ne'
  have hnd : ¬ 2 ∣ i := by
    have := Nat.odd_iff.mp hi
    omega
  rw [h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hi0]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_two]

theorem k32cov_card_projectiveSL_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (LinearFlag.projectiveSL 3 F) = 2 ^ 6 * 315 := by
  rw [Nat.card_congr (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  have hprod : ∏ j ∈ Finset.Icc 2 3, (4 ^ j - 1) = (4 ^ 2 - 1) * (4 ^ 3 - 1) := by
    have : Finset.Icc 2 3 = {2, 3} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
  rw [hprod]
  norm_num

theorem k32ExclPSL3Cover_of_bound
    (hB : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      K32ZBound2 (LinearFlag.projectiveSL 3 F) 1 4) : K32ExclPSL3Cover := by
  intro K _ _ hq hmodel _
  obtain ⟨-, F, hFfield, hFfin, hcard, ⟨e₀⟩⟩ := hmodel
  have hF4 : Nat.card F = 4 := by simpa using hcard
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF4]; norm_num)
  have hcardN := k32cov_card_projectiveSL_three hF4
  have e1 : K ⧸ CFSG.pCore 2 K ≃* LinearFlag.projectiveSL 3 F :=
    e₀.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm
  have hN1 : Nontrivial (LinearFlag.projectiveSL 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardN]; norm_num)
  have hZK : Subgroup.center K = CFSG.pCore 2 K :=
    k32cov_center_eq_pCore hq e1 CFSG.QuasithinUnique.Setup.X7Sec.center_projectiveSL_eq_bot hN1
  have e2 : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans e1
  have h2part : 2 ^ (Nat.card (LinearFlag.projectiveSL 3 F)).factorization 2 = 2 ^ 6 :=
    k32cov_two_pow_factorization hcardN (by decide)
  refine k32_noDatum_of_quot2 hq.1 e2 (hB F hF4) ?_ ?_
  · rw [h2part]; norm_num
  · rw [h2part]; norm_num

end CFSG.QuasithinUnique.DoubleA3
