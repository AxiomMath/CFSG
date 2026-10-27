module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
import CFSG.Goldschmidt.Steps.GoldType
import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicUnitary

public section

open CFSG.Open Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.AschbacherToolkit.Bender

private theorem sylowCenter_eq_self_of_comm {G : Type*} [Group G] {T : Subgroup G}
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : sylowCenter T = T := by
  refine le_antisymm (sylowCenter_le T) fun x hx => mem_sylowCenter.mpr ⟨hx, fun t ht => ?_⟩
  exact (hcomm x hx t ht).symm

private theorem sylow_eight_of_card_eight_mul {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {u : ℕ} (hu : Odd u) (hG : Nat.card G = 8 * u) :
    Nat.card (T : Subgroup G) = 8 := by
  rw [T.card_eq_multiplicity, hG,
    CFSG.ComponentClassification.WalterSchur.factorization_two_eight_mul hu]
  norm_num

private theorem false_of_abelian_center_lt {G : Type*} [Group G] {T : Sylow 2 G} {q k : ℕ}
    (hcomm : ∀ a ∈ (T : Subgroup G), ∀ b ∈ (T : Subgroup G), a * b = b * a)
    (hZ : Nat.card (sylowCenter (T : Subgroup G)) = q)
    (hT : Nat.card (T : Subgroup G) = q ^ k) (hq : 2 ≤ q) (hk : 2 ≤ k) : False := by
  have hZeq : sylowCenter (T : Subgroup G) = (T : Subgroup G) :=
    sylowCenter_eq_self_of_comm hcomm
  have hcardq : Nat.card (T : Subgroup G) = q := by rw [← hZ, hZeq]
  have hpow : q ^ k = q := by rw [← hT, hcardq]
  have hlt : q < q ^ k := by
    have := Nat.pow_lt_pow_right (show 1 < q by omega) (show 1 < k by omega)
    rwa [pow_one] at this
  omega

private theorem pow_four_ne_eight {m : ℕ} (hm : 1 ≤ m) : (4 : ℕ) ^ m ≠ 8 := by
  intro h
  have h2 : (2 : ℕ) ^ (2 * m) = 2 ^ 3 := by
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, h,
      show (8 : ℕ) = 2 ^ 3 by norm_num]
  have : 2 * m = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  omega

theorem goldtype_elementary_sylow {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : goldschmidtSimpleType K) (T : Sylow 2 K) {m : ℕ} (hm : 1 ≤ m)
    (hcomm : ∀ a ∈ (T : Subgroup K), ∀ b ∈ (T : Subgroup K), a * b = b * a)
    (hcard : Nat.card (T : Subgroup K) = 4 ^ m) :
    (m = 1 ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < n ∧ 5 ≤ p ^ n ∧
        (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ Nonempty (K ≃* PSL(2, GaloisField p n))) ∨
      (∃ f : ℕ, f = 2 * m ∧ 3 ≤ f ∧ Nonempty (K ≃* PSL(2, GaloisField 2 f))) := by
  unfold goldschmidtSimpleType at hK
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hpo, hf, hp5, h8, ⟨e⟩⟩ | ⟨m', hm', hcardK⟩ | ⟨he⟩
  ·
    right
    haveI : Finite (PSL(2, GaloisField 2 f)) := Finite.of_equiv K e.toEquiv
    set T' : Sylow 2 (PSL(2, GaloisField 2 f)) :=
      T.mapSurjective (f := e.toMonoidHom) e.surjective
    have hT' : (T' : Subgroup (PSL(2, GaloisField 2 f))) =
        (T : Subgroup K).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
    have hcardT' : Nat.card (T' : Subgroup (PSL(2, GaloisField 2 f))) = 2 ^ f :=
      CFSG.Quasithin.St84.psl2_sylow_two_card (by omega) T'
    have hmap : Nat.card ((T : Subgroup K).map e.toMonoidHom) =
        Nat.card (T : Subgroup K) := Subgroup.card_map_of_injective e.injective
    have hpow : (2 : ℕ) ^ f = 2 ^ (2 * m) := by
      rw [← hcardT', hT', hmap, hcard, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hfm : f = 2 * m := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    exact ⟨f, hfm, hf, ⟨e⟩⟩
  ·
    exfalso
    have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz hn e
    obtain ⟨-, -, hZ, hT⟩ :=
      CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter hB T
    refine false_of_abelian_center_lt hcomm hZ hT ?_ (by norm_num)
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    exfalso
    obtain ⟨hT, hZ, -⟩ := CFSG.ComponentClassification.GMS78.sylow_psu3 hf e T
    refine false_of_abelian_center_lt hcomm hZ hT ?_ (by norm_num)
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    left
    haveI := hp
    have hTcard : Nat.card (T : Subgroup K) = 4 :=
      (CFSG.Goldschmidt.GoldType.sylow_of_psl2_odd hpo hf h8 e T).1
    have hm1 : m = 1 := by
      have h41 : (4 : ℕ) ^ m = 4 ^ 1 := by rw [← hcard, hTcard, pow_one]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h41
    exact ⟨hm1, p, f, hp, hpo, hf, hp5, h8, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨u, hu, hu8⟩ := CFSG.ComponentClassification.WalterSchur.ordRee_eq_eight_mul m'
    have hcardT : Nat.card (T : Subgroup K) = 8 :=
      sylow_eight_of_card_eight_mul T hu (hcardK.trans hu8)
    exact pow_four_ne_eight hm (hcard.symm.trans hcardT)
  ·
    exfalso
    obtain ⟨e⟩ := he
    have hcardK' : Nat.card K = 175560 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.ComponentClassification.WalterSchur.goldschmidtJ1_eq_walterJ1,
        CFSG.Walter.J1Props.card_walterJ1]
    have hcardT : Nat.card (T : Subgroup K) = 8 :=
      sylow_eight_of_card_eight_mul T (u := 21945) (by decide) (by norm_num [hcardK'])
    exact pow_four_ne_eight hm (hcard.symm.trans hcardT)

end CFSG.OddStandard.SmallF3.Omega
