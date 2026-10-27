module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Core
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofCenter
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card
public import CFSG.HardMathSupport.Solomon.Proving.SU3CentreScalars
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Inner

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars StatedLieAdmissible)

theorem two_pow_sq (n : ℕ) : (2 ^ (3 * n)) ^ 2 = 64 ^ n := by
  rw [← pow_mul, show 3 * n * 2 = 6 * n by ring, pow_mul]
  norm_num

theorem sixtythree_dvd (n : ℕ) : 63 ∣ (2 ^ (3 * n)) ^ 2 - 1 := by
  rw [two_pow_sq]
  simpa using Nat.sub_dvd_pow_sub_pow 64 1 n

theorem three_pow_five_dvd {n : ℕ} (h3 : 3 ∣ 2 ^ (3 * n) + 1) :
    3 ^ 5 ∣ ((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1) := by
  have hq : 2 ^ (3 * n) = 8 ^ n := by rw [pow_mul]; norm_num
  rw [hq] at h3 ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exfalso
    have : 8 ^ (2 * k) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    omega
  set q := 8 ^ (2 * k + 1) with hqdef
  have hq9 : q % 9 = 8 := by
    rw [hqdef, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hQ9 : (q ^ 2) % 9 = 1 := by
    rw [Nat.pow_mod, hq9]
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  have hQq : q ≤ q ^ 2 := by nlinarith
  have hcube : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hQq]
    ring
  have hA : 9 ∣ q ^ 2 - 1 := by omega
  have hB : 9 ∣ q + 1 := by omega
  have hC : 3 ∣ q ^ 2 - q + 1 := by omega
  rw [hcube, show 3 ^ 5 = 9 * (9 * 3) by norm_num]
  exact Nat.mul_dvd_mul hA (Nat.mul_dvd_mul hB hC)

theorem map_center_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩ z
    have := hx (e.symm z)
    rw [← e.apply_symm_apply z, ← map_mul, ← map_mul, this]
  · intro hy
    refine ⟨e.symm y, fun z => ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy]

theorem Type418Arith.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Type418Arith Y) : Type418Arith X := by
  have hc := map_center_eq e
  have hq : Nat.card (X ⧸ Subgroup.center X) = Nat.card (Y ⧸ Subgroup.center Y) :=
    Nat.card_congr (QuotientGroup.congr _ _ e hc).toEquiv
  obtain ⟨h7, h9, h81⟩ := h
  refine ⟨hq ▸ h7, hq ▸ h9, fun hZ => hq ▸ h81 fun hY => hZ ?_⟩
  rw [← hc, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hY
  exact hY

theorem card_quot_center_of_eq_bot {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
  rw [← Subgroup.index_eq_card, h, Subgroup.index_bot]

theorem type418Arith_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : 63 ∣ Nat.card X) : Type418Arith X := by
  rw [Type418Arith, card_quot_center_of_eq_bot hZ]
  exact ⟨(by norm_num : 7 ∣ 63).trans h, (by norm_num : 3 ^ 2 ∣ 63).trans h,
    fun h' => absurd hZ h'⟩

theorem admissible_psl {m n : ℕ} (hm : m = 2 ∨ m = 3) (hn : 1 ≤ n) :
    StatedLieAdmissible .PSL m 2 (3 * n) := by
  have h8 : 2 ^ 3 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
  · intro h
    have := (Prod.mk.inj h).2
    omega
  · intro h
    have := (Prod.mk.inj h).2
    omega

theorem type418Arith_psl2 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hq : IsQuasisimple X)
    (φ : X ≃* projSL 2 (GaloisField 2 (3 * n))) : Type418Arith X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inl rfl) hn) hq φ
  refine type418Arith_of_center_eq_bot hZ ?_
  have hcard := Sec11.KSListsProof.card_projSL_two_mul (GaloisField 2 (3 * n))
  have hK : Nat.card (GaloisField 2 (3 * n)) = 2 ^ (3 * n) := GaloisField.card 2 _ (by omega)
  have hpos : 2 ≤ 2 ^ (3 * n) := Nat.le_self_pow (by omega) 2
  have hmod : (2 ^ (3 * n) - 1) % 2 = 1 := by
    have : 2 ^ (3 * n) % 2 = 0 := by
      rw [Nat.pow_mod]; simp [show 3 * n ≠ 0 by omega]
    omega
  have hgcd : Nat.gcd 2 (2 ^ (3 * n) - 1) = 1 := by
    rw [Nat.gcd_rec, hmod, Nat.gcd_one_left]
  rw [hK, hgcd, mul_one] at hcard
  rw [Nat.card_congr φ.toEquiv, hcard]
  exact Dvd.dvd.mul_left (sixtythree_dvd n) _

theorem type418Arith_psl3 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hq : IsQuasisimple X)
    (φ : X ≃* projSL 3 (GaloisField 2 (3 * n))) : Type418Arith X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := Sec13.Res5Proof.center_eq_bot_of_projSL (admissible_psl (Or.inr rfl) hn) hq φ
  refine type418Arith_of_center_eq_bot hZ ?_
  have hcard := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 (3 * n))
  have hK : Nat.card (GaloisField 2 (3 * n)) = 2 ^ (3 * n) := GaloisField.card 2 _ (by omega)
  rw [hK] at hcard
  rw [Nat.card_congr φ.toEquiv]
  set P := Nat.card (projSL 3 (GaloisField 2 (3 * n)))
  set q := 2 ^ (3 * n)
  have h63 := sixtythree_dvd n
  have hg : Nat.gcd 3 (q - 1) = 1 ∨ Nat.gcd 3 (q - 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 _)
  rcases hg with hg | hg
  · rw [hg, mul_one] at hcard
    rw [hcard]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h63 _) _
  · rw [hg] at hcard
    have h3q : 3 ∣ q - 1 := by
      have := Nat.gcd_dvd_right 3 (q - 1)
      rwa [hg] at this
    have h3c : 3 ∣ q ^ 3 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow q 1 3
      rw [one_pow] at this
      exact h3q.trans this
    have h189 : 63 * 3 ∣ P * 3 := by
      rw [hcard]
      exact Dvd.dvd.mul_left (Nat.mul_dvd_mul h63 h3c) _
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h189

theorem exists_scalar_of_mem_center_su3 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ (3 * n)) ^ 2) {z : CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K}
    (hz : z ∈ Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K)) :
    ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) u = (z : GL (Fin 3) K) ∧ u ^ 3 = 1 ∧
      (u : K) ^ (2 ^ (3 * n)) * u = 1 := by
  rw [CFSG.HardMathSupport.Solomon.Proving.center_statedSU_three_eq_scalars hK,
    Subgroup.mem_subgroupOf] at hz
  obtain ⟨u, hu⟩ := hz
  have hUD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * n) K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨hdet, huni⟩ := GH74.GLS.Stage2.Signalizer.Odd87.mem_statedSU_three hUD z.2
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hdet huni
  refine ⟨u, hu, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  · have h00 := congrFun (congrFun huni 0) 0
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply] at h00
    exact h00

theorem center_su3_facts {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ (3 * n)) ^ 2) :
    Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K)) ≤ 3 ∧
      (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K) ≠ ⊥ → 3 ∣ 2 ^ (3 * n) + 1) := by
  choose f hf using fun z : Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K) =>
    exists_scalar_of_mem_center_su3 hn hK z.2
  have hinj : Function.Injective
      (fun z : Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K) =>
        (⟨f z, (mem_rootsOfUnity 3 (f z)).mpr (hf z).2.1⟩ : rootsOfUnity 3 K)) := by
    intro z w h
    have h' : f z = f w := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [← (hf z).1, ← (hf w).1, h']
  refine ⟨(Nat.card_le_card_of_injective _ hinj).trans (card_rootsOfUnity _ _), ?_⟩
  intro hZ
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  obtain ⟨hzs, hu3, huq⟩ := hf z
  have hu1 : f z ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    rw [← hzs, h1, map_one]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (f z) = 3 := orderOf_eq_prime hu3 hu1
  have hq1 : f z ^ (2 ^ (3 * n) + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact huq
  have := orderOf_dvd_of_pow_eq_one hq1
  rwa [ho] at this


theorem type418Arith_su3 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ (3 * n)) ^ 2) :
    Type418Arith (CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K) := by
  set S := CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K
  set Z := Subgroup.center S
  have hcard := CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of' hK
  obtain ⟨hZ3, hZq⟩ := center_su3_facts hn hK
  have hsplit : Nat.card Z * Nat.card (S ⧸ Z) = Nat.card S := by
    rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
  set c := Nat.card Z
  set m := Nat.card (S ⧸ Z)
  have hc1 : 1 ≤ c := Nat.card_pos
  have h63 : 63 ∣ c * m := by
    rw [hsplit, hcard]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (sixtythree_dvd n) _) _
  have h7 : 7 ∣ m := by
    have h7cm : 7 ∣ c * m := (by norm_num : 7 ∣ 63).trans h63
    interval_cases c
    · simpa using h7cm
    · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7cm)
    · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7cm)
  have h81 : Z ≠ ⊥ → 3 ^ 4 ∣ m := by
    intro hZ
    have h35 : 3 ^ 5 ∣ c * m := by
      rw [hsplit, hcard, mul_assoc]
      exact Dvd.dvd.mul_left (three_pow_five_dvd (hZq hZ)) _
    have hc1' : c ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
    interval_cases c
    · exact absurd rfl hc1'
    · exact (pow_dvd_pow 3 (by norm_num : 4 ≤ 5)).trans
        (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h35)
    · rw [show 3 ^ 5 = 3 * 3 ^ 4 by norm_num] at h35
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h35
  refine ⟨h7, ?_, h81⟩
  by_cases hZ : Z = ⊥
  · have hc : c = 1 := Subgroup.card_eq_one.mpr hZ
    rw [hc, one_mul] at h63
    exact (by norm_num : 3 ^ 2 ∣ 63).trans h63
  · exact (pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans (h81 hZ)

theorem type418Arith_of {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hq : IsQuasisimple X)
    (h : Sec8.IsType418 X n) : Type418Arith X := by
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have heq : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * n)) K =
        CFSG.Open.StatedSU 3 (2 ^ (3 * n)) K := rfl
    exact Type418Arith.of_mulEquiv (e.trans (MulEquiv.subgroupCongr heq))
      (type418Arith_su3 hn hK)
  · exact type418Arith_psl2 hn hq φ
  · exact type418Arith_psl3 hn hq φ

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
