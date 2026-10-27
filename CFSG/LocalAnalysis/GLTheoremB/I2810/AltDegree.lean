module

public import CFSG.GF2Type.Smith1980Orth.IdentArith
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaCentreZMod2
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open Finset CFSG.GF2Type.Smith1980Orth

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree

theorem two_pow_not_dvd_factorial' {n : ℕ} (hn : n ≠ 0) : ¬ 2 ^ n ∣ n.factorial := by
  intro h
  have h1 := pow_dvd_iff_le_emultiplicity.mp h
  have h2 := Nat.emultiplicity_two_factorial_lt hn
  exact absurd h2 (not_lt.mpr h1)

theorem sqProd_le (k : ℕ) : sqProd k ≤ 2 ^ (k * (k + 1)) := by
  induction k with
  | zero => simp [sqProd]
  | succ k ih =>
    have h : sqProd (k + 1) = sqProd k * (2 ^ (2 * (k + 1)) - 1) := by
      unfold sqProd
      rw [Finset.prod_Icc_succ_top (by omega)]
    rw [h]
    calc sqProd k * (2 ^ (2 * (k + 1)) - 1) ≤ 2 ^ (k * (k + 1)) * 2 ^ (2 * (k + 1)) :=
          Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = 2 ^ ((k + 1) * (k + 1 + 1)) := by rw [← pow_add]; congr 1; ring

theorem omegaOdd_le (b : Bool) {m : ℕ} (hm : 1 ≤ m) :
    omegaOdd b m ≤ 2 ^ (m + 1) * 2 ^ ((m - 1) * m) := by
  unfold omegaOdd
  have h1 : (if b = true then 2 ^ m - 1 else 2 ^ m + 1) ≤ 2 ^ (m + 1) := by
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    split_ifs <;> omega
  have h3 := sqProd_le (m - 1)
  rw [Nat.sub_add_cancel hm] at h3
  exact Nat.mul_le_mul h1 h3

theorem pow_three_le_factorial : ∀ N : ℕ, 14 ≤ N → 2 ^ (3 * N - 20) ≤ N.factorial := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => decide
  | succ N hN ih =>
    rw [Nat.factorial_succ]
    calc 2 ^ (3 * (N + 1) - 20) = 2 ^ (3 * N - 20) * 8 := by
          rw [show 3 * (N + 1) - 20 = (3 * N - 20) + 3 by omega, pow_add]; norm_num
      _ ≤ N.factorial * (N + 1) := Nat.mul_le_mul ih (by omega)
      _ = (N + 1) * N.factorial := by ring

theorem no_alt_order (b : Bool) {N m : ℕ} (hm : 4 ≤ m) (hN : 5 ≤ N)
    (h : N.factorial / 2 = 2 ^ (m * (m - 1)) * omegaOdd b m) : False := by
  have h2 : 2 ∣ N.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfac : N.factorial = 2 ^ (m * (m - 1) + 1) * omegaOdd b m := by
    have := Nat.mul_div_cancel' h2
    rw [← this, h]; ring
  have hE : m * (m - 1) + 2 ≤ N := by
    by_contra hlt
    push_neg at hlt
    apply two_pow_not_dvd_factorial' (n := N) (by omega)
    have : 2 ^ N ∣ 2 ^ (m * (m - 1) + 1) := pow_dvd_pow 2 (by omega)
    exact this.trans (hfac ▸ dvd_mul_right _ _)
  have hup : N.factorial ≤ 2 ^ (2 * (m * (m - 1)) + m + 2) := by
    rw [hfac]
    calc 2 ^ (m * (m - 1) + 1) * omegaOdd b m
        ≤ 2 ^ (m * (m - 1) + 1) * (2 ^ (m + 1) * 2 ^ ((m - 1) * m)) :=
          Nat.mul_le_mul_left _ (omegaOdd_le b (by omega))
      _ = 2 ^ (2 * (m * (m - 1)) + m + 2) := by
          rw [← pow_add, ← pow_add, mul_comm (m - 1) m]; congr 1; ring
  have hlow : (m * (m - 1) + 2).factorial ≤ N.factorial := Nat.factorial_le hE
  rcases (by omega : m = 4 ∨ m = 5 ∨ 6 ≤ m) with rfl | rfl | hm6
  · have : 2 ^ (2 * (4 * (4 - 1)) + 4 + 2) < (4 * (4 - 1) + 2).factorial := by decide
    omega
  · have : 2 ^ (2 * (5 * (5 - 1)) + 5 + 2) < (5 * (5 - 1) + 2).factorial := by decide
    omega
  · have h30 : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul hm6 (by omega)
    have h3 := pow_three_le_factorial (m * (m - 1) + 2) (by omega)
    have hexp : 2 * (m * (m - 1)) + m + 2 < 3 * (m * (m - 1) + 2) - 20 := by
      have h4 : m + 16 < m * (m - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
        have hk1 : m - 1 = k + 5 := by omega
        rw [hk1, hk]
        nlinarith
      omega
    have h5 : 2 ^ (2 * (m * (m - 1)) + m + 2) < 2 ^ (3 * (m * (m - 1) + 2) - 20) :=
      Nat.pow_lt_pow_right (by norm_num) hexp
    omega

theorem card_statedProj_zmod2 {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : Nat.card (CFSG.Open.StatedProj H) = Nat.card H := by
  have hs : (CFSG.Open.StatedScalars ι (ZMod 2)).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hs).trans
    (QuotientGroup.quotientBot (G := H))).toEquiv

theorem card_omegaPlus (n : ℕ) (hn : 3 ≤ n) :
    Nat.card ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) =
      2 ^ ((n + 1) * n) * omegaOdd true (n + 1) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := ZMod 2)
    (n := n + 1) (by omega)
  rw [card_statedProj_zmod2] at h
  have h2 := cast_omegaOdd true (n + 1) (ε := 1) (Or.inl ⟨rfl, rfl⟩)
  simp only [Nat.card_zmod, Nat.cast_ofNat, Nat.add_sub_cancel] at h h2
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  push_cast
  rw [h2]
  ring

theorem card_omegaMinus (n : ℕ) (hn : 3 ≤ n) :
    Nat.card ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) =
      2 ^ ((n + 1) * n) * omegaOdd false (n + 1) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := ZMod 2)
    (n := n + 1) (by omega) (b := 1) (c := 1) (by decide)
  rw [card_statedProj_zmod2] at h
  have h2 := cast_omegaOdd false (n + 1) (ε := -1) (Or.inr ⟨rfl, rfl⟩)
  simp only [Nat.card_zmod, Nat.cast_ofNat, Nat.add_sub_cancel] at h h2
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  push_cast
  rw [h2]
  ring

theorem card_alt_eq_of_equiv {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) {N : ℕ}
    (hN : 2 ≤ N) (e : alternatingGroup (Fin N) ≃* (G ⧸ Subgroup.center G)) :
    N.factorial / 2 = Nat.card G := by
  haveI : Nontrivial (Fin N) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
  have h1 : Nat.card (alternatingGroup (Fin N)) = N.factorial / 2 := by
    rw [nat_card_alternatingGroup]; simp
  rw [← h1, Nat.card_congr e.toEquiv]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := G))).toEquiv

theorem center_eq_bot_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxL : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [h, Subgroup.mem_bot] at hxL
  exact e.injective (by rw [hxL, map_one])

theorem not_isSolvable_alt {n₀ : ℕ} (hn₀ : 5 ≤ n₀) :
    ¬ Group.IsSolvable (alternatingGroup (Fin n₀)) := by
  haveI : Group.IsPerfect (alternatingGroup (Fin n₀)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn₀)⟩
  haveI : Nontrivial (alternatingGroup (Fin n₀)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  exact Group.IsPerfect.not_isSolvable _

theorem solvable_omegaPlusFour : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  have hφ : ∀ v, StatedQuadPlus 2 (ZMod 2)
      ((LinearEquiv.refl (ZMod 2) (Fin 2 ⊕ Fin 2 → ZMod 2)) v) =
        (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)) v := fun v =>
    (congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus 2 (ZMod 2)) v).symm
  have hs := CFSG.HardMathSupport.Cooperstein.StructureLie.solvable_of_isPlusSpace_small
    (Q := CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)) (m := 2) le_rfl
    ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  exact Group.isSolvable_of_isSolvable_injective
    (f := (CFSG.HardMathSupport.Cooperstein.StructureLie.statedOmegaEquiv
      (LinearEquiv.refl (ZMod 2) (Fin 2 ⊕ Fin 2 → ZMod 2)) hφ).toMonoidHom)
    (CFSG.HardMathSupport.Cooperstein.StructureLie.statedOmegaEquiv
      (LinearEquiv.refl (ZMod 2) (Fin 2 ⊕ Fin 2 → ZMod 2)) hφ).injective

theorem card_omegaMinusSix :
    Subgroup.center ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) = ⊥ ∧
      Nat.card ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) = 25920 := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv hK
      hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have hcenY : Subgroup.center ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))) with h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hna
  refine ⟨hcenY, ?_⟩
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hcenSU : Subgroup.center ↥(StatedSU 4 (2 ^ 1) E) = ⊥ :=
    center_eq_bot_of_equiv eSU.symm hcenY
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := 1) hE
      (by norm_num) hnq).2, hcenSU]
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := E) Nat.prime_two
    (le_refl 1) hE (by norm_num : 2 ≤ 4)
  have h1 : Nat.card (StatedProj (StatedSU 4 (2 ^ 1) E)) = Nat.card (StatedSU 4 (2 ^ 1) E) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hscal).trans
      QuotientGroup.quotientBot).toEquiv
  rw [Nat.card_congr eSU.toEquiv, ← h1, hcard]
  decide +kernel

theorem factorial_div_two_ne {N : ℕ} (hN : 5 ≤ N) : N.factorial / 2 ≠ 25920 := by
  intro h
  have h2 : 2 ∣ N.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have : N.factorial = 51840 := by omega
  rcases Nat.lt_or_ge N 9 with h9 | h9
  · have := Nat.factorial_le (show N ≤ 8 by omega)
    have h8 : (8 : ℕ).factorial = 40320 := by decide
    omega
  · have := Nat.factorial_le h9
    have h8 : (9 : ℕ).factorial = 362880 := by decide
    omega

theorem plus_degree {n₀ n : ℕ} (hn₀ : 5 ≤ n₀) (hn : 1 ≤ n)
    (e : ↥(alternatingGroup (Fin n₀)) ≃*
      (↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) ⧸
        Subgroup.center ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))))) : n = 2 := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
  · exfalso
    haveI := solvable_omegaPlusFour
    haveI : Group.IsSolvable
        (↥(StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2))) ⧸
          Subgroup.center ↥(StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2)))) := inferInstance
    exact not_isSolvable_alt hn₀
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · rfl
  · exfalso
    have hZ := CFSG.HardMathSupport.Timmesfeld.Proving.center_statedOmega_quadPlus_zmod2
      (n := n + 1) (by omega)
    have hcard := card_alt_eq_of_equiv hZ (by omega) e
    rw [card_omegaPlus n h3] at hcard
    exact no_alt_order true (m := n + 1) (by omega) hn₀ (by simpa using hcard)

theorem minus_degree {n₀ n : ℕ} (hn₀ : 5 ≤ n₀) (hn : 1 ≤ n)
    (e : ↥(alternatingGroup (Fin n₀)) ≃*
      (↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ⧸
        Subgroup.center ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))) : n = 1 := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
  · rfl
  · exfalso
    obtain ⟨hZ, hc⟩ := card_omegaMinusSix
    have hcard := card_alt_eq_of_equiv hZ (by omega) e
    rw [hc] at hcard
    exact factorial_div_two_ne hn₀ hcard
  · exfalso
    have hZ := CFSG.HardMathSupport.Timmesfeld.Proving.center_statedOmega_quadMinus_zmod2
      (n := n + 1) (by omega)
    have hcard := card_alt_eq_of_equiv hZ (by omega) e
    rw [card_omegaMinus n h3] at hcard
    exact no_alt_order false (m := n + 1) (by omega) hn₀ (by simpa using hcard)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree
