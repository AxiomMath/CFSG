module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_le_of_cap13 {N : Fin 4 → ℕ} (hCap : Cap13 (G := G) N) {y : G}
    (hy : orderOf y = 13) {r : ℕ}
    (hF : {s : G | Inv N 0 s ∧ s * y = y * s}.ncard ≤ r) {u : G} (hu : Inv N 0 u)
    (huy : u * y = y * u) : Nat.card (centralizer ({y} : Set G)) ≤ 52 * r := by
  set O : Set G := {y' | ∃ h ∈ centralizer ({y} : Set G), h * u * h⁻¹ = y'} with hO
  have hOF : O ⊆ {s : G | Inv N 0 s ∧ s * y = y * s} := by
    rintro _ ⟨h, hh, rfl⟩
    have hgy : h * y = y * h := mem_centralizer_singleton_iff.1 hh
    refine ⟨Inv.of_isConj hu (isConj_iff.2 ⟨h, rfl⟩), ?_⟩
    have hy' : h⁻¹ * y * h = y := by
      calc h⁻¹ * y * h = h⁻¹ * (y * h) := by group
        _ = h⁻¹ * (h * y) := by rw [hgy]
        _ = y := by group
    calc h * u * h⁻¹ * y = h * (u * (h⁻¹ * y * h)) * h⁻¹ := by group
      _ = h * (u * y) * h⁻¹ := by rw [hy']
      _ = h * (y * u) * h⁻¹ := by rw [huy]
      _ = (h * y) * u * h⁻¹ := by group
      _ = (y * h) * u * h⁻¹ := by rw [hgy]
      _ = y * (h * u * h⁻¹) := by group
  have hmul := card_inf_centralizer_mul_ncard_of_orbit (centralizer ({y} : Set G)) u O
    (fun h hh => ⟨h, hh, rfl⟩) (fun s' hs' => hs')
  have h52 :
      Nat.card (centralizer ({y} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ 52 := by
    rw [inf_comm]
    exact hCap hu hy huy
  have hOle : O.ncard ≤ r := (Set.ncard_le_ncard hOF (Set.toFinite _)).trans hF
  rw [← hmul]
  exact Nat.mul_le_mul h52 hOle

end Generic

section BabyMonster


theorem babyInv_zero_of_nineteen_dvd {f : NativeSporadic.B} (hf : orderOf f = 2)
    (h19 : 19 ∣ Nat.card (centralizer ({f} : Set NativeSporadic.B))) : BabyInv 0 f := by
  obtain ⟨k, hk⟩ := babyTableIII.1 f hf
  have hc : Nat.card (centralizer ({f} : Set NativeSporadic.B)) = babyCentOrder k := hk.2
  rw [hc] at h19
  have key : ∀ k : Fin 4, 19 ∣ babyCentOrder k → k = 0 := by
    intro k hk
    fin_cases k
    · rfl
    · exfalso
      revert hk
      norm_num [babyCentOrder]
    · exfalso
      revert hk
      norm_num [babyCentOrder]
    · exfalso
      revert hk
      norm_num [babyCentOrder]
  rw [key k h19] at hk
  exact hk

theorem b13_exports {y : NativeSporadic.B} (hy : orderOf y = 13) :
    {s : NativeSporadic.B | BabyInv 0 s ∧ s * y = y * s}.ncard ≤ 9 ∧
      Nat.card (centralizer ({y} : Set NativeSporadic.B)) ≤ 468 := by
  haveI hfin : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hp2 : ¬ 13 ^ 2 ∣ Nat.card NativeSporadic.B := by
    rw [CFSG.RankThree.OddKernel.card_B_eq]
    norm_num
  have P := b13_parts
  have inv : ∀ {t : NativeSporadic.B}, t * t = 1 → t ≠ 1 →
      Matrix.rank (CFSG.Monster.B.bMat t - 1) = 1860 → BabyInv 0 t := by
    intro t h1 h2 h3
    have h2' : orderOf t = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact h1) h2
    exact babyInv_zero_of_rank_1860 h2' h3
  have i1 := inv P.mul_self_t1 P.ne_one_t1 P.rank_t1
  have i2 := inv P.mul_self_t2 P.ne_one_t2 P.rank_t2
  have i5 := inv P.mul_self_t5 P.ne_one_t5 P.rank_t5
  have hF := BThirteen.ncard_commuting_le (N := babyCentOrder) (sz := babyOrbitSize)
    BThirteen.arith13_baby babyTableIV BThirteen.cap13_baby P.order_x i1 i5 i2 P.comm_t1.symm
    P.comm_t5.symm P.comm_t2.symm P.comm_t1_t5 P.ne_t5_t1 P.order_t1_t2 P.comm_g_t1 P.comm_g_t5
    P.comm_g_t2 P.conj_g
  obtain ⟨c, hc⟩ := isConj_iff.1
    (BThirteen.isConj_of_orderOf_thirteen hp2 P.order_x P.conj_g hy)
  set Fy : Set NativeSporadic.B := {s | BabyInv 0 s ∧ s * y = y * s} with hFy
  have hset : Fy = (fun s => c * s * c⁻¹) '' {s | Inv babyCentOrder 0 s ∧ s * xB13 = xB13 * s} := by
    ext s
    constructor
    · rintro ⟨hs0, hsy⟩
      refine ⟨c⁻¹ * s * c, ⟨?_, ?_⟩, by group⟩
      · exact Inv.of_isConj hs0 (isConj_iff.2 ⟨c⁻¹, by simp⟩)
      · rw [← hc] at hsy
        calc c⁻¹ * s * c * xB13 = c⁻¹ * (s * (c * xB13 * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * xB13 * c⁻¹) * s) * c := by rw [hsy]
          _ = xB13 * (c⁻¹ * s * c) := by group
    · rintro ⟨s', ⟨hs0, hsx⟩, rfl⟩
      refine ⟨Inv.of_isConj hs0 (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
      rw [← hc]
      calc c * s' * c⁻¹ * (c * xB13 * c⁻¹) = c * (s' * xB13) * c⁻¹ := by group
        _ = c * (xB13 * s') * c⁻¹ := by rw [hsx]
        _ = (c * xB13 * c⁻¹) * (c * s' * c⁻¹) := by group
  have hFcard : Fy.ncard ≤ 9 := by
    rw [hset, Set.ncard_image_of_injective _ (by
      intro a b hab
      simpa using hab)]
    exact hF
  refine ⟨hFcard, ?_⟩
  have hu₀ : c * t1B13 * c⁻¹ ∈ Fy := by
    rw [hset]
    exact ⟨t1B13, ⟨i1, P.comm_t1⟩, rfl⟩
  have h468 := card_centralizer_le_of_cap13 BThirteen.cap13_baby hy
    (show {s : NativeSporadic.B | Inv babyCentOrder 0 s ∧ s * y = y * s}.ncard ≤ 9 from hFcard)
    hu₀.1 hu₀.2
  omega

end BabyMonster

end CFSG.HardMathSupport.Dickson.Sec6.I1431
