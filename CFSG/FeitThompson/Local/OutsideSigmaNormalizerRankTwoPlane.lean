module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Local.HighRankCentralTorsionLine
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Foundations.CentralExtensionNilpotent
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ} {M X : Subgroup G}

theorem characteristic_or_exists_isElementaryAbelian_natCard_eq_sq
    {P : Type*} [Group P] [Finite P] (hp : p.Prime) (hPp : IsPGroup p P)
    {Y : Subgroup P} (hY : Nat.card Y = p) :
    Y.Characteristic ∨
      ∃ A : Subgroup P, Y ≤ A ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ 2 := by
  have hYne : Nontrivial Y := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  have hPnt : Nontrivial P := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hYne
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hZ : centerTorsionBy P p ≠ ⊥ := centerTorsionBy_ne_bot_of_isPGroup hp hPp
  by_cases hle : centerTorsionBy P p ≤ Y
  ·
    left
    have hcard : Nat.card (centerTorsionBy P p) = p := by
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [hY] at hdvd
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hZ
      · exact h
    have heq : centerTorsionBy P p = Y := Subgroup.eq_of_le_of_card_ge hle (by rw [hY, hcard])
    rw [← heq]
    infer_instance
  ·
    right
    obtain ⟨z, hz, hzY⟩ := Set.not_subset.1 hle
    have hz1 : z ≠ 1 := fun h => hzY (h ▸ one_mem Y)
    have hord : orderOf z = p := orderOf_eq_of_mem_centerTorsionBy hp hz hz1
    have hWc : Subgroup.zpowers z ≤ Subgroup.center P :=
      Subgroup.zpowers_le.2 (centerTorsionBy_le_center p hz)
    have hWn : (Subgroup.zpowers z).Normal := normal_of_le_center hWc
    have hWcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hord]
    have hWea : IsElementaryAbelian p (Subgroup.zpowers z) :=
      IsElementaryAbelian.of_natCard_eq_prime hp hWcard
    have hYea : IsElementaryAbelian p Y := IsElementaryAbelian.of_natCard_eq_prime hp hY
    have hinf : Subgroup.zpowers z ⊓ Y = ⊥ := by
      have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers z ⊓ Y ≤ _)
      rw [hWcard] at hdvd
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hWcard, h]) ▸
          (inf_le_right : Subgroup.zpowers z ⊓ Y ≤ Y)) fun hh => hzY (hh (mem_zpowers z))
    refine ⟨Subgroup.zpowers z ⊔ Y, le_sup_right, ?_, ?_⟩
    · rw [sup_comm]
      exact hYea.sup_of_le_center hWea hWc
    · have := hWn
      rw [natCard_sup_eq_mul_of_normal_of_inf_eq_bot hinf, hWcard, hY, sq]

theorem exists_isElementaryAbelian_natCard_eq_sq_of_notMem_sigmaPrimes [Finite G] (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hX : Nat.card X = p) (hNX : normalizer (X : Set G) ≤ M) :
    ∃ A : Subgroup G, X ≤ A ∧ A ≤ M ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ 2 := by
  have := Fact.mk hp
  have hXM : X ≤ M := le_trans Subgroup.le_normalizer hNX
  have hXsub : Nat.card (X.subgroupOf M) = p ^ 1 := by
    rw [pow_one, Nat.card_congr (subgroupOfEquivOfLe hXM).toEquiv, hX]
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hXsub).exists_le_sylow
  set P : Subgroup G := (S : Subgroup M).map M.subtype with hPdef
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hXP : X ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hS
  have hPp : IsPGroup p P := S.isPGroup'.map M.subtype
  have hYcard : Nat.card (X.subgroupOf P) = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv, hX]
  rcases characteristic_or_exists_isElementaryAbelian_natCard_eq_sq hp hPp hYcard with hchar | hA
  ·
    exfalso
    refine hpM (mem_sigmaPrimes_iff.2 ⟨hp, hX ▸ Subgroup.card_dvd_of_le hXM, S, ?_⟩)
    have h := normalizer_le_normalizer_map_subtype P (X.subgroupOf P)
    rw [Subgroup.map_subgroupOf_eq_of_le hXP] at h
    exact h.trans hNX
  · obtain ⟨A, hXA, hAea, hAcard⟩ := hA
    refine ⟨A.map P.subtype, ?_, (Subgroup.map_subtype_le _).trans hPM, hAea.map_subtype, ?_⟩
    · rw [← Subgroup.map_subgroupOf_eq_of_le hXP]
      exact Subgroup.map_mono hXA
    · rw [Subgroup.card_subtype, hAcard]

theorem exists_mulEquiv_pi_of_notMem_sigmaPrimes [Finite G] (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hX : Nat.card X = p) (hNX : normalizer (X : Set G) ≤ M) :
    ∃ A : Subgroup G, X ≤ A ∧ A ≤ M ∧ Nonempty (A ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  obtain ⟨A, hXA, hAM, hAea, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_sq_of_notMem_sigmaPrimes hp hpM hX hNX
  exact ⟨A, hXA, hAM, nonempty_mulEquiv_pi_of_isElementaryAbelian hp hAea hAcard⟩

theorem two_le_elementaryAbelianPRank_of_notMem_sigmaPrimes [Finite G] (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hX : Nat.card X = p) (hNX : normalizer (X : Set G) ≤ M) :
    2 ≤ elementaryAbelianPRank p M := by
  obtain ⟨A, -, hAM, hAea, hAcard⟩ :=
    exists_isElementaryAbelian_natCard_eq_sq_of_notMem_sigmaPrimes hp hpM hX hNX
  exact hAea.le_elementaryAbelianPRank hp hAcard hAM

theorem elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable Y) (hM : IsCoatom M) (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hX : Nat.card X = p) (hNX : normalizer (X : Set G) ≤ M) :
    elementaryAbelianPRank p M = 2 := by
  refine le_antisymm ?_ (two_le_elementaryAbelianPRank_of_notMem_sigmaPrimes hp hpM hX hNX)
  by_contra h
  exact hpM (mem_sigmaPrimes_of_mem_alphaPrimes hna hodd hsolv hM
    (mem_alphaPrimes.2 ⟨hp, by omega⟩))

theorem elementaryAbelianPRank_eq_two_and_exists_plane_of_notMem_sigmaPrimes [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable Y) (hM : IsCoatom M) (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hX : Nat.card X = p) (hNX : normalizer (X : Set G) ≤ M) :
    elementaryAbelianPRank p M = 2 ∧
      ∃ A : Subgroup G, X ≤ A ∧ A ≤ M ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ 2 :=
  ⟨elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hna hodd hsolv hM hp hpM hX hNX,
    exists_isElementaryAbelian_natCard_eq_sq_of_notMem_sigmaPrimes hp hpM hX hNX⟩

end

end CFSG.FeitThompson
