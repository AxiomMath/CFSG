module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.UniquenessTransferCentralizerRankTwo
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import Mathlib.GroupTheory.Solvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p d : ℕ}

theorem nonempty_mulEquiv_multiplicative_pi_iff (A : Subgroup G) :
    Nonempty (↥A ≃* Multiplicative (Fin d → ZMod p)) ↔
      Nonempty (↥A ≃* (Fin d → Multiplicative (ZMod p))) :=
  ⟨fun ⟨e⟩ => ⟨e.trans (MulEquiv.funMultiplicative _ _)⟩,
   fun ⟨e⟩ => ⟨e.trans (MulEquiv.funMultiplicative _ _).symm⟩⟩

theorem natCard_of_nonempty_mulEquiv_multiplicative_pi {A : Subgroup G}
    (h : Nonempty (↥A ≃* Multiplicative (Fin d → ZMod p))) : Nat.card ↥A = p ^ d := by
  obtain ⟨e⟩ := (nonempty_mulEquiv_multiplicative_pi_iff A).mp h
  rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]

theorem isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi {A : Subgroup G}
    (h : Nonempty (↥A ≃* Multiplicative (Fin d → ZMod p))) : IsElementaryAbelian p A :=
  isElementaryAbelian_of_nonempty_mulEquiv_pi ((nonempty_mulEquiv_multiplicative_pi_iff A).mp h)

theorem le_elementaryAbelianPRank_of_nonempty_mulEquiv [Finite G] (hp : p.Prime) {A X : Subgroup G}
    (h : Nonempty (↥A ≃* Multiplicative (Fin d → ZMod p))) (hAX : A ≤ X) :
    d ≤ elementaryAbelianPRank p ↥X :=
  (isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi h).le_elementaryAbelianPRank hp
    (natCard_of_nonempty_mulEquiv_multiplicative_pi h) hAX

theorem exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank [Finite G] (hp : p.Prime)
    {X : Subgroup G} (h : d ≤ elementaryAbelianPRank p ↥X) :
    ∃ A ≤ X, Nonempty (↥A ≃* Multiplicative (Fin d → ZMod p)) := by
  obtain ⟨A, hAX, hcomm, hexp, hcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := X) (d := d) hp).mp
      ((le_elementaryAbelianPRank_iff hp.one_lt).mp h)
  refine ⟨A, hAX, (nonempty_mulEquiv_multiplicative_pi_iff A).mpr ?_⟩
  exact nonempty_mulEquiv_pi_of_isElementaryAbelian hp
    (isElementaryAbelian_iff.mpr
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩) hcard

theorem bot_lt_of_nonempty_mulEquiv_of_le (hp : 1 < p) (hd : d ≠ 0) {X Y : Subgroup G}
    (h : Nonempty (↥X ≃* Multiplicative (Fin d → ZMod p))) (hXY : X ≤ Y) : ⊥ < Y := by
  refine lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr ?_) hXY
  intro hX
  have hc := natCard_of_nonempty_mulEquiv_multiplicative_pi h
  rw [hX, Subgroup.card_bot] at hc
  exact absurd hc.symm (Nat.one_lt_pow hd hp).ne'

theorem conj_inv_smul_le_of_le_conj_smul {X Y : Subgroup G} {g : G}
    (h : X ≤ MulAut.conj g • Y) : MulAut.conj g⁻¹ • X ≤ Y :=
  Subgroup.pointwise_smul_subset_iff.mpr (by rwa [map_inv, inv_inv])

theorem isUniqueMaximalOvergroup_conj_smul_of_three_le_elementaryAbelianPRank_centralizer
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    {A M B : Subgroup G} [IsMulCommutative ↥A] (hApg : IsPGroup p ↥A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A) (hAM : IsUniqueMaximalOvergroup A M)
    (hBpg : IsPGroup p ↥B) (hBnc : ¬ IsCyclic ↥B)
    (hBrank : 3 ≤ elementaryAbelianPRank p ↥(centralizer (B : Set G))) :
    ∃ g : G, IsUniqueMaximalOvergroup B (MulAut.conj g • M) := by
  have := Fact.mk hp
  have hpG : p ∣ Nat.card G :=
    ((one_le_elementaryAbelianPRank_iff hp).mp (le_trans (by norm_num) hBrank)).trans
      (Subgroup.card_subgroup_dvd_card _)
  have hpodd : Odd p := hodd.of_dvd_nat hpG
  obtain ⟨C, hCB, hC⟩ :=
    exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank (d := 3) hp hBrank
  have hCea := isElementaryAbelian_of_nonempty_mulEquiv_multiplicative_pi hC
  have hCcomm : IsMulCommutative ↥C := (isElementaryAbelian_iff.mp hCea).1
  obtain ⟨P, hCP⟩ := hCea.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_le_conj_smul_sylow P hApg
  set A' := MulAut.conj g⁻¹ • A with hA'def
  have hA'P : A' ≤ (P : Subgroup G) := conj_inv_smul_le_of_le_conj_smul hg
  have hA'M : IsUniqueMaximalOvergroup A' (MulAut.conj g⁻¹ • M) := hAM.smul g⁻¹
  have hA'comm : IsMulCommutative ↥A' := isMulCommutative_conj_smul g⁻¹ A
  have hA'rank : 3 ≤ elementaryAbelianPRank p ↥A' := by
    rw [hA'def, ← elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
      (Subgroup.equivSMul (MulAut.conj g⁻¹) A)]
    exact hArank
  obtain ⟨E, hEA', hE⟩ :=
    exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank (d := 3) hp hA'rank
  have hPrank : 3 ≤ elementaryAbelianPRank p ↥(P : Subgroup G) :=
    le_elementaryAbelianPRank_of_nonempty_mulEquiv hp hC hCP
  have hPnc : ¬ IsCyclic ↥(P : Subgroup G) :=
    not_isCyclic_of_three_le_elementaryAbelianPRank hp hPrank
  have hPtopnc : ¬ IsCyclic ↥(⊤ : Subgroup ↥(P : Subgroup G)) := fun _ =>
    hPnc (isCyclic_of_surjective
      (Subgroup.topEquiv : (⊤ : Subgroup ↥(P : Subgroup G)) ≃* _) Subgroup.topEquiv.surjective)
  obtain ⟨D₀, -, hD₀norm, hD₀⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hpodd
    P.isPGroup' (⊤ : Subgroup ↥(P : Subgroup G)) hPtopnc
  set D : Subgroup G := Subgroup.map (P : Subgroup G).subtype D₀ with hDdef
  have hD : Nonempty (↥D ≃* Multiplicative (Fin 2 → ZMod p)) := by
    obtain ⟨e⟩ := hD₀
    exact (nonempty_mulEquiv_multiplicative_pi_iff D).mpr
      ⟨(D₀.equivMapOfInjective (P : Subgroup G).subtype
        (P : Subgroup G).subtype_injective).symm.trans e⟩
  have hDnorm : (P : Subgroup G) ≤ normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    rw [hDdef, Subgroup.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, hD₀norm.conj_mem y' hy' ⟨x, hx⟩, by simp⟩
  obtain ⟨K₁, hK₁le, hK₁⟩ := exists_elementaryAbelian_rank_two_le_inf_centralizer hD hE
    (hEA'.trans (hA'P.trans hDnorm))
  obtain ⟨K₂, hK₂le, hK₂⟩ := exists_elementaryAbelian_rank_two_le_inf_centralizer hD hC
    (hCP.trans hDnorm)
  have h1 : IsUniqueMaximalOvergroup K₁ (MulAut.conj g⁻¹ • M) :=
    isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
      (bot_lt_of_nonempty_mulEquiv_of_le hp.one_lt three_ne_zero hE hEA') hA'M
      ((hK₁le.trans inf_le_left).trans (hEA'.trans (Subgroup.le_centralizer A')))
      (le_elementaryAbelianPRank_of_nonempty_mulEquiv hp hK₁ le_rfl)
  have h2 : IsUniqueMaximalOvergroup D (MulAut.conj g⁻¹ • M) :=
    isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
      (bot_lt_of_nonempty_mulEquiv_of_le hp.one_lt two_ne_zero hK₁ le_rfl) h1
      (Subgroup.le_centralizer_iff.mp (hK₁le.trans inf_le_right))
      (le_elementaryAbelianPRank_of_nonempty_mulEquiv hp hD le_rfl)
  have h3 : IsUniqueMaximalOvergroup K₂ (MulAut.conj g⁻¹ • M) :=
    isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
      (bot_lt_of_nonempty_mulEquiv_of_le hp.one_lt two_ne_zero hD le_rfl) h2
      (hK₂le.trans inf_le_right)
      (le_elementaryAbelianPRank_of_nonempty_mulEquiv hp hK₂ le_rfl)
  have h4 : IsUniqueMaximalOvergroup C (MulAut.conj g⁻¹ • M) :=
    isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
      (bot_lt_of_nonempty_mulEquiv_of_le hp.one_lt two_ne_zero hK₂ le_rfl) h3
      ((Subgroup.le_centralizer C).trans (Subgroup.centralizer_le (hK₂le.trans inf_le_left)))
      (le_trans (by norm_num) (le_elementaryAbelianPRank_of_nonempty_mulEquiv hp hC le_rfl))
  have h5 : IsUniqueMaximalOvergroup B (MulAut.conj g⁻¹ • M) :=
    isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
      (bot_lt_of_nonempty_mulEquiv_of_le hp.one_lt three_ne_zero hC le_rfl) h4
      (Subgroup.le_centralizer_iff.mp hCB)
      (two_le_elementaryAbelianPRank_of_not_isCyclic hp hpodd hBpg hBnc)
  exact ⟨g⁻¹, h5⟩

theorem exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_centralizer
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    {A B : Subgroup G} [IsMulCommutative ↥A] (hApg : IsPGroup p ↥A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAM : ∃ M : Subgroup G, IsUniqueMaximalOvergroup A M)
    (hBpg : IsPGroup p ↥B) (hBnc : ¬ IsCyclic ↥B)
    (hBrank : 3 ≤ elementaryAbelianPRank p ↥(centralizer (B : Set G))) :
    ∃ N : Subgroup G, IsUniqueMaximalOvergroup B N := by
  obtain ⟨M, hM⟩ := hAM
  obtain ⟨g, hg⟩ :=
    isUniqueMaximalOvergroup_conj_smul_of_three_le_elementaryAbelianPRank_centralizer hp hna hodd
      hsolv hApg hArank hM hBpg hBnc hBrank
  exact ⟨_, hg⟩

end

end CFSG.FeitThompson
