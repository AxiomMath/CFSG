module

import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.LieType.Catalog.Realization
public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCPair
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement MatrixGroups

theorem isQuasisimple_of_hasSL2Model_card {K : Type} [Group K] {q : ℕ}
    (h : HasSL2Model K (fun r => r = q)) (hq : 4 ≤ q) : IsQuasisimple K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := hF ▸ hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialLinearGroupEquivStatedSL 2 F)
      (Odd87.isQuasisimple_special_linear_two h4))

theorem concl43E_simple
    {A : Type} [Group A] [Finite A] {ε : Bool} {z : A} {p : ℕ} {X : Subgroup A}
    (h : Concl43E (Kind.l4 ε) z p X) : IsSimpleGroup (↥(ncl X) ⧸ center ↥(ncl X)) := by
  rcases h with hb | hc | hd | he
  · obtain ⟨n, hn, hsl, -⟩ := hb
    exact (isQuasisimple_of_hasSL2Model_card hsl (by omega)).2.1
  · obtain ⟨n, -, hL, -⟩ := hc
    exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
  · exact absurd hd.1 (by simp)
  · exact (isQuasisimple_of_hasSL2Model_card he.1 (by norm_num)).2.1

theorem false_of_concl43E
    {Y : Type} [Group Y] [Finite Y] (hY : PairData Y) {ε : Bool} {z : Y} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup Y} (hXp : IsPGroup p ↥X) (hX : X ≠ ⊥)
    (h : Concl43E (Kind.l4 ε) z p X) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hXtriv : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX
  obtain ⟨x, hx⟩ : ∃ x : ↥X, orderOf x = p := by
    obtain ⟨n, hn⟩ := hXp.nontrivial_iff_card.mp hXtriv
    exact exists_prime_orderOf_dvd_card' p (by rw [hn.2]; exact dvd_pow_self p hn.1.ne')
  have hxo : orderOf (x : Y) = p := by rw [Subgroup.orderOf_coe, hx]
  have hx1 : (x : Y) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hodd : Odd (orderOf (x : Y)) := by
    rw [hxo]
    exact hp.eq_two_or_odd'.resolve_left hp2
  have hxK : (x : Y) ∈ ncl X := Subgroup.subset_normalClosure x.2
  exact hY.false_of_normal_simple (Subgroup.normalClosure_normal) hxK hx1 hodd (concl43E_simple h)

theorem comm_Em_ne_bot {G : Type} [Group G] [Finite G] {H X : Subgroup G} (hH : PairData ↥H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXH : X ≤ H) (hXp : IsPGroup p ↥X) (hX : X ≠ ⊥) :
    ⁅Em H, X⁆ ≠ ⊥ := by
  have hXp' : IsPGroup p ↥(X.subgroupOf H) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  have hX' : X.subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hX
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hXH hy⟩ : ↥H) ∈ X.subgroupOf H := hy
    rw [hbot, Subgroup.mem_bot] at hy'
    simpa using congrArg Subtype.val hy'
  have h1 := hH.comm_layer_ne_bot hp hp2 hXp' hX'
  intro hbot
  apply h1
  have h2 : ⁅(layer ↥H).map H.subtype, X⁆ = (⁅layer ↥H, X.subgroupOf H⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH]
  have h3 : (⁅layer ↥H, X.subgroupOf H⁆).map H.subtype = ⊥ := by rw [← h2]; exact hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h3

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
