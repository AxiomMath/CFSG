module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Eqs

variable {G : Type} [Group G]

theorem Fm_def (M : Subgroup G) : Fm M = (fittingSubgroup ↥M).map M.subtype := rfl

theorem Fs_def (M : Subgroup G) : Fs M = (generalizedFitting ↥M).map M.subtype := rfl

theorem Em_def (M : Subgroup G) : Em M = (layer ↥M).map M.subtype := rfl

theorem Op_def (p : ℕ) (M : Subgroup G) : Op p M = (pCore p ↥M).map M.subtype := rfl

theorem card_Fm (M : Subgroup G) : Nat.card ↥(Fm M) = Nat.card ↥(fittingSubgroup ↥M) :=
  Subgroup.card_map_of_injective M.subtype_injective

theorem card_Fs (M : Subgroup G) : Nat.card ↥(Fs M) = Nat.card ↥(generalizedFitting ↥M) :=
  Subgroup.card_map_of_injective M.subtype_injective

theorem card_Op (p : ℕ) (M : Subgroup G) : Nat.card ↥(Op p M) = Nat.card ↥(pCore p ↥M) :=
  Subgroup.card_map_of_injective M.subtype_injective

theorem Fm_le (M : Subgroup G) : Fm M ≤ M := Subgroup.map_subtype_le _

theorem Fs_le (M : Subgroup G) : Fs M ≤ M := Subgroup.map_subtype_le _

theorem Em_le (M : Subgroup G) : Em M ≤ M := Subgroup.map_subtype_le _

theorem Op_le (p : ℕ) (M : Subgroup G) : Op p M ≤ M := Subgroup.map_subtype_le _

theorem le_normalizer_map_subtype (M : Subgroup G) (K : Subgroup M) [K.Normal] :
    M ≤ normalizer ((K.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Normal.conj_mem ‹K.Normal› y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨m, hm⟩⁻¹ * y * ⟨m, hm⟩⁻¹⁻¹, Normal.conj_mem ‹K.Normal› y hy _, ?_⟩
    have h1 : (y : G) = m * x * m⁻¹ := hyx
    show (m⁻¹ * (y : G) * m⁻¹⁻¹ : G) = x
    rw [h1]
    group

theorem le_normalizer_Fm (M : Subgroup G) : M ≤ normalizer ((Fm M : Subgroup G) : Set G) :=
  le_normalizer_map_subtype M (fittingSubgroup ↥M)

theorem le_normalizer_Fs (M : Subgroup G) : M ≤ normalizer ((Fs M : Subgroup G) : Set G) := by
  have : (generalizedFitting ↥M).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  exact le_normalizer_map_subtype M (generalizedFitting ↥M)

theorem le_normalizer_Op (p : ℕ) (M : Subgroup G) : M ≤ normalizer ((Op p M : Subgroup G) : Set G) :=
  haveI : (pCore p ↥M).Normal := pCore_normal
  le_normalizer_map_subtype M (pCore p ↥M)

theorem Op_le_Fm (p : ℕ) (hp : p.Prime) (M : Subgroup G) [Finite G] : Op p M ≤ Fm M := by
  have : Fact p.Prime := ⟨hp⟩
  exact Subgroup.map_mono (CFSG.pCore_le_fitting ↥M p)

end Eqs

section PGroup

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_Op (p : ℕ) (hp : p.Prime) (M : Subgroup G) : IsPGroup p ↥(Op p M) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (pCore_isPGroup (p := p) (G := ↥M))
  exact IsPGroup.of_card (n := n) (by rw [card_Op, hn])

end PGroup

section Odd

theorem quasisimple_not_odd {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) :
    ¬ Odd (Nat.card K) := by
  intro hodd
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨hperf, hsimple, -⟩ := hK
  have : Group.IsPerfect K := hperf
  have : Nontrivial (K ⧸ center K) := hsimple.toNontrivial
  have : Nontrivial K := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.not_isSolvable K hsolv

theorem layer_eq_bot_of_odd {N : Type} [Group N] [Finite N]
    (h : Odd (Nat.card ↥(generalizedFitting N))) : layer N = ⊥ := by
  have hempty : {K : Subgroup N | IsComponent K} = ∅ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hK
    have hKF : K ≤ generalizedFitting N := le_sup_right.trans' (le_sSup hK)
    have hdvd : Nat.card ↥K ∣ Nat.card ↥(generalizedFitting N) := Subgroup.card_dvd_of_le hKF
    exact quasisimple_not_odd hK.1 (Odd.of_dvd_nat h hdvd)
  simp only [CFSG.layer.eq_sSup]
  rw [hempty, sSup_empty]

theorem generalizedFitting_eq_fitting_of_odd {N : Type} [Group N] [Finite N]
    (h : Odd (Nat.card ↥(generalizedFitting N))) : generalizedFitting N = fittingSubgroup N := by
  simp only [CFSG.generalizedFitting.eq_sup]
  rw [layer_eq_bot_of_odd h, sup_bot_eq]

theorem pPrimeCore_two_eq_top {X : Type} [Group X] [Finite X] (h : Odd (Nat.card X)) :
    pPrimeCore 2 X = ⊤ := by
  refine le_antisymm le_top (le_sSup ⟨inferInstance, ?_⟩)
  rw [Subgroup.card_top]
  exact Nat.coprime_two_left.mpr h

theorem fitting_eq_of_odd {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (h : Odd (Nat.card ↥(generalizedFitting ↥N))) : Fs N = Fm N ∧ Fm N = pPrimeCoreOf 2 (Fm N) := by
  have hgf := generalizedFitting_eq_fitting_of_odd h
  have hFs : Fs N = Fm N := by
    rw [Fs_def, Fm_def, hgf]
  refine ⟨hFs, ?_⟩
  have hodd : Odd (Nat.card ↥(Fm N)) := by
    rw [← hFs, card_Fs]
    exact h
  have h2 : pPrimeCore 2 ↥(Fm N) = ⊤ := pPrimeCore_two_eq_top hodd
  unfold pPrimeCoreOf
  rw [h2, Subgroup.map_top, Subgroup.range_subtype]

end Odd

end CFSG.GH74.GLS.Stage2.Bender.Thm1
