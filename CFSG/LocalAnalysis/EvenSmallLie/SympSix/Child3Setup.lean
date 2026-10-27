module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6LagrangianEvenSymplecticExclusion
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Sporadic.He.Simple
public import CFSG.LocalAnalysis.SteinbergBVSp6DirectSimpleLayer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianFullOddCore
import CFSG.Adapters.LieModelOrders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem setting_of_standardSetting {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1) :
    ∃ (T : Sylow 2 (centralizer (L : Set G))) (z : G), Setting L T z := by
  classical
  have hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L := hset.standard
  obtain ⟨T, hT⟩ := hset.cyclic
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2C : 2 ∣ Nat.card (centralizer (L : Set G)) := even_iff_two_dvd.1 hL.2.1
  have h2T : 2 ∣ Nat.card (T : Subgroup (centralizer (L : Set G))) := by
    have hpow := T.card_eq_multiplicity
    rw [hpow]
    refine dvd_pow_self 2 ?_
    intro h0
    rw [Nat.factorization_eq_zero_iff] at h0
    rcases h0 with h0 | h0 | h0
    · exact h0 Nat.prime_two
    · exact h0 h2C
    · exact Nat.card_pos.ne' h0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2T
  refine ⟨T, ((t : centralizer (L : Set G)) : G), ?_⟩
  have hz : orderOf ((t : centralizer (L : Set G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  exact
    { simple := hset.simple
      nonab := hset.nonab
      kProper := hset.kProper
      oddCore_eq := SteinbergBI.oddCore_eq_bot_of_isStandardSubgroup hset.simple hL
      standard := hL
      not_normal := SteinbergBI.not_normal_of_isStandardSubgroup hset.simple hset.nonab hL
      center_eq := hZ
      model := SteinbergBI.lieModel_PSp_of_center_eq_bot hZ hQ
      core := hset.core
      cyclic := hT
      mem := ⟨t, t.2, rfl⟩
      order := hz
      core_z := hset.core _ hz }

theorem exists_symplectic_model {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.Blueprint.LieModel L .PSp 3 2 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
      (b : BilinForm (ZMod 2) V) (_ : b.IsAlt) (_ : b.Nondegenerate)
      (_ : finrank (ZMod 2) V = 6) (_ : L ≃* bilinIsometryGroup b)
      (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V), IsSymplecticBasis b e := by
  obtain ⟨V, i1, i2, i3, b, hb, hnd, hV, ⟨φ⟩⟩ := exists_model_of_lieModel hL
  obtain ⟨e, he⟩ := exists_isSymplecticBasis hb hnd (n := 3) (by rw [hV])
  exact ⟨V, i1, i2, i3, b, hb, hnd, hV, φ, e, he⟩

theorem card_of_lieModel_classical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Blueprint.LieModel X t n p f) :
    Nat.card X = CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) :=
  CFSG.Blueprint.LieModel.card_eq_lieOrd hn h

theorem card_of_lieModel_PSp_three_two {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSp 3 2 1) : Nat.card X = 1451520 :=
  CFSG.Blueprint.LieModel.card_psp_three_two h

theorem evenStandardType_of {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSp 3 2 1) :
    CFSG.Blueprint.Recognition.Exact.EvenStandardType Q :=
  Or.inl ⟨.PSp, 3, 1, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, h⟩

theorem evenStandardResidual_of {L : Type} [Group L] (hZ : center L = ⊥)
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1) :
    CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L := by
  refine ⟨?_, Or.inr (Or.inr (Or.inl (Or.inl h)))⟩
  rw [hZ]
  exact IsPGroup.of_bot

theorem not_evenStandardException_of {Q : Type} [Group Q]
    (h : CFSG.Blueprint.LieModel Q .PSp 3 2 1) :
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException Q := by
  classical
  have hQ := card_of_lieModel_PSp_three_two h
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  ·
    have hle : Nat.card Q ≤ Fintype.card K ^ 16 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (commutator (Matrix.symplecticGroup (Fin 2) K))
          ≤ Nat.card (Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = Fintype.card K ^ 16 := by
            rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
            ring
    rw [hQ, hK] at hle
    exact absurd hle (by norm_num)
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
      Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Q ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    rw [hQ] at hle
    exact absurd hle (by norm_num)
  · rw [card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_of_lieModel_classical (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv] at hQ
    change Nat.card CFSG.Blueprint.NativeSporadic.He = _ at hQ
    rw [CFSG.Sporadic.He.card_He] at hQ
    exact absurd hQ (by norm_num)

theorem fullOddCore_of_schreier (hS : SchreierFor CFSG.Blueprint.Catalog) :
    Sp6LagrangianFullOddCoreStmt :=
  sp6_lagrangian_full_odd_core_of
    (CFSG.LocalAnalysis.SteinbergBV.direct_simple_involution_centralizer_layer_of_schreier hS)

end CFSG.EvenSmallLie.Child3
