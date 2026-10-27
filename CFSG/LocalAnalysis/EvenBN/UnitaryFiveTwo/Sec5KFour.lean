module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KThree
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Sporadic.He.Simple
import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition.Exact

section Sp44

theorem card_eq_lieOrd_of_lieModel {X : Type} [Group X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0) (h : LieModel X t n p f) :
    Nat.card X = CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) :=
  CFSG.Blueprint.LieModel.card_eq_lieOrd hn h

theorem card_of_lieModel_PSp_two_two {X : Type} [Group X] (h : LieModel X .PSp 2 2 2) :
    Nat.card X = 979200 := by
  rw [card_eq_lieOrd_of_lieModel (by norm_num) h]
  decide

theorem evenStandardType_of_PSp44 {Q : Type} [Group Q] (h : LieModel Q .PSp 2 2 2) :
    EvenStandardType Q :=
  Or.inl ⟨.PSp, 2, 2, ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩, h⟩

theorem not_evenStandardException_of_PSp44 {Q : Type} [Group Q] (h : LieModel Q .PSp 2 2 2) :
    ¬ EvenStandardException Q := by
  classical
  have hQ := card_of_lieModel_PSp_two_two h
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [card_eq_lieOrd_of_lieModel (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_eq_lieOrd_of_lieModel (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_eq_lieOrd_of_lieModel (by norm_num) h1] at hQ
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
  · rw [card_eq_lieOrd_of_lieModel (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · rw [card_eq_lieOrd_of_lieModel (by norm_num) h1] at hQ
    exact absurd hQ (by decide)
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv] at hQ
    change Nat.card CFSG.Blueprint.NativeSporadic.He = _ at hQ
    rw [CFSG.Sporadic.He.card_He] at hQ
    exact absurd hQ (by norm_num)

theorem false_of_standard_PSp44
    (hPSp2 : ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSp 2 2 f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    {L : Subgroup G} (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (hm : LieModel L .PSp 2 2 2) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) : False := by
  let e : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmQ : LieModel (L ⧸ center L) .PSp 2 2 2 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  have heven := hPSp2 G hnonab hK L hL hcore S hS (evenStandardType_of_PSp44 hmQ)
    (not_evenStandardException_of_PSp44 hmQ) ⟨2, le_rfl, hmQ⟩
  rw [hZ, Subgroup.card_bot] at heven
  exact Nat.not_even_one heven

end Sp44

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem false_of_gomiOneP
    (hPSp2 : ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSp 2 2 f)
    (h : d.Hyp) (hK : d.KLinear) (hH : ¬ d.H ≤ d.L ⊔ zpowers d.t)
    (h1P : ∀ a : G, ∀ ha : a ∈ d.H, a * a = 1 → h.act ⟨a, ha⟩ = fld → IsGraphOn d.K a →
      IsFieldOn d.K (d.t * a) → GomiOnePConclusion a) : False := by
  obtain ⟨a, haH, ha1, haf, hag, hta⟩ := h.exists_graph_involution hK hH
  have ha2 : orderOf a = 2 := by
    refine orderOf_eq_prime (by rw [sq, ha1]) fun h1 => ?_
    have hσ : UnitaryFiveTwo.fieldFactor fld ≠ 1 := by
      rw [fieldFactor_fld]
      exact barEquiv_ne_one
    apply hσ
    rw [← haf, show (⟨a, haH⟩ : d.H) = 1 from Subtype.ext h1, map_one, map_one]
  obtain ⟨L', hstd, hZ, hm, -, S, hS⟩ :=
    exists_standard_of_gomiOneP ha2 (h1P a haH ha1 haf hag hta)
  have := h.simple
  have hcyc : IsCyclic (S : Subgroup (centralizer (L' : Set G))) := by
    have hc : IsCyclic ((S : Subgroup (centralizer (L' : Set G))).map
        (centralizer (L' : Set G)).subtype) := by
      rw [hS]
      infer_instance
    exact (MulEquiv.isCyclic ((S : Subgroup (centralizer (L' : Set G))).equivMapOfInjective _
      (centralizer (L' : Set G)).subtype_injective)).2 hc
  exact false_of_standard_PSp44 hPSp2 h.nonab h.setting.setting.kProper h.core hstd hZ hm S hcyc

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
