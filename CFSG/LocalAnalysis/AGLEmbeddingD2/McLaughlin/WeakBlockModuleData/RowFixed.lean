module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PairTypes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NumericCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def SocleLE (L V : Subgroup G) (n : ℕ) : Prop :=
  (V ⊓ Subgroup.centralizer (L : Set G)).relIndex
    (⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) ≤ n

theorem fixed_of_nineThreeFive_pair [Finite G] (h86 : Asc81bEightSix) {M H R L : Subgroup G}
    (hpair : AGLPair 3 M H R) (hL : IsWeakSBlock M (pCoreOf 2 H) L) (h5 : NineThreeFive M L)
    {y : G} (hy : y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H)) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have hV : y ∈ blockV (pCoreOf 2 H) L := by
    have h := (hpair.blockV_facts h86 hL).2.2.1
    rw [h] at hy
    exact hy.1
  exact three_dvd_card_inf_centralizer_of_nineThreeFive hL.le hL.perfect h5
    (blockV_le_normalizer_of_pair hpair h86 hL) hV

theorem mulEquiv_of_center_eq_bot {X Y : Type} [Group X] [Group Y] (hZ : Subgroup.center X = ⊥)
    (e : X ⧸ Subgroup.center X ≃* Y) : Nonempty (X ≃* Y) :=
  ⟨((QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e⟩

theorem three_dvd_of_socleLE_alt_six [Finite G] {M L V : Subgroup G} (hLM : L ≤ M)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (e : ↥(barM M L) ≃* alternatingGroup (Fin 6))
    (hn : SocleLE L V 16) {y : G} (hy : y ∈ V) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  obtain ⟨F, hF⟩ := exists_surjective_barM hLM
  exact three_dvd_card_inf_centralizer_of_alt_six hLV hV2 hVc hy (e.toMonoidHom.comp F)
    (e.surjective.comp hF) hn

@[expose] def U33Atlas : Prop :=
  ∀ (X : Type) [Group X], IsUThreeThree X →
    Nat.card X = 6048 ∧ ∀ H : Subgroup X, ¬ 3 ∣ Nat.card H → Nat.card H ≤ 32

theorem three_dvd_of_socleLE_u33 [Finite G] (hat : U33Atlas) {M L V : Subgroup G} (hLM : L ≤ M)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hX : IsUThreeThree ↥(barM M L))
    (hn : SocleLE L V 64) {y : G} (hy : y ∈ V) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  obtain ⟨F, hF⟩ := exists_surjective_barM hLM
  obtain ⟨hcard, hbound⟩ := hat _ hX
  refine three_dvd_card_inf_centralizer_of_relIndex_bound hLV hV2 hVc hy hn fun Y hYL hY3 => ?_
  have h := mul_card_lt_card_of_surjective F hF (c := 32) (n := 64) hbound
    (by rw [hcard]; norm_num) (Y.subgroupOf L)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv])
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv] at h

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
