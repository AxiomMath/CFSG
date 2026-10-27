module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Constrained

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

theorem core4_of_std
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) : Core4 E t z :=
  core4 (core3 (core2 (core1 (core0 hF h hz))))

theorem lemma_3_2_exists (hF : FiniteFacts) (h : Std G L E t) : ∃ z : G, IsZ E t z :=
  hF.cocode.exists_z G E t h.m24

theorem lemma_3_2
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) :
    KleinPair t z ∧ ¬ IsConj t z ∧ IsConj t (t * z) ∧
    Nat.card ↥(CNz E z) = 2 ^ 21 * 3 ^ 3 * 5 ∧ (∃ S : Sylow 2 G, (S : Subgroup G) ≤ CNz E z) ∧
    Nat.card ↥(CNz E z ⊓ centralizer ({t} : Set G)) = 2 ^ 19 * 3 * 5 ∧
    (∃ y ∈ Nrm E ⊓ Jg t z, y * t * y⁻¹ = t * z) ∧
    Nat.card ↥(Nrm E ⊓ Jg t z) = 2 ^ 20 * 3 * 5 ∧
    Nat.card ↥(Kg t z) = 2 ^ 19 * 3 ^ 4 * 5 :=
  have c0 := core0 hF h hz
  ⟨c0.klein, c0.zdata.notConj, c0.zdata.conj_tz, c0.zdata.card_CNz, c0.zdata.sylow_CNz,
    c0.cocode.card_Ctz, c0.cocode.swap, c0.cocode.card_NV, c0.zdata.card_K⟩

theorem lemma_3_4
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) : JRData t z :=
  (core1 (core0 hF h hz)).jr

theorem lemma_3_5
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) : RPData E t z :=
  (core2 (core1 (core0 hF h hz))).rp

theorem lemma_3_8
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) :
    CFSG.IsExtraspecial 2 ↥(Rg t z) ∧ Nat.card ↥(Rg t z) = 2 ^ 13 ∧
      Phi2 (Rg t z) = zpowers z ∧ (center ↥(Rg t z)).map (Rg t z).subtype = zpowers z :=
  have c := core4_of_std hF h hz
  ⟨c.extra.extraspecial, c.jr.card_R, c.extra.phi_eq, center_Rg_map c.toCore3.toCore2.toCore1⟩

theorem lemma_3_11
    (hSch : CatalogOuterSolvable) (hB : DS81Lemma210Strong)
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) :
    CFSG.IsCharacteristicP 2 ↥(Cz z) :=
  isCharacteristicP_Cz h.std (core4_of_std hF h hz) hSch hB

theorem lemma_3_12
    (hSch : CatalogOuterSolvable) (hB : DS81Lemma210Strong)
    (hF : FiniteFacts) (h : Std G L E t) (hz : IsZ E t z) : O2CData t z :=
  o2cData (core4_of_std hF h hz) (lemma_3_11 hSch hB hF h hz)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
