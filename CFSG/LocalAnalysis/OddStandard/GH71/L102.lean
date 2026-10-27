module

public import CFSG.LocalAnalysis.OddStandard.GH71.L102J
public import CFSG.LocalAnalysis.OddStandard.GH71.L102Choice

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

theorem zIn_ne_bot {P : Subgroup G} (hP3 : IsPGroup 3 ↥P) (hP1 : P ≠ ⊥) : zIn P ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have := hP3.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(center ↥P))
  intro hb
  apply hc
  have hcZ : ((c : ↥P) : G) ∈ zIn P := by
    refine ⟨(c : ↥P).2, mem_centralizer_iff.mpr fun p hp => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp c.2 ⟨p, hp⟩)
  rw [hb, mem_bot] at hcZ
  exact Subtype.ext (Subtype.ext hcZ)

theorem thompson_ne_bot {P : Subgroup G} (hP3 : IsPGroup 3 ↥P) (hP1 : P ≠ ⊥) :
    Open.thompsonSubgroup P ≠ ⊥ := by
  obtain ⟨A, hA⟩ := exists_isMaxAbelianIn P
  have hZab : IsMulCommutative ↥(zIn P) :=
    ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩
  have h1 : Nat.card (zIn P) ≤ Nat.card A := hA.2.2 _ (zIn_le P) hZab
  intro hJ
  have hA1 : A = ⊥ := le_bot_iff.mp (hJ ▸ le_thompson hA)
  rw [hA1, card_bot] at h1
  have h0 : 0 < Nat.card (zIn P) := Nat.card_pos
  exact zIn_ne_bot hP3 hP1 (card_eq_one.mp (by omega))

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71


theorem lemma_10_2 (h : Ctx71 G z S U u) (hB0 : SpecB0) (hB1 : SpecB1) (hB4 : SpecB4)
    (hB5 : SpecB5) (h812 : IVK_8_12_ly) {P₁ : Subgroup G}
    (hP₁ : Open.fusionIsSylowIn 3 P₁ (pPrimeCoreOf 2 (Cen z)))
    (hSP₁ : S ≤ normalizer (P₁ : Set G)) (hP₁1 : P₁ ≠ ⊥)
    (hP₁S : ¬ S ≤ centralizer (P₁ : Set G)) :
    ∃ P K : Subgroup G, MaxSInv 3 S ⊤ P ∧ P₁ ≤ P ∧ normalizer (P : Set G) ≤ K ∧ K ≠ ⊤ ∧
      Covers K (Cen z) (pPrimeCoreOf 2 (Cen z)) := by
  have hP₁cov : Covers (normalizer (P₁ : Set G)) (Cen z) (pPrimeCoreOf 2 (Cen z)) :=
    covers_frattini Nat.prime_three (pPrimeCoreOf_le' _) (le_normalizer_pPrimeCoreOf' _)
      (odd_card_pPrimeCoreOf' _) hP₁
  obtain ⟨Q, P, hadm, hmaxP, hmaxQ⟩ := exists_adm102_max (z := z) (S := S) (P₁ := P₁)
    ⟨hP₁1, hP₁.2.1, hSP₁, hP₁cov, le_normalizer, hP₁.2.1, hSP₁, le_rfl⟩
  obtain ⟨hH, hbar, hP, hP₁Q, hRQ⟩ := h.choice_102 hB1 h812 hP₁ hP₁1 hadm hmaxP hmaxQ
  obtain ⟨hQ1, hQ3, hSQ, hQcov, hPN, hP3, hSP, hP₁P⟩ := hadm
  have hP1 : P ≠ ⊥ := fun hb => hP₁1 (le_bot_iff.mp (hb ▸ hP₁P))
  have hmaxG : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 3 ↥X →
      normalizer (P : Set G) ≤ normalizer (X : Set G) →
      Covers (normalizer (X : Set G)) (Cen z) (pPrimeCoreOf 2 (Cen z)) → MaxSInv 3 S ⊤ P := by
    intro X hX1 hX3 hPX hXcov
    refine ⟨le_top, hP3, hSP, fun W _ hW3 hSW hPW => ?_⟩
    by_contra hne
    have hlt : P < W := lt_of_le_of_ne hPW (Ne.symm hne)
    have h1 := lt_inf_normalizer_of_lt Nat.prime_three hW3 hlt
    have hadm' : Adm102 z S P₁ X (W ⊓ normalizer (X : Set G)) :=
      ⟨hX1, hX3, hSP.trans hPX, hXcov, inf_le_right, hW3.to_le inf_le_left,
        fun s hs => inf_normalizer_le_normalizer_inf ⟨hSW hs, le_normalizer (hPX (hSP hs))⟩,
        le_inf (hP₁P.trans hPW) (hP₁P.trans (le_normalizer.trans hPX))⟩
    have h3 : P < W ⊓ normalizer (X : Set G) := lt_of_lt_of_le h1 (inf_le_inf_left _ hPX)
    exact absurd (card_lt_of_lt' h3) (not_lt.mpr (hmaxP _ _ hadm'))
  rcases h.case_split_102 hB5 hSQ hQcov hbar hP hRQ le_rfl hP₁Q hP₁S with hZ | hL
  ·
    have hZ3 : IsPGroup 3 ↥(zIn P) := hP3.to_le (zIn_le P)
    have hZ1 := zIn_ne_bot hP3 hP1
    exact ⟨P, _, hmaxG _ hZ1 hZ3 (normalizer_le_normalizer_zIn P) hZ, hP₁P,
      normalizer_le_normalizer_zIn P, h.normalizer_ne_top hZ3 hZ1, hZ⟩
  ·
    have hJ : Open.thompsonSubgroup P = Open.thompsonSubgroup Q :=
      thompson_eq_of_forall_le (by rw [← hRQ]; exact inf_le_left)
        (fun D hD => h.le_of_isMaxAbelianIn hB0 hB4 h812 hH hSQ hQcov hbar hP hRQ le_rfl hL hD)
    have hJ3 : IsPGroup 3 ↥(Open.thompsonSubgroup P) := hP3.to_le (thompson_le P)
    have hJ1 := thompson_ne_bot hP3 hP1
    have hcovJ : Covers (normalizer (Open.thompsonSubgroup P : Set G)) (Cen z)
        (pPrimeCoreOf 2 (Cen z)) :=
      covers_mono (by rw [hJ]; exact normalizer_le_normalizer_thompson Q) hQcov
    exact ⟨P, _, hmaxG _ hJ1 hJ3 (normalizer_le_normalizer_thompson P) hcovJ, hP₁P,
      normalizer_le_normalizer_thompson P, h.normalizer_ne_top hJ3 hJ1, hcovJ⟩

end Ctx71

end CFSG.OddStandard.GH71
