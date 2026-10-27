module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoMain

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_sylow_eq_sup_zpowers_of_isSylowOf (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f))
    (hRS : IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G)))
    {P : Subgroup G} (hP : IsPGroup 2 P) (htN : t ∈ normalizer (P : Set G))
    (hSP : d.S.map L.subtype ≤ P)
    (hN : normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) =
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ⊔ P) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = P ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)
    with hA
  have htS : t ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun n hn => by
      rw [← mem_centralizer_iff.1 h.htL n (map_subtype_le _ hn), mul_inv_cancel_right]
      exact hn
  have htA : zpowers t ≤ A := (zpowers_le).2 ⟨h.t_mem_centralizer, htS⟩
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hRA : yamadaR d t ≤ A := by
    rw [hR]
    exact sup_le (le_inf (h.S_le_centralizer d) le_normalizer) htA
  have hQ : IsPGroup 2 (P ⊔ zpowers t : Subgroup G) :=
    hP.to_sup_of_normal_left' (IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one]))
      ((zpowers_le).2 htN)
  have hN' : normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) = A ⊔ (P ⊔ zpowers t) := by
    rw [hN, ← sup_assoc, eq_comm, sup_eq_left]
    exact htA.trans le_sup_left
  have hRQ : yamadaR d t ≤ P ⊔ zpowers t := by
    rw [hR]
    exact sup_le_sup_right hSP _
  exact exists_sylow_eq_of_normalizer_eq_sup_D4 hQ hN' (hRS.of_le hRA inf_le_left) hRQ

theorem false_of_isSylowOf_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (hRS : IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G))) :
    False := by
  obtain ⟨-, hPp, htP, htN, hSP, -, -, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have h521 := h.yamada_5_21 d hlay
  have hB := h.exists_sylow_eq_sup_zpowers_of_isSylowOf d hRS hPp htN hSP
    (h.normalizer_yamadaP_sup_zpowers d hlay (h.commutator_yamadaP_sup_zpowers d hlay)
      (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx))
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
  have hB2 : 2 ≤ Nat.card (yamadaY₂ d t) := by
    rw [(h.yamada_5_9_2 d hlay).2.1]
    calc 2 ≤ 2 ^ f := hq
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)
  refine h.false_of_isSylow_sup_zpowers_of_lt_card d hB htN htP fun y hy hy2 => ?_
  obtain ⟨E, hE, hEC, hcard⟩ := exists_isElemAbelian_two_mul_card_le h521.2.1
    (le_sup_right.trans (h.yamadaW₂_le_yamadaW₃ d hlay)) hB2 hy2
    (h.commutator_mem_yamadaY₂_of_mem_yamadaP d hlay y hy)
  refine ⟨E, hE, hEC, ?_⟩
  rw [h521.2.2, (h.yamada_5_9_2 d hlay).2.1] at hcard
  exact two_mul_pow_five_lt_of_two_mul_pow_ten_le hq hcard

theorem even_of_not_isSylowOf (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hRS : ¬ IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G))) : Even f :=
  Nat.not_odd_iff_even.1 fun hf => hRS (h.isSylowOf_yamadaR_centralizer_of_odd d hf)

end Setup

@[expose] def TrialityD4FieldAutomorphismCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)), 2 ≤ f → Even f → h.LayerHyp d →
    ¬ IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G)) → False

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem false_of_layerHyp_of_fieldCase (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : 2 ≤ f) (hlay : h.LayerHyp d) (hres : TrialityD4FieldAutomorphismCase) : False := by
  by_cases hRS : IsSylowOf 2 (yamadaR d t) (centralizer ({t} : Set G))
  · exact h.false_of_isSylowOf_of_layerHyp d hlay hRS
  · exact hres G L f t h d hf (h.even_of_not_isSylowOf d hRS) hlay hRS

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
