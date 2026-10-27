module

public import CFSG.LocalAnalysis.EvenBN.G2.FieldNatural

import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_isElemAbelian_of_mem_yamadaM₆_or_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {x : G} (hx : x ∈ yamadaM₆ d t ∨ x ∈ yamadaD₇ d t) (hx2 : x * x = 1) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ E ≤ centralizer ({x} : Set G) ∧
      2 * Nat.card K ^ 3 < Nat.card E := by
  have hD := hQ.doubling
  have hq3 : 2 * Nat.card K ^ 3 < Nat.card K ^ 4 := by
    have h3 : 2 < Nat.card K := lt_of_lt_of_le (by norm_num) hQ.four_le
    calc 2 * Nat.card K ^ 3 < Nat.card K * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right h3 (by positivity)
      _ = Nat.card K ^ 4 := by ring
  rcases hx with hxM | hxD
  ·
    refine ⟨yamadaY₂ d t, ⟨⟨⟨fun a b => Subtype.ext (h.yamadaY₂_mul_comm d hK hD a.2 b.2)⟩⟩,
      fun y hy => ?_⟩, fun y hy => ?_, ?_⟩
    · rw [sq]
      exact h.yamadaY₂_mul_self hW d hK hD hy
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (Q44.M₆_le_centralizer_Y₂ hW h d hK hQ hxM) y hy
    · rw [h.card_yamadaY₂ d hK hD]
      exact hq3
  ·
    obtain ⟨hWe, hWc, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
    obtain ⟨hZ, -⟩ := h.yamada_5_52 hW d hK hQ
    have hD₇P : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
    have hZ' : yamadaP d t ⊓ centralizer (yamadaP d t : Set G) = yamadaU₁ d t := by
      rw [← map_upperCentralSeries_one]
      exact hZ
    have hU₁D₇ : yamadaU₁ d t ≤ centralizer (yamadaD₇ d t : Set G) := fun u hu =>
      Subgroup.centralizer_le hD₇P (hZ'.ge hu).2
    have hdiv := Common.card_le_card_inf_centralizer_mul_card (D := yamadaD₇ d t)
      (Z := yamadaU₁ d t) (A := yamadaW₃ d t) (h.yamada_5_55_1 hW d hK hQ).1.2.le hU₁D₇
      (h.yamadaW₃_le_yamadaD₇ hW d hK hQ) hxD
    refine ⟨yamadaW₃ d t ⊓ centralizer ({x} : Set G),
      (isElemAbelian_iff_isElementaryAbelian.mpr hWe).mono inf_le_left, inf_le_right, ?_⟩
    rw [hWc, hD.card_eq] at hdiv
    have hq : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
    have h6 : Nat.card K ^ 4 * Nat.card K ^ 2 ≤
        Nat.card (yamadaW₃ d t ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card K ^ 2 := by
      calc Nat.card K ^ 4 * Nat.card K ^ 2 = Nat.card K ^ 6 := by ring
        _ ≤ _ := hdiv
    have h4 := Nat.le_of_mul_le_mul_right h6 hq
    omega

theorem field_conj_t_not_mem_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hF : FieldAlternative (yamadaBarK₂ d t) (yamadaT₂ d t) f) :
    ∀ g : G, g⁻¹ * t * g ∉ yamadaP d t := by
  intro g hg
  have htt := h.t_mul_t
  have hx2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨E, hE, hEC, hcard⟩ := h.exists_isElemAbelian_of_mem_yamadaM₆_or_yamadaD₇ hW d hK hQ
    (h.field_involution_mem_yamadaM₆_or_yamadaD₇ hW d hK hQ hsyl hex hF _ hg hx2) hx2
  have hE'C : E.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (hEC hy)
    rw [mem_centralizer_singleton_iff]
    change g * y * g⁻¹ * t = t * (g * y * g⁻¹)
    calc g * y * g⁻¹ * t = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by rw [h1]
      _ = t * (g * y * g⁻¹) := by group
  have hE'a : IsElemAbelian 2 (E.map (MulAut.conj g).toMonoidHom) :=
    SectionRank.isElemAbelian_map hE _
  have hle := (h.card_le_of_isElemAbelian d hK hE'C hE'a)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hle
  have := hle.1.trans (Nat.mul_le_mul_left 2 hle.2)
  omega

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
