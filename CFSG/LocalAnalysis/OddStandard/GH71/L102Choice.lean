module

public import CFSG.LocalAnalysis.OddStandard.GH71.L103
public import CFSG.LocalAnalysis.OddStandard.GH71.HBarCent

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

@[expose] def Adm102 (z : G) (S P₁ Q V : Subgroup G) : Prop :=
  Q ≠ ⊥ ∧ IsPGroup 3 ↥Q ∧ S ≤ normalizer (Q : Set G) ∧
    Covers (normalizer (Q : Set G)) (Cen z) (pPrimeCoreOf 2 (Cen z)) ∧
    V ≤ normalizer (Q : Set G) ∧ IsPGroup 3 ↥V ∧ S ≤ normalizer (V : Set G) ∧ P₁ ≤ V

theorem exists_adm102_max {z : G} {S P₁ : Subgroup G} (hP₁ : Adm102 z S P₁ P₁ P₁) :
    ∃ Q P, Adm102 z S P₁ Q P ∧
      (∀ Q' V', Adm102 z S P₁ Q' V' → Nat.card V' ≤ Nat.card P) ∧
      (∀ Q' V', Adm102 z S P₁ Q' V' → Nat.card V' = Nat.card P → Nat.card Q' ≤ Nat.card Q) := by
  set 𝓕 : Set (Subgroup G × Subgroup G) := {p | Adm102 z S P₁ p.1 p.2} with h𝓕
  obtain ⟨⟨Q₀, P₀⟩, h₀, hmax₀⟩ :=
    Set.exists_max_image 𝓕 (fun p => Nat.card p.2) (Set.toFinite 𝓕) ⟨(P₁, P₁), hP₁⟩
  set 𝓕' : Set (Subgroup G × Subgroup G) := {p | p ∈ 𝓕 ∧ Nat.card p.2 = Nat.card P₀} with h𝓕'
  obtain ⟨⟨Q, P⟩, ⟨h1, h2⟩, hmax⟩ :=
    Set.exists_max_image 𝓕' (fun p => Nat.card p.1) (Set.toFinite 𝓕') ⟨(Q₀, P₀), h₀, rfl⟩
  refine ⟨Q, P, h1, fun Q' V' hA => ?_, fun Q' V' hA hc => ?_⟩
  · have h2' : Nat.card P = Nat.card P₀ := h2
    rw [h2']
    exact hmax₀ (Q', V') hA
  · exact hmax (Q', V') ⟨hA, hc.trans h2⟩

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem choice_102 (h : Ctx71 G z S U u) (hB1 : SpecB1) (h812 : IVK_8_12_ly)
    {P₁ Q P : Subgroup G} (hP₁ : Open.fusionIsSylowIn 3 P₁ (pPrimeCoreOf 2 (Cen z)))
    (hP₁1 : P₁ ≠ ⊥) (hadm : Adm102 z S P₁ Q P)
    (hmaxP : ∀ Q' V', Adm102 z S P₁ Q' V' → Nat.card V' ≤ Nat.card P)
    (hmaxQ : ∀ Q' V', Adm102 z S P₁ Q' V' → Nat.card V' = Nat.card P → Nat.card Q' ≤ Nat.card Q) :
    normalizer (Q : Set G) ≠ ⊤ ∧
      (IsDoubleCoverOfAlt (HBar (normalizer (Q : Set G))) 11 ∨
        Blueprint.NativeSporadic.IsSporadic (HBar (normalizer (Q : Set G))) .Ly) ∧
      MaxSInv 3 S (normalizer (Q : Set G)) P ∧ P₁ ≤ Q ∧
      P ⊓ pPrimeCoreOf 2 (normalizer (Q : Set G)) = Q := by
  obtain ⟨hQ1, hQ3, hSQ, hQcov, hPN, hP3, hSP, hP₁P⟩ := hadm
  set H := normalizer (Q : Set G) with hHdef
  have hH : H ≠ ⊤ := h.normalizer_ne_top hQ3 hQ1
  have hSH : S ≤ H := hSQ
  have hbar := h.hbar_of_covers hB1 h812 hH hSH hQcov
  have hP : MaxSInv 3 S H P := ⟨hPN, hP3, hSP, fun W hWH hW3 hSW hPW =>
    (eq_of_le_of_card_ge hPW
      (hmaxP Q W ⟨hQ1, hQ3, hSQ, hQcov, hWH, hW3, hSW, hP₁P.trans hPW⟩)).symm⟩
  have hP₁O : P₁ ≤ pPrimeCoreOf 2 H :=
    (le_inf hP₁.1 (hP₁P.trans hPN)).trans (h.inf_pPrimeCoreOf_le hSH hbar)
  have hcard := L127.inf_sylow_of_maximal hSH h.S2 hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  have hRsyl : Open.fusionIsSylowIn 3 (P ⊓ pPrimeCoreOf 2 H) (pPrimeCoreOf 2 H) :=
    L121.fusionIsSylowIn_of_card inf_le_right hP3.to_inf_left hcard
  have hQO : Q ≤ pPrimeCoreOf 2 H :=
    le_pPrimeCoreOf_of_odd le_normalizer (odd_card_of_isPGroup_three hQ3) le_rfl
  have hQR : Q ≤ P ⊓ pPrimeCoreOf 2 H := by
    have h3 : IsPGroup 3 ↥(P ⊓ pPrimeCoreOf 2 H ⊔ Q) :=
      IsPGroup.to_sup_of_normal_right' hRsyl.2.1 hQ3 (inf_le_left.trans hPN)
    have := hRsyl.2.2 _ (sup_le inf_le_right hQO) h3 le_sup_left
    exact le_sup_right.trans this.le
  have hSR : S ≤ normalizer ((P ⊓ pPrimeCoreOf 2 H : Subgroup G) : Set G) := fun s hs =>
    inf_normalizer_le_normalizer_inf ⟨hSP hs, le_normalizer_pPrimeCoreOf' H (hSH hs)⟩
  have hPR : P ≤ normalizer ((P ⊓ pPrimeCoreOf 2 H : Subgroup G) : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hx, le_normalizer_pPrimeCoreOf' H (hPN hx)⟩
  have hcovR : Covers (normalizer ((P ⊓ pPrimeCoreOf 2 H : Subgroup G) : Set G)) H
      (pPrimeCoreOf 2 H) :=
    covers_frattini Nat.prime_three (pPrimeCoreOf_le' H) (le_normalizer_pPrimeCoreOf' H)
      (odd_card_pPrimeCoreOf' H) hRsyl
  have hz2 : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_z, pow_one])
  have hNz := normalizer_zpowers_eq_centralizer h.orderOf_z
  have hcovRM : Covers (normalizer ((P ⊓ pPrimeCoreOf 2 H : Subgroup G) : Set G)) (Cen z)
      (pPrimeCoreOf 2 (Cen z)) := by
    have := covers_transfer hz2 (zpowers_le.mpr (hSH h.ctx.z_mem))
      (zpowers_le.mpr (hSR h.ctx.z_mem)) (by rw [hNz]; exact hQcov) hcovR
    rwa [hNz] at this
  have hP₁R : P₁ ≤ P ⊓ pPrimeCoreOf 2 H := le_inf hP₁P hP₁O
  have hR1 : P ⊓ pPrimeCoreOf 2 H ≠ ⊥ := fun hb => hP₁1 (le_bot_iff.mp (hb ▸ hP₁R))
  have hRadm : Adm102 z S P₁ (P ⊓ pPrimeCoreOf 2 H) P :=
    ⟨hR1, hP3.to_inf_left, hSR, hcovRM, hPR, hP3, hSP, hP₁P⟩
  have hRQ : P ⊓ pPrimeCoreOf 2 H = Q := (eq_of_le_of_card_ge hQR (hmaxQ _ _ hRadm rfl)).symm
  exact ⟨hH, hbar, hP, hRQ ▸ hP₁R, hRQ⟩

end Ctx71

end CFSG.OddStandard.GH71
