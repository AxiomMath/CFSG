module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2EndN3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace EndN

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x : G} {q : ℕ} {W D₁ D₂ : Subgroup G}

namespace Data

variable (E : Data T M H S L D n t M₀ x q W D₁ D₂)
include E

theorem false_main
    : False := by
  set R : Subgroup G := thompsonJ S with hR
  set R₁ : Subgroup G := R ⊓ L with hR₁
  set U₂ : Subgroup G := blockU (conjR L t) with hU₂
  set P : Subgroup G := T ⊓ Subgroup.normalizer (R : Set G) with hP
  set T₁ : Subgroup G := P ⊓ Subgroup.normalizer (R₁ : Set G) with hT₁def
  set S₂ : Subgroup G := T₁ ⊓ Subgroup.normalizer (U₂ : Set G) with hS₂def
  have hidx₁ : T₁.relIndex P ≤ 2 := E.relIndex_T₁_le
  have hidx₂ : S₂.relIndex T₁ ≤ 2 := E.relIndex_S₂_le
  have h1 : Nat.card P ≤ 2 * Nat.card T₁ := by
    have h := Subgroup.relIndex_mul_card (H := T₁) (K := P)
    rw [inf_eq_left.2 (inf_le_left : T₁ ≤ P)] at h
    calc Nat.card P = T₁.relIndex P * Nat.card T₁ := h.symm
      _ ≤ 2 * Nat.card T₁ := Nat.mul_le_mul_right _ hidx₁
  have h2 : Nat.card T₁ ≤ 2 * Nat.card S₂ := by
    have h := Subgroup.relIndex_mul_card (H := S₂) (K := T₁)
    rw [inf_eq_left.2 (inf_le_left : S₂ ≤ T₁)] at h
    calc Nat.card T₁ = S₂.relIndex T₁ * Nat.card S₂ := h.symm
      _ ≤ 2 * Nat.card S₂ := Nat.mul_le_mul_right _ hidx₂
  have hcard : Nat.card S ≤ Nat.card S₂ := by
    have h4 : 4 * Nat.card S ≤ Nat.card P := E.four_mul_card_le
    omega
  have hS₂T : S₂ ≤ T := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hS₂R₁ : S₂ ≤ Subgroup.normalizer (R₁ : Set G) := inf_le_left.trans inf_le_right
  have hS₂U₂ : S₂ ≤ Subgroup.normalizer (U₂ : Set G) := inf_le_right
  have hR1 : AppE.R1 S L ≤ S₂ := by
    intro g hg
    have hgS : g ∈ S := AppE.R1_le_S hg
    have hgL : conjR L g = L := (AppE.mem_R1_iff.1 hg).2
    have hgR : conjR (thompsonJ S) g = thompsonJ S :=
      thompsonJ_normalized (Subgroup.le_normalizer hgS)
    refine ⟨⟨⟨E.B.S_le_T hgS, conjR_eq_self_iff.1 hgR⟩, conjR_eq_self_iff.1 ?_⟩,
      E.normalizer_L₂_le_U₂ (E.B.dbl.R1_le_normalizer_L₂ hg)⟩
    rw [hR₁, hR, conjR_inf, hgR, hgL]
  have hSyl : IsSylowTwoOf S₂ (Subgroup.normalizer (R₁ : Set G)) :=
    E.isSylowTwoOf_normalizer_R₁ hS₂T hS₂R₁ hS₂U₂ hR1 hcard
  have hT₁eq : T₁ = S₂ :=
    hSyl.eq_of_le (inf_le_left : S₂ ≤ T₁) (inf_le_right : T₁ ≤ Subgroup.normalizer (R₁ : Set G))
      (E.B.T_isPGroup.to_le (inf_le_left.trans inf_le_left))
  have hxT₁ : x ∈ T₁ :=
    ⟨⟨E.B.hMT E.B.hx₀, E.x_normalizer_R⟩,
      conjR_eq_self_iff.1 (E.B.conjR_R₁ E.hT₁ E.hT₂ E.hD E.hC E.hDx)⟩
  have hxS₂ : x ∈ S₂ := hT₁eq ▸ hxT₁
  exact E.U₂_ne_conj (conjR_eq_self_iff.2 hxS₂.2).symm

end Data

end EndN

theorem S2Base.false_of_lt_normT
    {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
    {t : G} {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
    (B : S2Base T M H S L D n t M₀ x q W) (h246 : Lemma246Double) {D₁ D₂ : Subgroup G}
    (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x = D) (hRJ : thompsonJ M₀ = thompsonJ S)
    (hA4 : Set.ncard {A : Subgroup G | IsMaxElemAbelian (thompsonJ S) A} = 4)
    (hlt : ¬ (T ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ M₀)) : False :=
  EndN.Data.false_main ⟨B, h246, hT₁, hT₂, hD, hC, hDx, hRJ, hA4, hlt⟩

end CFSG.QuasithinUnique.Lin2
