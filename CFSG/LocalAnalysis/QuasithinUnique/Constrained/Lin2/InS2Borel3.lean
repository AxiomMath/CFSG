module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Torus

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem R₁_le_normalizer_R₂ :
    thompsonJ S ⊓ L ≤ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb.2 a ha.2).symm

theorem R₁_inf_R₂ : (thompsonJ S ⊓ L) ⊓ (thompsonJ S ⊓ conjR L t) = ⊥ := by
  rw [eq_bot_iff, ← B.L_inf_L₂]
  exact inf_le_inf inf_le_right inf_le_right

theorem P_isPGroup : IsPGroup 2 ↥(S ⊓ conjJoin S L) := B.isSylowTwoOf_S_inf_L₀.isPGroup

theorem card_P : Nat.card ↥(S ⊓ conjJoin S L) =
    Nat.card ↥(thompsonJ S ⊓ L) * Nat.card ↥(thompsonJ S ⊓ conjR L t) := by
  have h := card_sup_mul_card_inf B.R₁_le_normalizer_R₂
  rw [B.R₁_inf_R₂, Subgroup.card_bot, mul_one] at h
  rw [B.S_inf_L₀_eq, h]

theorem L_le_normalizer_R₂ :
    L ≤ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb a ha.2).symm

theorem L₂_le_normalizer_R₁ :
    conjR L t ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => B.comm_elem a ha.2 b hb

theorem B₁_le_F : L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) ≤
    conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) := by
  intro a ha
  refine ⟨B.hjoin ▸ Subgroup.mem_sup_left ha.1, ?_⟩
  have h1 : a ∈ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := ha.2
  have h2 : a ∈ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
    B.L_le_normalizer_R₂ ha.1
  have h3 : a ∈ Subgroup.normalizer
      ((thompsonJ S ⊓ L ⊔ thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := by
    rw [← conjR_eq_self_iff, conjR_sup, conjR_eq_of_mem_normalizer h1,
      conjR_eq_of_mem_normalizer h2]
  rw [B.S_inf_L₀_eq]
  exact h3

theorem B₂_le_F : conjR L t ⊓ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) ≤
    conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) := by
  intro a ha
  refine ⟨B.hjoin ▸ Subgroup.mem_sup_right ha.1, ?_⟩
  have h1 : a ∈ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := ha.2
  have h2 : a ∈ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
    B.L₂_le_normalizer_R₁ ha.1
  have h3 : a ∈ Subgroup.normalizer
      ((thompsonJ S ⊓ L ⊔ thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := by
    rw [← conjR_eq_self_iff, conjR_sup, conjR_eq_of_mem_normalizer h2,
      conjR_eq_of_mem_normalizer h1]
  rw [B.S_inf_L₀_eq]
  exact h3

theorem B₁_inf_B₂ : (L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) ⊓
    (conjR L t ⊓ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G)) = ⊥ := by
  rw [eq_bot_iff, ← B.L_inf_L₂]
  exact inf_le_inf inf_le_left inf_le_left

theorem B₁_le_normalizer_B₂ :
    L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((conjR L t ⊓ Subgroup.normalizer
        ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb.1 a ha.1).symm

theorem F_eq_sup : conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) =
    (L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)) ⊔
      (conjR L t ⊓ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G)) := by
  apply le_antisymm
  · intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := B.N_P_decomp hk
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  · exact sup_le B.B₁_le_F B.B₂_le_F

theorem card_F : Nat.card ↥(conjJoin S L ⊓
    Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) =
    Nat.card ↥(S ⊓ conjJoin S L) * (2 ^ n - 1) ^ 2 := by
  obtain ⟨F₁, _, _, ⟨A₁⟩⟩ := B.coord₁
  obtain ⟨F₂, _, _, ⟨A₂⟩⟩ := B.coord₂
  have h := card_sup_mul_card_inf B.B₁_le_normalizer_B₂
  rw [B.B₁_inf_B₂, Subgroup.card_bot, mul_one] at h
  rw [B.F_eq_sup, h, A₁.card_borel, A₂.card_borel, B.card_P]
  ring

end S2Base

end CFSG.QuasithinUnique.Lin2
