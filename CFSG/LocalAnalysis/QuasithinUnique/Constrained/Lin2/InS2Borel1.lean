module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Syl

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem mem_normalizer_of_conj_mem {X : Subgroup G} {a : G} (h : ∀ y ∈ X, a * y * a⁻¹ ∈ X) :
    a ∈ Subgroup.normalizer (X : Set G) := by
  have hle : conjR X a⁻¹ ≤ X := fun y hy => by
    have h1 := h _ (mem_conjR.1 hy)
    have e : a * (a⁻¹ * y * a⁻¹⁻¹) * a⁻¹ = y := by group
    rwa [e] at h1
  have heq : conjR X a⁻¹ = X := eq_of_le_of_card_le' hle (by rw [card_conjR])
  have := conjR_eq_self_iff.1 heq
  simpa using Subgroup.inv_mem _ this

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem coord₁ : ∃ (F : Type) (_ : Field F) (_ : Fintype F),
    Nonempty (Adapted L (thompsonJ S ⊓ L) n F) :=
  exists_adapted (by have := B.hn; omega) B.hlin B.isSylowTwoOf_R₁

theorem coord₂ : ∃ (F : Type) (_ : Field F) (_ : Fintype F),
    Nonempty (Adapted (conjR L t) (thompsonJ S ⊓ conjR L t) n F) :=
  exists_adapted (by have := B.hn; omega) B.hlin₂ B.isSylowTwoOf_R₂

theorem R_isPGroup : IsPGroup 2 (thompsonJ S) :=
  B.cs.sylow.isPGroup.to_le (thompsonJ_le_self S)

theorem P_inf_L : (S ⊓ conjJoin S L) ⊓ L = thompsonJ S ⊓ L := by
  rw [B.S_inf_L₀_eq]
  exact sup_inf_left_of_commute (X := L) (Y := conjR L t) B.comm_elem B.L_inf_L₂ inf_le_right
    inf_le_right

theorem P_inf_L₂ : (S ⊓ conjJoin S L) ⊓ conjR L t = thompsonJ S ⊓ conjR L t := by
  rw [B.S_inf_L₀_eq]
  exact sup_inf_right_of_commute (X := L) (Y := conjR L t) B.comm_elem B.L_inf_L₂ inf_le_right
    inf_le_right

theorem R₁_le_P : thompsonJ S ⊓ L ≤ S ⊓ conjJoin S L := by
  rw [B.S_inf_L₀_eq]; exact le_sup_left

theorem R₂_le_P : thompsonJ S ⊓ conjR L t ≤ S ⊓ conjJoin S L := by
  rw [B.S_inf_L₀_eq]; exact le_sup_right

theorem N_P_decomp {k : G}
    (hk : k ∈ conjJoin S L ⊓ Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) :
    ∃ a ∈ L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G),
      ∃ b ∈ conjR L t ⊓ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G),
        k = a * b := by
  have hk1 : k ∈ L ⊔ conjR L t := B.hjoin ▸ hk.1
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer B.L₂_le_normalizer_L).1 hk1
  refine ⟨a, ⟨ha, ?_⟩, b, ⟨hb, ?_⟩, rfl⟩
  · refine mem_normalizer_of_conj_mem fun y hy => ?_
    have h1 : a * b * y * (a * b)⁻¹ = a * y * a⁻¹ := by
      have hc : b * y = y * b := (B.comm_elem y hy.2 b hb).symm
      calc a * b * y * (a * b)⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ := by group
        _ = a * (y * b) * b⁻¹ * a⁻¹ := by rw [hc]
        _ = a * y * a⁻¹ := by group
    have h2 : a * b * y * (a * b)⁻¹ ∈ S ⊓ conjJoin S L :=
      (Subgroup.mem_normalizer_iff.1 hk.2 y).1 (B.R₁_le_P hy)
    rw [h1] at h2
    have h3 : a * y * a⁻¹ ∈ L := L.mul_mem (L.mul_mem ha hy.2) (L.inv_mem ha)
    have := B.P_inf_L ▸ (show a * y * a⁻¹ ∈ (S ⊓ conjJoin S L) ⊓ L from ⟨h2, h3⟩)
    exact this
  · refine mem_normalizer_of_conj_mem fun y hy => ?_
    have h1 : a * b * y * (a * b)⁻¹ = b * y * b⁻¹ := by
      have hc : a * y = y * a := B.comm_elem a ha y hy.2
      calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = a * (b * y * b⁻¹) * a⁻¹ := rfl
        _ = b * y * b⁻¹ := by
          have hc' : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a :=
            B.comm_elem a ha _ (mul_mem (mul_mem hb hy.2) (inv_mem hb))
          rw [hc']; group
    have h2 : a * b * y * (a * b)⁻¹ ∈ S ⊓ conjJoin S L :=
      (Subgroup.mem_normalizer_iff.1 hk.2 y).1 (B.R₂_le_P hy)
    rw [h1] at h2
    have h3 : b * y * b⁻¹ ∈ conjR L t :=
      (conjR L t).mul_mem ((conjR L t).mul_mem hb hy.2) ((conjR L t).inv_mem hb)
    have := B.P_inf_L₂ ▸ (show b * y * b⁻¹ ∈ (S ⊓ conjJoin S L) ⊓ conjR L t from ⟨h2, h3⟩)
    exact this

end S2Base

end CFSG.QuasithinUnique.Lin2
