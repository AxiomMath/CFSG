module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowFixed

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_sup_iff_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          have := h a' ha' b hb
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [this.symm]
            _ = a * a' * (b * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          have := h a ha b hb
          calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
            _ = a⁻¹ * b⁻¹ := by group }
    have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem SocleLE.of_le [Finite G] {L V V' : Subgroup G} (hV' : V' ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLV' : L ≤ Subgroup.normalizer (V' : Set G))
    {n : ℕ} (h : SocleLE L V n) : SocleLE L V' n := by
  unfold SocleLE at h ⊢
  set C : Subgroup G := Subgroup.centralizer (L : Set G)
  have hA' : ⁅V', L⁆ ⊔ (V' ⊓ C) ≤ V' :=
    sup_le (commutator_le_of_le_normalizer hLV') inf_le_left
  have hA : ⁅V, L⁆ ⊔ (V ⊓ C) ≤ V :=
    sup_le (commutator_le_of_le_normalizer hLV) inf_le_left
  have hle : ⁅V', L⁆ ⊔ (V' ⊓ C) ≤ ⁅V, L⁆ ⊔ (V ⊓ C) :=
    sup_le_sup (Subgroup.commutator_mono hV' le_rfl) (inf_le_inf_right _ hV')
  have e1 : (V' ⊓ C).relIndex (⁅V', L⁆ ⊔ (V' ⊓ C)) = C.relIndex (⁅V', L⁆ ⊔ (V' ⊓ C)) := by
    rw [← Subgroup.inf_relIndex_right (V' ⊓ C), ← Subgroup.inf_relIndex_right C]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hx⟩; exact ⟨hc, hx⟩
    · rintro ⟨hc, hx⟩; exact ⟨⟨hA' hx, hc⟩, hx⟩
  have e2 : (V ⊓ C).relIndex (⁅V, L⁆ ⊔ (V ⊓ C)) = C.relIndex (⁅V, L⁆ ⊔ (V ⊓ C)) := by
    rw [← Subgroup.inf_relIndex_right (V ⊓ C), ← Subgroup.inf_relIndex_right C]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hx⟩; exact ⟨hc, hx⟩
    · rintro ⟨hc, hx⟩; exact ⟨⟨hA hx, hc⟩, hx⟩
  rw [e1]
  rw [e2] at h
  refine le_trans (Subgroup.relIndex_le_of_le_right hle ?_) h
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem HasIrreducibleCommutatorQuotient.of_le {L V V' : Subgroup G} (hV' : V' ≤ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (h : HasIrreducibleCommutatorQuotient L V)
    (hne : ⁅V', L⁆ ⊓ Subgroup.centralizer (L : Set G) < ⁅V', L⁆) :
    HasIrreducibleCommutatorQuotient L V' := by
  refine ⟨hne, ?_⟩
  intro W hW1 hW2 hWL
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hC
  set U : Subgroup G := ⁅V, L⁆ with hU
  set U' : Subgroup G := ⁅V', L⁆ with hU'
  have hU'U : U' ≤ U := Subgroup.commutator_mono hV' le_rfl
  have hUV : U ≤ V := commutator_le_of_le_normalizer hLV
  have hcomm : ∀ a ∈ W, ∀ b ∈ U ⊓ C, a * b = b * a := fun a ha b hb =>
    hVc a (hUV (hU'U (hW2 ha))) b (hUV hb.1)
  set W' : Subgroup G := W ⊔ (U ⊓ C) with hW'
  have hW'U : W' ≤ U := sup_le (hW2.trans hU'U) inf_le_left
  have hLW' : L ≤ Subgroup.normalizer (W' : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun ℓ hℓ y hy => ?_
    have hy' : y ∈ W ⊔ (U ⊓ C) := hy
    obtain ⟨w, hw, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hy'
    have e : ℓ * (w * c) * ℓ⁻¹ = (ℓ * w * ℓ⁻¹) * c := by
      have hcc : ℓ * c = c * ℓ := Subgroup.mem_centralizer_iff.mp hc.2 ℓ hℓ
      have hc' : c * ℓ⁻¹ = ℓ⁻¹ * c := by
        calc c * ℓ⁻¹ = ℓ⁻¹ * (ℓ * c) * ℓ⁻¹ := by group
          _ = ℓ⁻¹ * (c * ℓ) * ℓ⁻¹ := by rw [hcc]
          _ = ℓ⁻¹ * c := by group
      calc ℓ * (w * c) * ℓ⁻¹ = ℓ * w * (c * ℓ⁻¹) := by group
        _ = ℓ * w * (ℓ⁻¹ * c) := by rw [hc']
        _ = (ℓ * w * ℓ⁻¹) * c := by group
    rw [e]
    exact W'.mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hWL hℓ) w).mp hw))
      (Subgroup.mem_sup_right hc)
  rcases h.2 W' le_sup_right hW'U hLW' with h1 | h2
  · left
    refine le_antisymm (fun x hx => ?_) hW1
    have hx' : x ∈ U ⊓ C := by
      rw [← h1]
      exact Subgroup.mem_sup_left hx
    exact ⟨hW2 hx, hx'.2⟩
  · right
    refine le_antisymm hW2 fun u hu => ?_
    have hu' : u ∈ W ⊔ (U ⊓ C) := by
      have h3 : u ∈ (⁅V, L⁆ : Subgroup G) := hU'U hu
      rw [← h2] at h3
      exact h3
    obtain ⟨w, hw, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hu'
    have hcU' : c ∈ U' := by
      have : c = w⁻¹ * (w * c) := by group
      rw [this]
      exact U'.mul_mem (U'.inv_mem (hW2 hw)) hu
    have hcW : c ∈ W := hW1 ⟨hcU', hc.2⟩
    exact W.mul_mem hw hcW

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
