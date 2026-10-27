module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem isMaxElemAbelian_conjSubgroup {A : Subgroup G} (hA : IsMaxElemAbelian S A) {σ : G}
    (hσ : σ ∈ normalizer (S : Set G)) : IsMaxElemAbelian S (conjSubgroup A σ) := by
  obtain ⟨hAS, hAe, hmax⟩ := hA
  refine ⟨?_, ?_, fun B hBS hBe => ?_⟩
  · have := C5.conjSubgroup_mono hAS σ
    rwa [C5.conjSubgroup_eq_self hσ] at this
  · exact C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp hAe).conjSubgroup σ)
  · have hB' : conjSubgroup B σ⁻¹ ≤ S := by
      have := C5.conjSubgroup_mono hBS σ⁻¹
      rwa [C5.conjSubgroup_eq_self (inv_mem hσ)] at this
    have hBe' : IsElemAbelian 2 (conjSubgroup B σ⁻¹) :=
      C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp hBe).conjSubgroup σ⁻¹)
    have h1 := hmax _ hB' hBe'
    rw [C5.card_conjSubgroup] at h1
    rw [C5.card_conjSubgroup]
    exact h1

theorem pCoreOf_ne_bot (hcs : ConstrainedSetting G T M H S L) : pCoreOf 2 H ≠ ⊥ := fun h =>
  blockU_ne_bot (isShort hcs) (le_bot_iff.mp (h ▸ blockU_le_pCoreOf_general hcs))

theorem normT_le_of_isMaxElemAbelian (hcs : ConstrainedSetting G T M H S L) {M₀ : Subgroup G}
    (hSM : S ≤ M₀) (hMT : M₀ ≤ T) {x : G} (hx : x ∈ M₀)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian S A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) : normT T S ≤ M₀ := by
  have hHP : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have h244 : ∀ y, y ∈ T → y ∈ normalizer (pCoreOf 2 H : Set G) → y ∈ S := fun y hyT hyN => by
    have e := lemma244 G T M H S L hcs (pCoreOf 2 H) (pCoreOf_ne_bot hcs) (pCoreOf_le_S hcs) hHP
    have : y ∈ T ⊓ normalizer (pCoreOf 2 H : Set G) := ⟨hyT, hyN⟩
    rwa [e] at this
  intro σ hσ
  have hσT : σ ∈ T := hσ.1
  have hσN : σ ∈ normalizer (S : Set G) := hσ.2
  have hP : IsMaxElemAbelian S (pCoreOf 2 H) := (hA _).mpr (Or.inl rfl)
  have hP' := isMaxElemAbelian_conjSubgroup hP hσN
  rcases (hA _).mp hP' with h | h
  · exact hSM (h244 σ hσT (conjSubgroup_eq_iff_mem_normalizer.mp h))
  · rw [conjR_eq] at h
    have h' : conjSubgroup (pCoreOf 2 H) (σ * x⁻¹) = pCoreOf 2 H := by
      rw [← conjSubgroup_conjSubgroup, h, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    have hσx : σ * x⁻¹ ∈ S :=
      h244 _ (mul_mem hσT (inv_mem (hMT hx))) (conjSubgroup_eq_iff_mem_normalizer.mp h')
    have e : σ = (σ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (hSM hσx) hx

theorem normT_eq (hcs : ConstrainedSetting G T M H S L) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian S A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) : normT T S = M₀ :=
  le_antisymm (normT_le_of_isMaxElemAbelian hcs hSM hMT hx hA) fun _ hm =>
    ⟨hMT hm, normalizer_of_relIndex_two hSM h2 hm⟩

omit [Finite G] in
theorem baum_eq_sup_conj {x : G} (hx : x ∈ normalizer (S : Set G))
    (c4 : pCoreOf 2 H = baumD S L ⊔ blockU0 S L)
    (c8 : baum S = baumD S L ⊔ blockU0 S L ⊔ conjR (blockU0 S L) x) :
    baum S = pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x := by
  have hUP : blockU0 S L ≤ pCoreOf 2 H := c4 ▸ le_sup_right
  have hPB : pCoreOf 2 H ≤ baum S := c4 ▸ c8 ▸ le_sup_left
  refine le_antisymm ?_ (sup_le hPB ?_)
  · rw [c8]
    exact sup_le (c4 ▸ le_sup_left) (le_sup_of_le_right (C5.conjSubgroup_mono hUP x))
  · have := C5.conjSubgroup_mono hPB x
    rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S hx)] at this

end C56

end CFSG.QuasithinUnique
