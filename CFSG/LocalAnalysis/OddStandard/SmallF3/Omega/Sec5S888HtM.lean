module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem heart_dict_of_blocks {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} {z : G} {A₁ A₂ : Subgroup G}
    (hd : HeartData φ A M Alt) (hM : M ≤ normalizer (A : Set G))
    (hAlt : Alt = alternatingGroup (Fin 8) ∨ Alt = ⊤)
    (hAlt' : alternatingGroup (Fin 8) ≤ Alt) (hz : z = φ heartZVec)
    (h : ((A₁ : Set G) = φ '' {v | IsFirstBlockVec v} ∧
        (A₂ : Set G) = φ '' {v | IsSecondBlockVec v}) ∨
      ((A₁ : Set G) = φ '' {v | IsSecondBlockVec v} ∧
        (A₂ : Set G) = φ '' {v | IsFirstBlockVec v})) :
    ∃ (Alt' : Subgroup (Equiv.Perm (Fin 8))) (φ' : (Fin 8 → ZMod 2) → G),
      (Alt' = alternatingGroup (Fin 8) ∨ Alt' = ⊤) ∧
      IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ' A ⊥ M Alt' ∧
      z = φ' heartZVec ∧
      (∀ x : G, x ∈ A₁ ↔ ∃ v, IsFirstBlockVec v ∧ φ' v = x) ∧
      (∀ x : G, x ∈ A₂ ↔ ∃ v, IsSecondBlockVec v ∧ φ' v = x) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨Alt, φ, hAlt, hd.toPermModuleMod hM, hz, fun x => Set.ext_iff.mp h₁ x,
      fun x => Set.ext_iff.mp h₂ x⟩
  · have hd' := hd.relabel (hAlt' heartSwap_mem_alternatingGroup)
    refine ⟨Alt, fun v => φ (permVec heartSwap v), hAlt, hd'.toPermModuleMod hM, ?_,
      fun x => ?_, fun x => ?_⟩
    · show z = φ (permVec heartSwap heartZVec)
      rw [permVec_heartSwap_zVec, hd.add_one _ isEvenVec_heartZVec, ← hz]
    · rw [← heart_image_swap_firstBlock φ] at h₁
      exact Set.ext_iff.mp h₁ x
    · rw [← heart_image_swap_secondBlock φ] at h₂
      exact Set.ext_iff.mp h₂ x

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem asc82HeartDict_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (h510 : Asc82Lemma510) (fact : Asc82Fact512H)
    (f7 : Asc82Fact512M8) : Asc82HeartDict := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  have hR : Sec5RCtx G t L S z r B A := c.toSec5RCtx
  have hC : Sec5Ctx G t L S z := hR.toSec5Ctx
  have hΩ : IsOm6Z2 L := hC.toSec5Setting.isOm6Z2
  have h2 : Case59Two t z A := h510 G t L S z r B A hR
  obtain ⟨hcard, htA⟩ := sec5b_card_t_mem hR
  have hzA : z ∈ A := sec5b_z_mem_A hcard h2
  obtain ⟨c1, c2, c3, Alt, hAlt, φ₀, hφ₀⟩ := id h2
  have hd₀ := sec5b_heartData hφ₀
  have hAlt' : alternatingGroup (Fin 8) ≤ Alt := by
    rcases hAlt with rfl | rfl
    · exact le_rfl
    · exact le_top
  have hcard28 : Set.ncard (conjClassIn (normalizer (A : Set G)) t) = 28 := by
    rw [← c2]
    exact c3
  have hzt : z ∉ conjClassIn (normalizer (A : Set G)) t := by
    intro hz
    rw [← c2, c1] at hz
    exact hz.2 ⟨1, (normalizer (A : Set G)).one_mem, by simp⟩
  obtain ⟨w₀, -, hw₀z, hw₀4⟩ :=
    heart_z_weight_four hAlt' hd₀ htA hzA c.t_ne_one c.z_ne_one hcard28 hzt
  obtain ⟨σ, hσA, hσ⟩ := sec5b_exists_alt (v := heartZVec) (w := w₀)
    (by rw [vecWeight_heartZVec, hw₀4])
  obtain ⟨φ₁, hd₁, hz₁⟩ : ∃ φ₁ : (Fin 8 → ZMod 2) → G,
      HeartData φ₁ A (normalizer (A : Set G)) Alt ∧ φ₁ heartZVec = z :=
    ⟨fun v => φ₀ (permVec σ v), hd₀.relabel (hAlt' hσA), by
      show φ₀ (permVec σ heartZVec) = z
      rw [hσ, hw₀z]⟩
  have hcls := heart_class_pair hAlt' hd₁ htA c.t_ne_one hcard28
  have hA₁z : φ₁ heartZVec ∈ A ⊓ (K₁ ⊔ K₂) := by
    rw [hz₁]
    exact ⟨hzA, Subgroup.mem_sup_left c.z_mem_K₁⟩
  have hA₁t : ∀ x ∈ A ⊓ (K₁ ⊔ K₂), x ≠ 1 → x ≠ φ₁ heartZVec →
      x ∈ conjClassIn (normalizer (A : Set G)) t := by
    intro x hx hx1 hxz
    rw [hz₁] at hxz
    exact heart_A₁_class h36 h37 h52b h53 tab fact c h2 hx.1 hx.2 hx1 hxz
  have h8 : 8 ≤ Nat.card ↥(A ⊓ (K₁ ⊔ K₂)) := by
    have h7 := f7 G L hΩ t hC.involution c.centre r (sec5b_orderOf_r hR) hR.type_r B hR.B_le
      hR.B_E32 hR.B_split.1 hR.B_split.2.1 hR.B_split.2.2 z hR.pocket (c.A_eq ▸ hzA)
    rw [← c.prod, ← c.A_eq] at h7
    exact h7
  have hblk₁ := heart_block_cases hd₁ hcls inf_le_left hA₁z hA₁t h8
  have hA₂z : φ₁ heartZVec ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) := by
    rw [hz₁]
    exact ⟨hzA, Subgroup.mem_sup_left c.z_mem_K₃⟩
  have hA₂t : ∀ x ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h), x ≠ 1 → x ≠ φ₁ heartZVec →
      x ∈ conjClassIn (normalizer (A : Set G)) t := by
    intro x hx hx1 hxz
    rw [hz₁] at hxz
    exact heart_A₂_class h36 h37 h52b h53 tab fact c h2 hx.1 hx.2 hx1 hxz
  have hblk₂ := heart_block_cases hd₁ hcls inf_le_left hA₂z hA₂t (heart_card_A₂ c h8)
  have htA₂ : t ∈ A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) := ⟨htA, c.t_mem_sup₃₄⟩
  have htA₁ : t ∉ A ⊓ (K₁ ⊔ K₂) := fun hh => heart_t_not_mem_sup h37 fact c hh.2
  refine heart_dict_of_blocks hd₁ le_rfl hAlt hAlt' hz₁.symm ?_
  rcases hblk₁ with h₁ | h₁
  · rcases hblk₂ with h₂ | h₂
    · exfalso
      have ht : t ∈ ((A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) : Subgroup G) : Set G) :=
        htA₂
      rw [h₂, ← h₁] at ht
      exact htA₁ ht
    · exact Or.inl ⟨h₁, h₂⟩
  · rcases hblk₂ with h₂ | h₂
    · exact Or.inr ⟨h₁, h₂⟩
    · exfalso
      have ht : t ∈ ((A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) : Subgroup G) : Set G) :=
        htA₂
      rw [h₂, ← h₁] at ht
      exact htA₁ ht

end Ctx

end CFSG.OddStandard.SmallF3.Omega
