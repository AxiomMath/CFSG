module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AS76b (oddCoreIn NormalIn)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure conjugateSubgroup)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem toBar_mem_bar_iff {K Y : Subgroup G} (hY : Y ≤ normalizer (K : Set G))
    (x : normalizer (K : Set G)) : toBar K x ∈ bar K Y ↔ (x : G) ∈ Y ⊔ oddCoreIn K := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (mem_bar_iff K Y _).mp hx
    have hmem : (y : G)⁻¹ * x ∈ oddCoreIn K := by
      have h1 : y⁻¹ * x ∈ coreIn K := QuotientGroup.eq.mp hyx
      exact h1
    have h2 := mul_mem (mem_sup_left hy : (y : G) ∈ Y ⊔ oddCoreIn K) (mem_sup_right hmem)
    simpa using h2
  · intro hx
    rw [← bar_sup_core hY]
    exact toBar_mem_bar K hx

@[expose] def weakClosure (K T S : Subgroup G) : Subgroup G :=
  ⨆ (k : G) (_ : k ∈ K) (_ : rightConjugate T k ≤ S), rightConjugate T k

omit [Finite G] in
theorem weakClosure_le (K T S : Subgroup G) : weakClosure K T S ≤ S :=
  iSup₂_le fun _ _ => iSup_le fun h => h

theorem bar_weakClosure {K T S : Subgroup G} (hSN : S ≤ normalizer (K : Set G))
    (hTN : T ≤ normalizer (K : Set G)) (hT2 : IsPGroup 2 T) :
    bar K (weakClosure K T S) = relativeWeakClosure (bar K K) (bar K T) (bar K S) := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  apply le_antisymm
  ·
    have hle : weakClosure K T S ≤
        ((relativeWeakClosure (bar K K) (bar K T) (bar K S)).comap (toBar K)).map
          (normalizer (K : Set G)).subtype := by
      refine iSup₂_le fun k hk => iSup_le fun hkS => ?_
      intro x hx
      have hxN : x ∈ normalizer (K : Set G) := hSN (hkS hx)
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      let k' : normalizer (K : Set G) := ⟨k, hKN hk⟩
      have h1 : toBar K ⟨x, hxN⟩ ∈ bar K (rightConjugate T k') := toBar_mem_bar K hx
      rw [bar_rightConjugate T k'] at h1
      have hterm : conjugateSubgroup (toBar K k')⁻¹ (bar K T) ≤ bar K S := by
        change rightConjugate (bar K T) (toBar K k') ≤ bar K S
        rw [← bar_rightConjugate T k']
        exact bar_mono K hkS
      have hmem : conjugateSubgroup (toBar K k')⁻¹ (bar K T) ≤
          relativeWeakClosure (bar K K) (bar K T) (bar K S) :=
        le_iSup_of_le (⟨(toBar K k')⁻¹, inv_mem (toBar_mem_bar K hk)⟩ : bar K K)
          (le_iSup_of_le hterm le_rfl)
      exact hmem h1
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_bar_iff K _ z).mp hz
    obtain ⟨y, hy, hyw⟩ := hle hw
    have hyw' : y = w := Subtype.ext hyw
    rw [← hyw']
    exact hy
  ·
    refine iSup_le fun c => iSup_le fun hc => ?_
    obtain ⟨c', hc'K, hc'c⟩ := (mem_bar_iff K K c.1).mp c.2
    set y : normalizer (K : Set G) := c'⁻¹ with hydef
    have hyK : (y : G) ∈ K := inv_mem hc'K
    have hbarc : conjugateSubgroup c.1 (bar K T) = bar K (rightConjugate T y) := by
      rw [bar_rightConjugate T y, hydef, map_inv, hc'c]
      simp only [rightConjugate, inv_inv, conjugateSubgroup]
    have hTyN : rightConjugate T y ≤ normalizer (K : Set G) := rightConjugate_le_normalizer hTN y
    have hTy2 : IsPGroup 2 (rightConjugate T y) := hT2.map _
    have hTyS : rightConjugate T y ≤ S ⊔ oddCoreIn K := by
      intro x hx
      have hxN := hTyN hx
      have h1 : toBar K ⟨x, hxN⟩ ∈ bar K S := by
        have h2 : toBar K ⟨x, hxN⟩ ∈ bar K (rightConjugate T y) := toBar_mem_bar K hx
        rw [← hbarc] at h2
        exact hc h2
      exact (toBar_mem_bar_iff hSN ⟨x, hxN⟩).mp h1
    obtain ⟨o, ho, hle⟩ := le_rightConjugate_of_le_sup_core hSN hTy2 hTyS
    have hoN : o ∈ normalizer (K : Set G) := hKN (core_le K ho)
    set k' : normalizer (K : Set G) := y * (⟨o, hoN⟩ : normalizer (K : Set G))⁻¹ with hk'def
    have hk'K : (k' : G) ∈ K := mul_mem hyK (inv_mem (core_le K ho))
    have hk'S : rightConjugate T k' ≤ S := by
      have h1 : rightConjugate T k' = rightConjugate (rightConjugate T y) o⁻¹ := by
        rw [rightConjugate_mul]
        rfl
      rw [h1]
      calc rightConjugate (rightConjugate T y) o⁻¹ ≤ rightConjugate (rightConjugate S o) o⁻¹ :=
            Subgroup.map_mono hle
        _ = S := by rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hbark : bar K (rightConjugate T k') = conjugateSubgroup c.1 (bar K T) := by
      rw [hbarc, bar_rightConjugate T k', bar_rightConjugate T y, hk'def, map_mul,
        map_inv (toBar K) (⟨o, hoN⟩ : normalizer (K : Set G)),
        (toBar_eq_one_iff K ⟨o, hoN⟩).mpr ho, inv_one, mul_one]
    rw [← hbark]
    exact bar_mono K (le_iSup₂_of_le (k' : G) hk'K (le_iSup_of_le hk'S le_rfl))

omit [Finite G] in
theorem normalIn_of_le_normalizer {K T W : Subgroup G} (hTN : T ≤ normalizer (K : Set G))
    (hW : W ≤ K ⊔ T) (h : bar K K ⊔ bar K T ≤ normalizer (bar K W : Set (Bar K))) :
    NormalIn (W ⊔ oddCoreIn K) (K ⊔ T) := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hKTN : K ⊔ T ≤ normalizer (K : Set G) := sup_le hKN hTN
  have hWN : W ≤ normalizer (K : Set G) := hW.trans hKTN
  have hle : W ⊔ oddCoreIn K ≤ K ⊔ T := sup_le hW ((core_le K).trans le_sup_left)
  have hconj : ∀ g ∈ K ⊔ T, ∀ x ∈ W ⊔ oddCoreIn K, g * x * g⁻¹ ∈ W ⊔ oddCoreIn K := by
    intro g hg x hx
    let g' : normalizer (K : Set G) := ⟨g, hKTN hg⟩
    let x' : normalizer (K : Set G) := ⟨x, hKTN (hle hx)⟩
    have hx' : toBar K x' ∈ bar K W := (toBar_mem_bar_iff hWN x').mpr hx
    have hg' : toBar K g' ∈ normalizer (bar K W : Set (Bar K)) :=
      h (by rw [← bar_sup hKN hTN]; exact toBar_mem_bar K hg)
    have h1 : toBar K (g' * x' * g'⁻¹) ∈ bar K W := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hg' _).mp hx'
    exact (toBar_mem_bar_iff hWN _).mp h1
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr fun g hg => ?_⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hconj g hg x, fun hx => ?_⟩
  have h1 := hconj g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h1

end CFSG.ComponentClassification.Asc76.Lemma22
