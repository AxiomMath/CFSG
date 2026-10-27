
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowCertInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

structure SylowParts : Prop where
  normT0 : normT0OK (enumBFS 42 gensS 20160).tabs = true
  center : centerT0OK = true
  ok₁ : enumOK 42 (wordTabs wU₁) (enumBFS 42 (wordTabs wU₁) 16) = true
  size₁ : (enumBFS 42 (wordTabs wU₁) 16).tabs.size = 16
  ok₂ : enumOK 42 (wordTabs wU₂) (enumBFS 42 (wordTabs wU₂) 16) = true
  size₂ : (enumBFS 42 (wordTabs wU₂) 16).tabs.size = 16
  mem₁ : ∀ k < 16, found (indexOf (enumBFS 42 (wordTabs wU₁) 16).tabs)
    (enumBFS 42 (wordTabs wU₁) 16).tabs (tgT k) = true
  mem₂ : ∀ k < 16, found (indexOf (enumBFS 42 (wordTabs wU₂) 16).tabs)
    (enumBFS 42 (wordTabs wU₂) 16).tabs (tgT (4 * k)) = true
  normal₁ : normalOK 42 (enumBFS 42 (wordTabs wU₁) 16).tabs (wordTabs wP₁)
    ((wordTabs wP₁).map (invTab 42)) (wordTabs wU₁) = true
  normal₂ : normalOK 42 (enumBFS 42 (wordTabs wU₂) 16).tabs (wordTabs wP₂)
    ((wordTabs wP₂).map (invTab 42)) (wordTabs wU₂) = true
  prod : prodOK = true

@[expose] def U1 : Subgroup (Equiv.Perm (Fin 42)) := closure (wordSet wU₁)

@[expose] def U2 : Subgroup (Equiv.Perm (Fin 42)) := closure (wordSet wU₂)

theorem le_normalizer_of_normalOK {ws us : List (List ℕ)} {T : Array Tab}
    (hT : Enumerates (closure (wordSet us)) T.toList)
    (h : normalOK 42 T (wordTabs ws) ((wordTabs ws).map (invTab 42)) (wordTabs us) = true) :
    closure (wordSet ws) ≤ normalizer ((closure (wordSet us) : Subgroup _) : Set _) := by
  rw [closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := mem_wordSet_iff.1 ha
  have hj' : j < (wordTabs ws).size := by rw [size_wordTabs]; exact hj
  have hrep := tabRep_wordTabs ws hj
  rw [← getElem!_pos ws j hj] at hrep
  have key : ∀ s ∈ wordSet us, wordPerm ws[j]! * s * (wordPerm ws[j]!)⁻¹ ∈ closure (wordSet us) ∧
      (wordPerm ws[j]!)⁻¹ * s * wordPerm ws[j]! ∈ closure (wordSet us) := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := mem_wordSet_iff.1 hs
    have hi' : i < (wordTabs us).size := by rw [size_wordTabs]; exact hi
    have hsrep := tabRep_wordTabs us hi
    rw [← getElem!_pos us i hi] at hsrep
    exact conj_mem_of_normalOK hT h hj' hi' hrep hsrep
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro g
  constructor
  · exact conj_mem_closure fun s hs => (key s hs).1
  · intro hg
    have := conj_mem_closure (a := (wordPerm ws[j]!)⁻¹)
      (fun s hs => by rw [inv_inv]; exact (key s hs).2) hg
    rwa [show (wordPerm ws[j]!)⁻¹ * (wordPerm ws[j]! * g * (wordPerm ws[j]!)⁻¹) *
      (wordPerm ws[j]!)⁻¹⁻¹ = g by group] at this

theorem wordSet_append (ws us : List (List ℕ)) :
    wordSet (ws ++ us) = wordSet ws ∪ wordSet us := by
  ext g
  simp only [wordSet, Set.mem_ofPred_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨w, hw | hw, rfl⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨w, Or.inl hw, rfl⟩
    · exact ⟨w, Or.inr hw, rfl⟩

section Parts2

theorem closure_P1_P2 : closure (wordSet (wP₁ ++ wP₂)) = S := by
  refine le_antisymm (closure_wordSet_le _) ?_
  have hm : ∀ w ∈ wP₁ ++ wP₂, wordPerm w ∈ closure (wordSet (wP₁ ++ wP₂)) :=
    fun w hw => subset_closure ⟨w, hw, rfl⟩
  have h2 : g₂ ∈ closure (wordSet (wP₁ ++ wP₂)) := by
    have h := hm [1] (by simp [wP₁, wP₂])
    simpa [wordPerm, genS] using h
  have h3 : g₃ ∈ closure (wordSet (wP₁ ++ wP₂)) := by
    have h := hm [2] (by simp [wP₁, wP₂])
    simpa [wordPerm, genS] using h
  have h1 : g₁ ∈ closure (wordSet (wP₁ ++ wP₂)) := by
    have h := hm [1, 0, 1] (by simp [wP₁, wP₂])
    simp only [wordPerm, genS, List.foldl_cons, List.foldl_nil, one_mul, if_pos, if_neg,
      one_ne_zero, reduceIte] at h
    have h' := mul_mem (mul_mem (inv_mem h2) h) (inv_mem h2)
    have e : g₂⁻¹ * (g₂ * g₁ * g₂) * g₂⁻¹ = g₁ := by group
    rwa [e] at h'
  have hSdef : S = closure {g₁, g₂, g₃} := rfl
  rw [hSdef, closure_le]
  rintro a (rfl | rfl | rfl)
  · exact h1
  · exact h2
  · exact h3

theorem sup_P1_P2 : P1 ⊔ P2 = S := by
  rw [← closure_P1_P2, P1, P2, ← Subgroup.closure_union, wordSet_append]

end Parts2

end CFSG.ComponentClassification.GrSLit.L34Facts
