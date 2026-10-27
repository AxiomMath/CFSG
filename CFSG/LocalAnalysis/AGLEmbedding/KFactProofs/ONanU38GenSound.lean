module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Gen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Vec

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Monster.B.Fischer
open scoped Matrix

@[expose] def genSet (d : GenData) : Set SU :=
  {g | ∃ k < d.gens.size, ((g : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
    toMat3 (d.gens.getD k #[])}

theorem GLof_mulArr3 {A B : Array GF64} (hA : isSUArr A = true) (hB : isSUArr B = true) :
    GLof (mulArr3 A B) = GLof A * GLof B :=
  Units.ext (by
    rw [coe_GLof (isSUArr_mulArr3 hA hB), Units.val_mul, coe_GLof hA, coe_GLof hB,
      toMat3_mulArr3])

theorem GLof_conjTrArr3 {A : Array GF64} (hA : isSUArr A = true) :
    GLof (conjTrArr3 A) = (GLof A)⁻¹ :=
  Units.ext (by rw [coe_GLof (isSUArr_conjTrArr3 hA), coe_GLof_inv hA])

theorem GLof_oneArr3 : GLof oneArr3 = 1 := by
  have h : isSUArr oneArr3 = true := by
    have := isSUArr_ofMat3 (g := 1) SU.one_mem
    simpa [oneArr3] using this
  exact Units.ext (by rw [coe_GLof h, toMat3_oneArr3, Units.val_one])

theorem isSUArr_oneArr3 : isSUArr oneArr3 = true := by
  have := isSUArr_ofMat3 (g := 1) SU.one_mem
  simpa [oneArr3] using this

section Words

variable {G : Array (Array GF64)} (hG : ∀ k < G.size, isSUArr (G.getD k #[]) = true)

include hG

theorem isSUArr_letterArr3 {l : ℕ} (hl : l / 2 < G.size) : isSUArr (letterArr3 G l) = true := by
  by_cases hpar : l % 2 = 0
  · simp only [letterArr3, hpar, ↓reduceIte]
    exact hG _ hl
  · simp only [letterArr3, hpar, ↓reduceIte]
    exact isSUArr_conjTrArr3 (hG _ hl)

theorem isSUArr_wordArr3 {w : List ℕ} (hw : ∀ l ∈ w, l / 2 < G.size) :
    isSUArr (wordArr3 G w) = true := by
  induction w with
  | nil => exact isSUArr_oneArr3
  | cons l w ih =>
    unfold wordArr3 at ih ⊢
    rw [List.foldr_cons]
    exact isSUArr_mulArr3 (isSUArr_letterArr3 hG (hw l List.mem_cons_self))
      (ih fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))

end Words

section Main

variable (d : GenData)

@[expose] noncomputable def Mg (k : ℕ) : GL (Fin 3) GF64 := GLof (d.gens.getD k #[])

@[expose] noncomputable def Hc : Subgroup (GL (Fin 3) GF64) :=
  Subgroup.closure ((fun k => (Mg d k)⁻¹) '' {k | k < d.gens.size})

theorem Mg_mem_Hc {k : ℕ} (hk : k < d.gens.size) : Mg d k ∈ Hc d := by
  have : (Mg d k)⁻¹ ∈ Hc d := Subgroup.subset_closure ⟨k, hk, rfl⟩
  simpa using (Hc d).inv_mem this

theorem GLof_letter_mem (hG : ∀ k < d.gens.size, isSUArr (d.gens.getD k #[]) = true) {l : ℕ}
    (hl : l / 2 < d.gens.size) : GLof (letterArr3 d.gens l) ∈ Hc d := by
  by_cases hpar : l % 2 = 0
  · simp only [letterArr3, hpar, ↓reduceIte]
    exact Mg_mem_Hc d hl
  · simp only [letterArr3, hpar, ↓reduceIte]
    rw [GLof_conjTrArr3 (hG _ hl)]
    exact Subgroup.subset_closure ⟨l / 2, hl, rfl⟩

theorem GLof_word_mem (hG : ∀ k < d.gens.size, isSUArr (d.gens.getD k #[]) = true) {w : List ℕ}
    (hw : ∀ l ∈ w, l / 2 < d.gens.size) : GLof (wordArr3 d.gens w) ∈ Hc d := by
  induction w with
  | nil =>
    unfold wordArr3
    simp only [List.foldr_nil]
    rw [GLof_oneArr3]
    exact (Hc d).one_mem
  | cons l w ih =>
    have hs := isSUArr_wordArr3 hG (w := w) (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))
    have hl := isSUArr_letterArr3 hG (hw l List.mem_cons_self)
    have : wordArr3 d.gens (l :: w) = mulArr3 (letterArr3 d.gens l) (wordArr3 d.gens w) := rfl
    rw [this, GLof_mulArr3 hl hs]
    exact (Hc d).mul_mem (GLof_letter_mem d hG (hw l List.mem_cons_self))
      (ih fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))

end Main

end CFSG.AGLEmbedding.ChevOuter.U38
