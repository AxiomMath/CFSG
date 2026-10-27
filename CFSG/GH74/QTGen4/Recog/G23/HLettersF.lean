module

public import CFSG.GH74.QTGen4.Recog.G23.HLetters
public import CFSG.GH74.QTGen4.Recog.G23.HLettersB
public import CFSG.GH74.QTGen4.Recog.G23.HLettersE
public meta import CFSG.GH74.QTGen4.Recog.G23.HLetters
public meta import CFSG.GH74.QTGen4.Recog.G23.HSL

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Quasithin.G23Type
open scoped MatrixGroups

def slGen4 : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ![slX, slXi, slY, slYi]

theorem slGen4_val (i : Fin 4) : (slGen4 i).1 = gen4 i := by
  fin_cases i <;> simp [slGen4, gen4_eq, slX_val, slXi_val, slY_val, slYi_val]

theorem sl_gen_fold : ∀ A : M2, A.det = 1 →
    ∃ w ∈ allW 6, w.foldl (fun B i => B * gen4 i) 1 = A := by
  simpa only [evM] using sl_gen_words

theorem slGen4_mem {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))}
    (hX : slX ∈ P) (hY : slY ∈ P) (i : Fin 4) : slGen4 i ∈ P := by
  have hXi : slXi ∈ P := by rw [← slX_inv]; exact P.inv_mem hX
  have hYi : slYi ∈ P := by rw [← slY_inv]; exact P.inv_mem hY
  fin_cases i
  · exact hX
  · exact hXi
  · exact hY
  · exact hYi

theorem foldSL_mem (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hgen : ∀ i, slGen4 i ∈ P) (l : List (Fin 4)) :
    ∀ acc ∈ P, l.foldl (fun A i => A * slGen4 i) acc ∈ P := by
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons i l ih => intro acc hacc; exact ih _ (P.mul_mem hacc (hgen i))

theorem foldSL_val (l : List (Fin 4)) : ∀ acc : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
    (l.foldl (fun A i => A * slGen4 i) acc).1 = l.foldl (fun A i => A * gen4 i) acc.1 := by
  induction l with
  | nil => intro acc; rfl
  | cons i l ih =>
    intro acc
    have hi : (acc * slGen4 i).1 = acc.1 * gen4 i := by
      rw [Matrix.SpecialLinearGroup.coe_mul, slGen4_val]
    show (l.foldl (fun A i => A * slGen4 i) (acc * slGen4 i)).1 = _
    rw [ih, hi]
    rfl

theorem sl_closure_top : Subgroup.closure ({slX, slY} : Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) = ⊤ := by
  set P := Subgroup.closure ({slX, slY} : Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) with hP
  have hX : slX ∈ P := Subgroup.subset_closure (by simp)
  have hY : slY ∈ P := Subgroup.subset_closure (by simp)
  have hgen : ∀ i, slGen4 i ∈ P := slGen4_mem hX hY
  rw [eq_top_iff]
  intro A _
  obtain ⟨w, -, hw⟩ := sl_gen_fold A.1 A.2
  have hQ : w.foldl (fun B i => B * slGen4 i) 1 ∈ P :=
    foldSL_mem P hgen w 1 P.one_mem
  have hval : (w.foldl (fun B i => B * slGen4 i) 1).1 = A.1 := by
    rw [foldSL_val, Matrix.SpecialLinearGroup.coe_one]
    exact hw
  have hAeq : A = w.foldl (fun B i => B * slGen4 i) 1 := Subtype.ext hval.symm
  rw [hAeq]
  exact hQ

section Gap3

variable {G : Type} [Group G] {H H₁ H₂ : Subgroup G}

theorem G23One.closure_letters_eq [Finite G] (hH : G23One H H₁ H₂) {a b c d w : G}
    (hA : Subgroup.closure ({a, b} : Set G) = H₁) (hC : Subgroup.closure ({c, d} : Set G) = H₂)
    (hw : w ∈ H) (hwK : w ∉ H₁ ⊔ H₂) :
    Subgroup.closure ({a, b, c, d, w} : Set G) = H := by
  have hA1 : H₁ ≤ Subgroup.closure ({a, b, c, d, w} : Set G) := by
    rw [← hA]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hC1 : H₂ ≤ Subgroup.closure ({a, b, c, d, w} : Set G) := by
    rw [← hC]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hK : H₁ ⊔ H₂ ≤ Subgroup.closure ({a, b, c, d, w} : Set G) := sup_le hA1 hC1
  have hL : Subgroup.closure ({a, b, c, d, w} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h
    · rw [h]
      exact hH.le_one (show a ∈ H₁ by rw [← hA]; exact Subgroup.subset_closure (by simp))
    · rw [h]
      exact hH.le_one (show b ∈ H₁ by rw [← hA]; exact Subgroup.subset_closure (by simp))
    · rw [h]
      exact hH.le_two (show c ∈ H₂ by rw [← hC]; exact Subgroup.subset_closure (by simp))
    · rw [h]
      exact hH.le_two (show d ∈ H₂ by rw [← hC]; exact Subgroup.subset_closure (by simp))
    · rw [h]
      exact hw
  have hwL : w ∈ Subgroup.closure ({a, b, c, d, w} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hcard : Nat.card H = 2 * Nat.card ↥(H₁ ⊔ H₂) := by
    have := card_sup_mul_two_of_G23One hH
    omega
  exact closure_eq_of_index_two hL hK hwL hwK hcard

end Gap3

end CFSG.GH74.QTGen4.Recog.G23
