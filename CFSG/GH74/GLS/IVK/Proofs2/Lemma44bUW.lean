module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowWreathed

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma44bUW

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree CFSG.Wreathed CFSG.Wreathed.BrauerWong
  CFSG.Open

variable {p n : ℕ} {F : Type} [Field F]

theorem unitary_diag_mem (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F) {a b : Fˣ} (ha : h.bar (a : F) * a = 1)
    (hb : h.bar (b : F) * b = 1) : (CFSG.DesarguesianPlanes.diagGL a b : GL (Fin 2) F) ∈ GU2Stated (p ^ n) F := by
  rw [Lemma41aU3.mem_GU2Stated_iff h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.DesarguesianPlanes.diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

theorem unitary_swap_mem (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F) :
    (CFSG.DesarguesianPlanes.swapGL : GL (Fin 2) F) ∈ GU2Stated (p ^ n) F := by
  rw [Lemma41aU3.mem_GU2Stated_iff h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.DesarguesianPlanes.swapGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_GU2_wreathed (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F)
    (hq : (p ^ n) % 4 = 3) {k : ℕ} (hk : (p ^ n + 1).factorization 2 = k) :
    2 ≤ k ∧ ∃ M : Subgroup ↥(GU2Stated (p ^ n) F), Nat.card M = 2 ^ (2 * k + 1) ∧
      Nonempty (↥M ≃* WreathedTwoGroup k) := by
  have hfin : Finite F := h.finite
  obtain ⟨hk2, -, hdvd, -⟩ := semidihedral_arith hq
  rw [hk] at hk2 hdvd
  refine ⟨hk2, ?_⟩
  have hcardU : Nat.card Fˣ = (p ^ n) ^ 2 - 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_units, h.card, ← pow_mul, mul_comm n 2]
  obtain ⟨α, hα⟩ := exists_orderOf_eq_of_dvd_natCard (α := Fˣ) (d := 2 ^ k)
    (by rw [hcardU]; exact (pow_dvd_pow 2 (Nat.le_succ k)).trans hdvd)
  have hα1 : α ^ (p ^ n + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hα, ← hk]
    exact Nat.ordProj_dvd _ _
  have hbar : h.bar (α : F) * α = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ]
    have := congrArg (fun u : Fˣ => (u : F)) hα1
    simpa using this
  have hbar1 : h.bar ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by simp
  have h1 : (CFSG.DesarguesianPlanes.diagGL α 1 : GL (Fin 2) F) ∈ GU2Stated (p ^ n) F := unitary_diag_mem h hbar hbar1
  have h2 : (CFSG.DesarguesianPlanes.diagGL 1 α : GL (Fin 2) F) ∈ GU2Stated (p ^ n) F := unitary_diag_mem h hbar1 hbar
  have h3 : (CFSG.DesarguesianPlanes.swapGL : GL (Fin 2) F) ∈ GU2Stated (p ^ n) F := unitary_swap_mem h
  let f := presentationHom (wreath_diagGL_left_pow hα) (wreath_diagGL_right_pow hα)
    wreath_swapGL_sq (wreath_diagGL_comm α) (wreath_swapGL_conj α)
  have hf : Function.Injective f := presentationHom_diagGL_injective hα
  have hmem : ∀ w, f w ∈ GU2Stated (p ^ n) F := by
    intro w
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ k)).symm.surjective w
    change f (element _ a b e) ∈ _
    rw [presentationHom_element]
    exact (GU2Stated (p ^ n) F).mul_mem ((GU2Stated (p ^ n) F).mul_mem
      ((GU2Stated (p ^ n) F).pow_mem h1 _) ((GU2Stated (p ^ n) F).pow_mem h2 _))
      ((GU2Stated (p ^ n) F).pow_mem h3 _)
  let g : Wreath (2 ^ k) →* ↥(GU2Stated (p ^ n) F) := f.codRestrict _ hmem
  have hg : Function.Injective g := fun x y hxy => hf (congrArg Subtype.val hxy)
  refine ⟨g.range, ?_, ⟨(MonoidHom.ofInjective hg).symm⟩⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv, card_wreath]
  ring

end Lemma44bUW

end CFSG.GH74.GLS.IVK.Proofs2
