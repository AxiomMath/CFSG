module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q2Basic
import CFSG.ClassicalInvolution.Phan.PhanS8Q6HerNV

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] {M : Model K}

theorem mem_orthSpan_four {x₀ x₁ x₂ x₃ c : Vec K} :
    c ∈ orthSpan M (Set.range ![x₀, x₁, x₂, x₃]) ↔
      bf M x₀ c = 0 ∧ bf M x₁ c = 0 ∧ bf M x₂ c = 0 ∧ bf M x₃ c = 0 := by
  rw [mem_orthSpan]
  constructor
  · intro h
    exact ⟨h _ ⟨0, rfl⟩, h _ ⟨1, rfl⟩, h _ ⟨2, rfl⟩, h _ ⟨3, rfl⟩⟩
  · rintro ⟨h0, h1, h2, h3⟩ u ⟨i, rfl⟩
    fin_cases i <;> simpa

variable (M) in
@[expose] def phi (x u u' : Vec K) : K := her M x x * her M u u' - her M u x * her M x u'

theorem sesq_phi (x : Vec K) : Sesq M (phi M x) := by
  refine ⟨fun u u' y => ?_, fun u y y' => ?_, fun c u y => ?_, fun c u y => ?_⟩
  · simp only [phi, her_add_left]; ring
  · simp only [phi, her_add_right]; ring
  · simp only [phi, her_smul_left]; ring
  · simp only [phi, her_smul_right]; ring

theorem phi_self (x u : Vec K) : phi M x u u = gram M u x := by
  unfold phi gram
  ring

theorem gramInj_flag {x₀ x₁ x₂ x₃ : Vec K} (h00 : bf M x₀ x₀ = 0) (h01 : bf M x₀ x₁ = 0)
    (h02 : bf M x₀ x₂ = 0) (h11 : bf M x₁ x₁ = 0) (h22 : bf M x₂ x₂ = 0)
    (h12 : bf M x₁ x₂ ≠ 0) (h03 : bf M x₀ x₃ ≠ 0) : GramInj M ![x₀, x₁, x₂, x₃] := by
  intro l hl
  have e0 := hl 0
  have e1 := hl 1
  have e2 := hl 2
  have e3 := hl 3
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at e0 e1 e2 e3
  have b10 : bf M x₁ x₀ = 0 := by rw [bf_comm]; exact h01
  have b20 : bf M x₂ x₀ = 0 := by rw [bf_comm]; exact h02
  have b21 : bf M x₂ x₁ = bf M x₁ x₂ := bf_comm M _ _
  have b30 : bf M x₃ x₀ = bf M x₀ x₃ := bf_comm M _ _
  rw [h00, b10, b20, b30] at e0
  have l3 : l 3 = 0 := by
    have : l 3 * bf M x₀ x₃ = 0 := by linear_combination e0
    exact (mul_eq_zero.1 this).resolve_right h03
  rw [h01, h11, b21, l3] at e1
  have l2 : l 2 = 0 := by
    have : l 2 * bf M x₁ x₂ = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right h12
  rw [h02, h22, l3, l2] at e2
  have l1 : l 1 = 0 := by
    have : l 1 * bf M x₁ x₂ = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_right h12
  rw [l3, l2, l1] at e3
  have l0 : l 0 = 0 := by
    have : l 0 * bf M x₀ x₃ = 0 := by linear_combination e3
    exact (mul_eq_zero.1 this).resolve_right h03
  funext k
  fin_cases k <;> simpa

theorem gramInj_quad {a b c d : Vec K} (haa : bf M a a = 0) (hbb : bf M b b = 0)
    (hcc : bf M c c = 0) (hdd : bf M d d = 0) (hab : bf M a b = 0) (hbc : bf M b c = 0)
    (hcd : bf M c d = 0) (hda : bf M d a = 0) (hac : bf M a c ≠ 0) (hbd : bf M b d ≠ 0) :
    GramInj M ![a, b, c, d] := by
  intro l hl
  have e0 := hl 0
  have e1 := hl 1
  have e2 := hl 2
  have e3 := hl 3
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at e0 e1 e2 e3
  have bba : bf M b a = 0 := by rw [bf_comm]; exact hab
  have bcb : bf M c b = 0 := by rw [bf_comm]; exact hbc
  have bdc : bf M d c = 0 := by rw [bf_comm]; exact hcd
  have bad : bf M a d = 0 := by rw [bf_comm]; exact hda
  have bca : bf M c a = bf M a c := bf_comm M _ _
  have bdb : bf M d b = bf M b d := bf_comm M _ _
  rw [haa, bba, bca, hda] at e0
  rw [hab, hbb, bcb, bdb] at e1
  rw [hbc, hcc, bdc] at e2
  rw [bad, hcd, hdd] at e3
  have l2 : l 2 = 0 := by
    have : l 2 * bf M a c = 0 := by linear_combination e0
    exact (mul_eq_zero.1 this).resolve_right hac
  have l3 : l 3 = 0 := by
    have : l 3 * bf M b d = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right hbd
  have l0 : l 0 = 0 := by
    have : l 0 * bf M a c = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_right hac
  have l1 : l 1 = 0 := by
    have : l 1 * bf M b d = 0 := by linear_combination e3
    exact (mul_eq_zero.1 this).resolve_right hbd
  funext k
  fin_cases k <;> simpa

theorem exists_phi_ne {x n p o : Vec K} (hxx : her M x x ≠ 0) (hx0 : bf M x x = 0)
    (hn0 : bf M n n = 0) (hp0 : bf M p p = 0) (hxn : bf M x n = 0) (hxp : bf M x p = 0)
    (hnp : bf M n p ≠ 0) (hxo : bf M x o ≠ 0) (hg : gram M x n ≠ 0) :
    ∃ u u' : Vec K, (bf M x u = 0 ∧ bf M n u = 0 ∧ bf M p u = 0 ∧ bf M o u = 0) ∧
      (bf M x u' = 0 ∧ bf M n u' = 0 ∧ bf M p u' = 0 ∧ bf M o u' = 0) ∧
      phi M x u u' ≠ 0 := by
  have hGI : GramInj M ![x, n, p, tauV M x] :=
    gramInj_flag hx0 hxn hxp hn0 hp0 hnp (by simpa [her] using hxx)
  obtain ⟨w, hw, w', hw', hne⟩ := exists_her_ne hGI (i := 0) (j := 1) (by simpa using hg)
  rw [mem_orthSpan_four] at hw hw'
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  obtain ⟨hw1', hw2', hw3', hw4'⟩ := hw'
  set lam : K := bf M w o / bf M x o with hlam
  set lam' : K := bf M w' o / bf M x o with hlam'
  have bnx : bf M n x = 0 := by rw [bf_comm]; exact hxn
  have bpx : bf M p x = 0 := by rw [bf_comm]; exact hxp
  have key : ∀ (w : Vec K) (l : K), bf M x w = 0 → bf M n w = 0 → bf M p w = 0 →
      l = bf M w o / bf M x o →
      bf M x (w + (-l) • x) = 0 ∧ bf M n (w + (-l) • x) = 0 ∧ bf M p (w + (-l) • x) = 0 ∧
        bf M o (w + (-l) • x) = 0 := by
    intro w l h1 h2 h3 hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bf_add_right, bf_smul_right, h1, hx0]; ring
    · rw [bf_add_right, bf_smul_right, h2, bf_comm M n x, hxn]; ring
    · rw [bf_add_right, bf_smul_right, h3, bf_comm M p x, hxp]; ring
    · rw [bf_add_right, bf_smul_right, bf_comm M o w, bf_comm M o x, hl]
      field_simp
      ring
  refine ⟨w + (-lam) • x, w' + (-lam') • x, key w lam hw1 hw2 hw3 rfl,
    key w' lam' hw1' hw2' hw3' rfl, ?_⟩
  have F1 : her M w x = 0 := by
    simp only [her]
    rw [bf_comm]; exact hw4
  have F2 : her M x w' = 0 := by
    rw [her_conj_symm M w' x]
    have : her M w' x = 0 := by simp only [her]; rw [bf_comm]; exact hw4'
    rw [this, map_zero]
  have : phi M x (w + (-lam) • x) (w' + (-lam') • x) = her M x x * her M w w' := by
    simp only [phi, her_add_left, her_add_right, her_smul_left, her_smul_right, F1, F2]
    ring
  rw [this]
  exact mul_ne_zero hxx hne

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
