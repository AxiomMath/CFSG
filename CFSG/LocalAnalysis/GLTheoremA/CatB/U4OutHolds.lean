module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutSp8
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutU4eight
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem u4Out_index_form_residual {P : Type} [Group P] [Finite P]
    (h : catalogIs P (fun i => S9.isTableU4 i ∧ ¬ S9.isU4two i ∧ ¬ S9.isU5two i)) :
    ∃ a b : ℕ, (innerAut P).index = 2 ^ a * 3 ^ b := by
  obtain ⟨i, ⟨hT, hn4, hn5⟩, e⟩ := h
  have hi : S9.isD4two i ∨ S9.isSp8two i ∨ S9.isU4eight i ∨ S9.isU6two i := by
    unfold S9.isTableU4 at hT
    rcases hT with h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact absurd h1 hn5
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact absurd h1 hn4
  rcases hi with h1 | h1 | h1 | h1
  · have hc : catalogIs P S9.isD4two := by
      unfold catalogIs
      exact ⟨i, h1, e⟩
    rcases u4Out_index_d4two hc with h2 | h2
    · exact ⟨0, 1, by rw [h2]; norm_num⟩
    · exact ⟨1, 1, by rw [h2]; norm_num⟩
  · have hc : catalogIs P S9.isSp8two := by
      unfold catalogIs
      exact ⟨i, h1, e⟩
    rcases u4Out_index_sp8two hc with h2 | h2
    · exact ⟨0, 0, by rw [h2]; norm_num⟩
    · exact ⟨1, 0, by rw [h2]; norm_num⟩
  · have hc : catalogIs P S9.isU4eight := by
      unfold catalogIs
      exact ⟨i, h1, e⟩
    exact ⟨1, 1, by rw [u4Out_index_u4eight hc]; norm_num⟩
  · have hc : catalogIs P S9.isU6two := by
      unfold catalogIs
      exact ⟨i, h1, e⟩
    exact ⟨1, 1, by rw [u4Out_index_u6two hc]; norm_num⟩

theorem u4OutRest_holds : U4OutRest := by
  intro Q _ _ hQ _ hcat
  obtain ⟨a, b, hab⟩ := u4Out_index_form_residual hcat
  have hdiv := u4Out_index_dvd_quot hQ
  rw [hab] at hdiv
  obtain ⟨d₁, d₂, h₁, h₂, hd⟩ := _root_.dvd_mul.1 hdiv
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h₁
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h₂
  exact ⟨i, j, by rw [hd, hi, hj]⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
