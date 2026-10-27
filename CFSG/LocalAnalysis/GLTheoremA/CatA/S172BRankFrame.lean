module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_frame_perpL_no_minusPair {n : ℕ} (hdim : finrank (ZMod 2) V = 2 * n) :
    ∃ l : List (V × V), IsFrame Q l ∧
      ¬ ∃ a b : V, a ∈ perpL Q l ∧ b ∈ perpL Q l ∧ MinusPair Q a b := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, ∃ l : List (V × V), IsFrame Q l ∧ k ≤ l.length := by
    intro k
    induction k with
    | zero => exact ⟨[], IsFrame.nil, le_rfl⟩
    | succ k ih =>
      obtain ⟨l, hl, hk⟩ := ih
      obtain ⟨a, b, ha, hb, hab⟩ := hcon l hl
      have hperp : ∀ q ∈ l, PairPerp Q (a, b) q := by
        intro q hq
        obtain ⟨h1, h2⟩ := (mem_perpL_iff l a).1 ha q hq
        obtain ⟨h3, h4⟩ := (mem_perpL_iff l b).1 hb q hq
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [polar_comm]; exact h1
        · rw [polar_comm]; exact h2
        · rw [polar_comm]; exact h3
        · rw [polar_comm]; exact h4
      exact ⟨(a, b) :: l, IsFrame.cons hab hperp hl, by simp only [List.length_cons]; omega⟩
  obtain ⟨l, hl, hk⟩ := key (n + 1)
  have h1 := hl.finrank_Wspan
  have h2 : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  omega

theorem length_eq_pred_of_perpL_no_minusPair (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : IsPlusType Q) (hodd : Odd n) {l : List (V × V)}
    (hl : IsFrame Q l) (hno : ¬ ∃ a b : V, a ∈ perpL Q l ∧ b ∈ perpL Q l ∧ MinusPair Q a b) :
    l.length = n - 1 ∧ finrank (ZMod 2) (perpL Q l) = 2 := by
  have h1 := hl.finrank_perpL_le hQ hno
  have h2 := Submodule.finrank_add_eq_of_isCompl hl.isCompl
  have h3 := hl.finrank_Wspan
  have h4 := isFrame_length_lt_of_isPlusType_odd hl hdim hplus hodd
  omega

theorem exists_hyperbolic_pair_of_no_minusPair {P : Submodule (ZMod 2) V} (hP : P ≠ ⊥)
    (hnd : ∀ x ∈ P, (∀ y ∈ P, polar Q x y = 0) → x = 0)
    (hno : ¬ ∃ a b : V, a ∈ P ∧ b ∈ P ∧ MinusPair Q a b) :
    ∃ e f : V, e ∈ P ∧ f ∈ P ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 := by
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P, polar Q x y = 1 := by
    by_contra h
    push Not at h
    exact hx0 (hnd x hxP fun y hy => (zmod_two_cases _).resolve_right (h y hy))
  obtain ⟨e, f', heP, hf'P, he, hef'⟩ :
      ∃ e f' : V, e ∈ P ∧ f' ∈ P ∧ Q e = 0 ∧ polar Q e f' = 1 := by
    rcases zmod_two_cases (Q x) with hQx | hQx
    · exact ⟨x, y, hxP, hyP, hQx, hxy⟩
    · rcases zmod_two_cases (Q y) with hQy | hQy
      · exact ⟨y, x, hyP, hxP, hQy, by rw [polar_comm]; exact hxy⟩
      · exact (hno ⟨x, y, hxP, hyP, ⟨hQx, hQy, hxy⟩⟩).elim
  rcases zmod_two_cases (Q f') with hQf' | hQf'
  · exact ⟨e, f', heP, hf'P, he, hQf', hef'⟩
  · refine ⟨e, f' + e, heP, P.add_mem hf'P heP, he, ?_, ?_⟩
    · rw [map_add_polar, hQf', he, polar_comm Q f' e, hef']
      decide
    · rw [polar_add_right, hef', polar_self_zero]
      simp

theorem exists_family_of_isFrame {l : List (V × V)} (hl : IsFrame Q l) {m : ℕ} (hm : l.length = m) :
    ∃ a b : Fin m → V, (∀ i, MinusPair Q (a i) (b i)) ∧
      (∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) ∧
      ∀ x ∈ perpL Q l, ∀ i, polar Q x (a i) = 0 ∧ polar Q x (b i) = 0 := by
  subst hm
  refine ⟨fun i => (l.get i).1, fun i => (l.get i).2, fun i => hl.pair _ (List.get_mem l i), ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_get.1 hl.perp i j h
    · exact (List.pairwise_iff_get.1 hl.perp j i h).symm
  · intro x hx i
    obtain ⟨h1, h2⟩ := (mem_perpL_iff l x).1 hx _ (List.get_mem l i)
    rw [polar_comm Q x, polar_comm Q x]
    exact ⟨h1, h2⟩

theorem exists_minusPairFamily (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : IsPlusType Q) (hodd : Odd n) :
    ∃ (a b : Fin (n - 1) → V) (e f : V), (∀ i, MinusPair Q (a i) (b i)) ∧
      (∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
      ∀ i, polar Q e (a i) = 0 ∧ polar Q e (b i) = 0 ∧ polar Q f (a i) = 0 ∧
        polar Q f (b i) = 0 := by
  obtain ⟨l, hl, hno⟩ := exists_frame_perpL_no_minusPair (Q := Q) hdim
  obtain ⟨hlen, hfin⟩ := length_eq_pred_of_perpL_no_minusPair hQ hdim hplus hodd hl hno
  obtain ⟨a, b, hp, hperp, horth⟩ := exists_family_of_isFrame hl hlen
  have hP : perpL Q l ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfin
    omega
  obtain ⟨e, f, he, hf, hQe, hQf, hef⟩ :=
    exists_hyperbolic_pair_of_no_minusPair hP (hl.perpL_nondeg hQ) hno
  exact ⟨a, b, e, f, hp, hperp, hQe, hQf, hef, fun i =>
    ⟨(horth e he i).1, (horth e he i).2, (horth f hf i).1, (horth f hf i).2⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

end
