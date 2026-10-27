module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

theorem le_glaTwoLocalRank_of_twist {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    {E V : Subgroup K} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) (hV : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set K)) (htw : ¬ ∀ e ∈ E, ∀ v ∈ V, e * v = v * e) :
    k ≤ GLATwoLocalRank p K := by
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    exact htw fun e _ v hv => by rw [Subgroup.mem_bot.1 hv, mul_one, one_mul]
  have h := card_le_pow_glaTwoLocalRank hp hE hV1 hV hEV
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h

theorem i1017_spor_cases (hTab : I1017TableFact) (hCo3 : I1017CoThreeTwist)
    (hFi22 : I1017FiTwoTwoTwist) (hFi23 : I1017FiTwoThreeTwist) (hBaby : I1017BabyTwist)
    {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : catalogIs K isSporIndex) {E V : Subgroup K} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ k) (hk : 3 ≤ k) (hV : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set K)) (htw : ¬ ∀ e ∈ E, ∀ v ∈ V, e * v = v * e) :
    (p = 3 ∧ (catalogIs K (sporIs .ONan) ∨ catalogIs K (sporIs .HN))) ∨
    (∃ row : Row, row.prime = p ∧ catalogIs K (sporIs row.name)) ∨
    (p = 3 ∧ catalogIs K (sporIs .Fi22) ∧ k ≤ 3) ∨
    (p = 3 ∧ (catalogIs K (sporIs .Fi23) ∨ catalogIs K (sporIs .B)) ∧ k ≤ 4) := by
  have hm : 3 ≤ GLATwoLocalRank p K :=
    hk.trans (le_glaTwoLocalRank_of_twist hp hE hcard hV hEV htw)
  rcases hTab K p hp hp2 hK hm with ⟨rfl, i, ⟨s, hs, rfl⟩, he⟩ | ⟨rfl, hM⟩
  · have hcat : catalogIs K (sporIs s) := ⟨_, rfl, he⟩
    have hno : ∀ r, r ≤ k → ¬ NoTwistRank s r := fun r hr hN =>
      htw (hN K hcat E hE (by rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hr) V hV hEV)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, Or.inl hcat⟩
    · exact Or.inl ⟨rfl, Or.inr hcat⟩
    · exact Or.inr (Or.inl ⟨.ly, rfl, hcat⟩)
    · exact Or.inr (Or.inl ⟨.co1, rfl, hcat⟩)
    · exact Or.inr (Or.inl ⟨.co2, rfl, hcat⟩)
    · exact (hno 3 hk hCo3).elim
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, hcat, ?_⟩))
      by_contra h
      exact hno 4 (by omega) hFi22
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl hcat, ?_⟩))
      by_contra h
      exact hno 5 (by omega) hFi23
    · exact Or.inr (Or.inl ⟨.fi24, rfl, hcat⟩)
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr hcat, ?_⟩))
      by_contra h
      exact hno 5 (by omega) hBaby
    · exact Or.inr (Or.inl ⟨.th, rfl, hcat⟩)
    · exact Or.inr (Or.inl ⟨.m3, rfl, hcat⟩)
    · exact Or.inr (Or.inl ⟨.suz, rfl, hcat⟩)
  · exact Or.inr (Or.inl ⟨.m5, rfl, hM⟩)

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
