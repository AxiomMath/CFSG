module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.SpanSizes
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.PropertyH
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwo
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Translation2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {H : Type} [Group H]
  [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem isRegular_lines_or_points (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) (hne : ¬ ∃ q : ℕ, s = q ^ 2 ∧ t = q ^ 3) :
    (∀ L, c L = 1 → IsRegularVertex Γ L) ∨ (s = t ∧ ∀ x, c x = 0 → IsRegularVertex Γ x) := by
  classical
  obtain ⟨p, hp⟩ := exists_ncard_spanSet_eq hP hT hM c 0
  obtain ⟨p', hp'⟩ := exists_ncard_spanSet_eq hP hT hM c 1
  have htri : p = t ∨ p = 1 := by
    rcases trichotomy hP hT c hdeg (fun u _ => hasPropertyH hP hT hM u) hp with h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨p, h1, h2⟩ hne
  have htri' : p' = s ∨ p' = 1 := by
    rcases trichotomy_dual hP hT c hdeg (fun u _ => hasPropertyH hP hT hM u) hp' with
      h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · have hs2 := two_le_s hP hT c hdeg
      have hle : p' ^ 3 ≤ p' ^ 2 := by
        rw [← h2, ← h1]
        exact hst
      have hle1 : p' ≤ 1 := by
        by_contra h
        have h2' : 2 ≤ p' := by omega
        have hlt : p' ^ 2 < p' ^ 3 :=
          Nat.pow_lt_pow_right (by omega : 1 < p') (by norm_num : 2 < 3)
        omega
      rcases (by omega : p' = 0 ∨ p' = 1) with h0 | h1'
      · rw [h0] at h2
        norm_num at h2
        omega
      · exact Or.inr h1'
  rcases htri' with hps | hp'1
  ·
    left
    intro L hL M hLM
    rw [hp' L M hL hLM, hps, hdeg L, if_neg (by rw [hL]; decide)]
  · rcases htri with hpt | hp1
    ·
      right
      obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
      have hregx : IsRegularVertex Γ x := by
        intro y hy
        rw [hp x y hx hy, hpt, hdeg x, if_pos hx]
      have hts : t ≤ s := t_le_s_of_isRegularVertex hP hT c hdeg hx hregx
      refine ⟨by omega, ?_⟩
      intro x' hx' y hy
      rw [hp x' y hx' hy, hpt, hdeg x', if_pos hx']
    ·
      exfalso
      obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
      refine false_of_spans_two hP hT c hdeg hst hM hx ?_ ?_
      · intro y hy
        rw [hp x y hx hy, hp1]
      · intro L M hxL hLM
        have hL1 : c L = 1 :=
          Fin.eq_one_of_ne_zero _ fun h => c.valid hxL (hx.trans h.symm)
        rw [hp' L M hL1 hLM, hp'1]

theorem commute_of_mem_rootGroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) (hne : ¬ ∃ q : ℕ, s = q ^ 2 ∧ t = q ^ 3) (p : GPath Γ 4)
    (hp : p.NoBack) {g h : H} (hg : g ∈ rootGroup H Γ (p 1) (p 2) (p 3))
    (hh : h ∈ rootGroup H Γ (p 1) (p 2) (p 3)) : g * h = h * g := by
  rcases isRegular_lines_or_points hP hT c hdeg hst hM hne with hreg | ⟨hst', hreg⟩
  · exact commute_of_mem_rootGroup_of_isRegular hP hT c hdeg hst hM hreg p hp hg hh
  ·
    refine commute_of_mem_rootGroup_of_isRegular hP hT (dualColoring c)
      (degree_eq_of_dualColoring hdeg) (by omega) hM ?_ p hp hg hh
    intro L hL
    refine hreg L (by_contra fun h => ?_)
    rw [dualColoring_apply, Fin.eq_one_of_ne_zero _ h] at hL
    exact absurd hL (by decide)

end CFSG.Geometry.GeneralizedQuadrangles

end
