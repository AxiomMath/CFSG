module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic
import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem exists_mem_map_eq_one {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W)
    (hW0 : W ≠ ⊥) : ∃ v ∈ W, Q v = 1 := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  by_contra hcon
  push Not at hcon
  have hQ0 : ∀ w ∈ W, Q w = 0 := fun w hw => by
    rcases zmod_two_cases (Q w) with h | h
    · exact h
    · exact absurd h (hcon w hw)
  apply hv0
  apply hW v hvW
  intro y hy
  simp only [polar, hQ0 _ (W.add_mem hvW hy), hQ0 v hvW, hQ0 y hy, sub_zero]

theorem exists_aniso_pair_of_two_le [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V}
    (hW : PolarNondegOn Q W) {c : ℕ} (hc : 2 ≤ c) (hdim : finrank (ZMod 2) W = 2 * c) :
    ∃ P : AnisoPair Q, P.a ∈ W ∧ P.b ∈ W := by
  have hW0 : W ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨a, haW, haQ⟩ := exists_mem_map_eq_one hW hW0
  by_contra hno
  push Not at hno
  have hno' : ∀ b ∈ W, polar Q a b = 1 → Q b = 0 := by
    intro b hb hab
    rcases zmod_two_cases (Q b) with h | h
    · exact h
    · exact absurd hb (hno ⟨a, b, haQ, h, hab⟩ haW)
  have ha0 : a ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at haQ
    exact zero_ne_one haQ
  obtain ⟨b₀, hb₀W, hb₀⟩ := hW.exists_polar_ne_zero haW ha0
  have hb₀1 : polar Q a b₀ = 1 := by
    rcases zmod_two_cases (polar Q a b₀) with h | h
    · exact absurd h hb₀
    · exact h
  have hQb₀ : Q b₀ = 0 := hno' b₀ hb₀W hb₀1
  have key : ∀ u ∈ W, polar Q a u = 0 → Q u = polar Q b₀ u := by
    intro u hu hau
    have h1 : polar Q a (b₀ + u) = 1 := by rw [polar_add_right, hb₀1, hau, add_zero]
    have h2 := hno' (b₀ + u) (W.add_mem hb₀W hu) h1
    rw [QuadraticMap.map_add Q, hQb₀, zero_add] at h2
    exact eq_of_add_eq_zero'' h2
  have hiso : ∀ u ∈ W, polar Q a u = 0 → ∀ u' ∈ W, polar Q a u' = 0 → polar Q u u' = 0 := by
    intro u hu hau u' hu' hau'
    have h3 : polar Q a (u + u') = 0 := by rw [polar_add_right, hau, hau', add_zero]
    have h4 : Q (u + u') = polar Q b₀ u + polar Q b₀ u' := by
      rw [key _ (W.add_mem hu hu') h3, polar_add_right]
    calc polar Q u u' = Q (u + u') - Q u - Q u' := rfl
      _ = (polar Q b₀ u + polar Q b₀ u') - polar Q b₀ u - polar Q b₀ u' := by
        rw [h4, key u hu hau, key u' hu' hau']
      _ = 0 := by ring
  have hB := nondegenerate_polarBilin_restrict hW
  obtain ⟨φ, hφ⟩ : ∃ φ : W →ₗ[ZMod 2] ZMod 2, φ = polarBilin (Q.restrict W) ⟨a, haW⟩ := ⟨_, rfl⟩
  have hφapply : ∀ u : W, φ u = polar Q a u := fun u => by
    rw [hφ, polarBilin_apply_apply, polar_restrict]
  obtain ⟨T, hT⟩ : ∃ T : Submodule (ZMod 2) W, T = LinearMap.ker φ := ⟨_, rfl⟩
  have hTmem : ∀ u : W, u ∈ T ↔ polar Q a u = 0 := fun u => by
    rw [hT, LinearMap.mem_ker, hφapply]
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    rcases zmod_two_cases t with rfl | rfl
    · exact ⟨0, map_zero φ⟩
    · exact ⟨⟨b₀, hb₀W⟩, by rw [hφapply]; exact hb₀1⟩
  have hdimT : finrank (ZMod 2) T + 1 = 2 * c := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange, finrank_top, finrank_self, hdim, ← hT] at this
    omega
  have hTle : T ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict W)) T := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [polarBilin_apply_apply, polar_restrict]
    exact hiso n.1 n.2 ((hTmem n).1 hn) u.1 u.2 ((hTmem u).1 hu)
  have h1 := Submodule.finrank_mono hTle
  rw [LinearMap.BilinForm.finrank_orthogonal hB, hdim] at h1
  omega

theorem exists_aniso_pairs_nondeg [FiniteDimensional (ZMod 2) V] :
    ∀ (c : ℕ) (W : Submodule (ZMod 2) V), finrank (ZMod 2) W = 2 * c → PolarNondegOn Q W →
      ∃ Ps : List (AnisoPair Q), Ps.Pairwise AnisoPair.Orth ∧ (∀ P ∈ Ps, P.a ∈ W ∧ P.b ∈ W) ∧
        (Ps.length = c ∨ (Ps.length + 1 = c ∧ ∃ e ∈ W, e ≠ 0 ∧ Q e = 0 ∧
          ∀ P ∈ Ps, polar Q P.a e = 0 ∧ polar Q P.b e = 0)) := by
  intro c
  induction c with
  | zero =>
    intro W hdim _
    refine ⟨[], List.Pairwise.nil, by simp, Or.inl rfl⟩
  | succ c ih =>
    intro W hdim hW
    by_cases hc : c = 0
    · subst hc
      by_cases hex : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0
      · obtain ⟨e, heW, he0, heQ⟩ := hex
        exact ⟨[], List.Pairwise.nil, by simp, Or.inr ⟨rfl, e, heW, he0, heQ, by simp⟩⟩
      · push Not at hex
        have hW0 : W ≠ ⊥ := fun h => by
          rw [h, finrank_bot] at hdim
          omega
        obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
        have hQ1 : ∀ w ∈ W, w ≠ 0 → Q w = 1 := fun w hw hw0 => by
          rcases zmod_two_cases (Q w) with h | h
          · exact absurd h (hex w hw hw0)
          · exact h
        have hnot : ¬ W ≤ Submodule.span (ZMod 2) {a} := by
          intro hle
          have h1 := Submodule.finrank_mono hle
          have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {a}) = 1 :=
            finrank_span_singleton ha0
          omega
        obtain ⟨b, hbW, hbn⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
        have hb0 : b ≠ 0 := fun h => hbn (h ▸ Submodule.zero_mem _)
        have hab0 : a + b ≠ 0 := fun h => by
          apply hbn
          have : b = a := (eq_of_add_eq_zero' h).symm
          rw [this]
          exact Submodule.subset_span (Set.mem_singleton a)
        have hpol : polar Q a b = 1 := by
          have h := QuadraticMap.map_add Q a b
          rw [hQ1 _ (W.add_mem haW hbW) hab0, hQ1 a haW ha0, hQ1 b hbW hb0] at h
          revert h
          generalize polar Q a b = p
          revert p
          decide
        exact ⟨[⟨a, b, hQ1 a haW ha0, hQ1 b hbW hb0, hpol⟩], by simp,
          by simp [haW, hbW], Or.inl rfl⟩
    · obtain ⟨P, haW, hbW⟩ := exists_aniso_pair_of_two_le hW (by omega : 2 ≤ c + 1) hdim
      have hfin := finrank_inf_perp P haW hbW
      have hW'nd := PolarNondegOn.inf_perp_aniso hW P haW hbW
      obtain ⟨Ps', hpw, hmem, hlen⟩ := ih (W ⊓ P.perp) (by omega) hW'nd
      refine ⟨P :: Ps', ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun P' hP' => ?_, hpw⟩
        obtain ⟨ha', hb'⟩ := hmem P' hP'
        have ha1 := (AnisoPair.mem_perp P).1 (Submodule.mem_inf.1 ha').2
        have hb1 := (AnisoPair.mem_perp P).1 (Submodule.mem_inf.1 hb').2
        exact ⟨ha1.1, hb1.1, ha1.2, hb1.2⟩
      · intro P' hP'
        rcases List.mem_cons.1 hP' with rfl | hP''
        · exact ⟨haW, hbW⟩
        · obtain ⟨ha', hb'⟩ := hmem P' hP''
          exact ⟨(Submodule.mem_inf.1 ha').1, (Submodule.mem_inf.1 hb').1⟩
      · rcases hlen with h | ⟨h, e, heW, he0, heQ, he⟩
        · left
          simp only [List.length_cons]
          omega
        · right
          refine ⟨by simp only [List.length_cons]; omega, e, (Submodule.mem_inf.1 heW).1, he0, heQ,
            ?_⟩
          intro P' hP'
          rcases List.mem_cons.1 hP' with rfl | hP''
          · have := (AnisoPair.mem_perp P').1 (Submodule.mem_inf.1 heW).2
            exact this
          · exact he P' hP''

end CFSG.AGLEmbedding.OmegaMinusCent
