module

public import CFSG.Geometry.ProjectiveSpaces.Basic
import Mathlib.Tactic.Set

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} (G : ProjectiveSpace P)

theorem eq_of_mem_line_of_not_mem {S : Set P} (hS : G.IsSubspace S) {q w x y : P} (hq : q ∉ S)
    (hx : x ∈ G.line q w) (hy : y ∈ G.line q w) (hxS : x ∈ S) (hyS : y ∈ S) : x = y := by
  by_contra hxy
  exact hq (hS x hxS y hyS hxy (G.line_eq_line hxy hx hy ▸ G.left_mem_line q w))

theorem not_mem_line_of_not_mem {S : Set P} (hS : G.IsSubspace S) {x y z : P} (hx : x ∈ S)
    (hy : y ∈ S) (hz : z ∉ S) : z ∉ G.line x y := fun h => hz (hS.line_subset hx hy h)

theorem not_collinear_of_not_mem {S : Set P} (hS : G.IsSubspace S) {x y z : P} (hxy : x ≠ y)
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∉ S) : ¬ G.Collinear x y z := by
  rw [G.collinear_iff_of_ne hxy]
  exact G.not_mem_line_of_not_mem hS hx hy hz

theorem eq_of_mem_line_of_mem_line {c a b x : P} (h : ¬ G.Collinear c a b)
    (hx : x ∈ G.line c a) (hx' : x ∈ G.line a b) : x = a := by
  obtain ⟨hca, -, hab⟩ := G.ne_of_not_collinear h
  have hne : G.line c a ≠ G.line a b := fun e => h (Or.inr (e ▸ G.right_mem_line a b))
  exact G.eq_of_mem_of_mem (G.line_mem_lines hca) (G.line_mem_lines hab) hne hx hx'
    (G.right_mem_line c a) (G.left_mem_line a b)

theorem line_subset_plane₁₃ {x y z : P} (h : ¬ G.Collinear x y z) :
    G.line x z ⊆ G.plane x y z :=
  (G.isSubspace_plane h).line_subset (G.left_mem_plane x y z) (G.right_mem_plane x y z)

theorem line_subset_plane₂₃ {x y z : P} (h : ¬ G.Collinear x y z) :
    G.line y z ⊆ G.plane x y z :=
  (G.isSubspace_plane h).line_subset (G.middle_mem_plane x y z) (G.right_mem_plane x y z)

theorem collinear_of_plane_ne {a₁ a₂ a₃ b₁ b₂ b₃ p₁₂ p₁₃ p₂₃ : P}
    (ha : ¬ G.Collinear a₁ a₂ a₃) (hb : ¬ G.Collinear b₁ b₂ b₃)
    (hne : G.plane a₁ a₂ a₃ ≠ G.plane b₁ b₂ b₃)
    (hp₁₂ : p₁₂ ∈ G.line a₁ a₂ ∩ G.line b₁ b₂) (hp₁₃ : p₁₃ ∈ G.line a₁ a₃ ∩ G.line b₁ b₃)
    (hp₂₃ : p₂₃ ∈ G.line a₂ a₃ ∩ G.line b₂ b₃) : G.Collinear p₁₂ p₁₃ p₂₃ :=
  G.collinear_of_mem_plane_of_mem_plane ha hb hne (G.line_subset_plane _ _ _ hp₁₂.1)
    (G.line_subset_plane₁₃ ha hp₁₃.1) (G.line_subset_plane₂₃ ha hp₂₃.1)
    (G.line_subset_plane _ _ _ hp₁₂.2) (G.line_subset_plane₁₃ hb hp₁₃.2)
    (G.line_subset_plane₂₃ hb hp₂₃.2)

theorem mem_line_of_mem_line {c a b : P} (hb : b ∈ G.line c a) (hab : a ≠ b) :
    c ∈ G.line a b := by
  rw [G.line_eq_line hab (G.right_mem_line c a) hb]
  exact G.left_mem_line c a

theorem desargues (hdim : ∀ x y z : P, ¬ G.Collinear x y z → ∃ w, w ∉ G.plane x y z)
    {c a₁ a₂ a₃ b₁ b₂ b₃ p₁₂ p₁₃ p₂₃ : P}
    (ha : ¬ G.Collinear a₁ a₂ a₃) (hb : ¬ G.Collinear b₁ b₂ b₃)
    (h₁₂ : ¬ G.Collinear c a₁ a₂) (h₁₃ : ¬ G.Collinear c a₁ a₃) (h₂₃ : ¬ G.Collinear c a₂ a₃)
    (hb₁ : b₁ ∈ G.line c a₁) (hb₂ : b₂ ∈ G.line c a₂) (hb₃ : b₃ ∈ G.line c a₃)
    (hcb₁ : c ≠ b₁) (hcb₂ : c ≠ b₂) (hcb₃ : c ≠ b₃)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂) (hab₃ : a₃ ≠ b₃)
    (hp₁₂ : p₁₂ ∈ G.line a₁ a₂ ∩ G.line b₁ b₂) (hp₁₃ : p₁₃ ∈ G.line a₁ a₃ ∩ G.line b₁ b₃)
    (hp₂₃ : p₂₃ ∈ G.line a₂ a₃ ∩ G.line b₂ b₃) : G.Collinear p₁₂ p₁₃ p₂₃ := by
  by_cases hne' : G.plane a₁ a₂ a₃ ≠ G.plane b₁ b₂ b₃
  · exact G.collinear_of_plane_ne ha hb hne' hp₁₂ hp₁₃ hp₂₃
  have hne : G.plane a₁ a₂ a₃ = G.plane b₁ b₂ b₃ := Classical.not_not.1 hne'
  obtain ⟨hca₁, hca₂, ha₁₂⟩ := G.ne_of_not_collinear h₁₂
  obtain ⟨-, hca₃, ha₁₃⟩ := G.ne_of_not_collinear h₁₃
  obtain ⟨-, -, ha₂₃⟩ := G.ne_of_not_collinear h₂₃
  obtain ⟨hb₁₂, hb₁₃, hb₂₃⟩ := G.ne_of_not_collinear hb
  set π := G.plane a₁ a₂ a₃ with hπdef
  have hπ : G.IsSubspace π := G.isSubspace_plane ha
  have ha₁π : a₁ ∈ π := G.left_mem_plane _ _ _
  have ha₂π : a₂ ∈ π := G.middle_mem_plane _ _ _
  have ha₃π : a₃ ∈ π := G.right_mem_plane _ _ _
  have hb₁π : b₁ ∈ π := hne ▸ G.left_mem_plane _ _ _
  have hb₂π : b₂ ∈ π := hne ▸ G.middle_mem_plane _ _ _
  have hb₃π : b₃ ∈ π := hne ▸ G.right_mem_plane _ _ _
  have hcπ : c ∈ π := hπ.line_subset ha₁π hb₁π (G.mem_line_of_mem_line hb₁ hab₁)
  obtain ⟨q, hq⟩ := hdim a₁ a₂ a₃ ha
  have hqa₁ : q ≠ a₁ := fun e => hq (by rw [e]; exact ha₁π)
  obtain ⟨r, hr, hrq, hra₁⟩ := G.exists_mem_line_ne hqa₁
  have hlr : G.line q r = G.line q a₁ := G.line_eq_of_mem hr hrq
  have hla₁r : G.line a₁ r = G.line q a₁ :=
    G.line_eq_line (Ne.symm hra₁) (G.right_mem_line q a₁) hr
  have hrπ : r ∉ π := fun h => hq (hπ.line_subset ha₁π h (hla₁r ▸ G.left_mem_line q a₁))
  have hcr : c ≠ r := fun e => hrπ (by rw [← e]; exact hcπ)
  have hσ : ¬ G.Collinear c a₁ q := G.not_collinear_of_not_mem hπ hca₁ hcπ ha₁π hq
  have hσS := G.isSubspace_plane hσ
  have hrσ : r ∈ G.plane c a₁ q :=
    hσS.line_subset (G.right_mem_plane _ _ _) (G.middle_mem_plane _ _ _) hr
  have hb₁σ : b₁ ∈ G.plane c a₁ q := G.line_subset_plane _ _ _ hb₁
  have hqb₁ : q ≠ b₁ := fun e => hq (by rw [e]; exact hb₁π)
  obtain ⟨s, hs1, hs2⟩ := G.inter_nonempty_of_mem_plane hσ (G.left_mem_plane _ _ _) hrσ
    (G.right_mem_plane _ _ _) hb₁σ hcr hqb₁
  have hsπ : s ∉ π := by
    intro hsπ
    have hsb₁ : s = b₁ := G.eq_of_mem_line_of_not_mem hπ hq hs2 (G.right_mem_line q b₁) hsπ hb₁π
    have h1 : G.line c b₁ = G.line c r := G.line_eq_of_mem (hsb₁ ▸ hs1) (Ne.symm hcb₁)
    have h2 : G.line c b₁ = G.line c a₁ := G.line_eq_of_mem hb₁ (Ne.symm hcb₁)
    exact hrπ (hπ.line_subset hcπ ha₁π (h2 ▸ h1 ▸ G.right_mem_line c r))
  have hcs : c ≠ s := fun e => hsπ (by rw [← e]; exact hcπ)
  have hra : ¬ G.Collinear r a₂ a₃ := fun h => hrπ (by
    rcases h.rotate with h | h
    · exact absurd h ha₂₃
    · exact hπ.line_subset ha₂π ha₃π h)
  have hsb : ¬ G.Collinear s b₂ b₃ := fun h => hsπ (by
    rcases h.rotate with h | h
    · exact absurd h hb₂₃
    · exact hπ.line_subset hb₂π hb₃π h)
  have hne₂ : G.plane r a₂ a₃ ≠ G.plane s b₂ b₃ := by
    intro e
    have hπ' : G.plane r a₂ a₃ ≠ π := fun e' => hrπ (e' ▸ G.left_mem_plane r a₂ a₃)
    have hcol : G.Collinear a₂ a₃ b₂ :=
      G.collinear_of_mem_plane_of_mem_plane hra ha hπ' (G.middle_mem_plane _ _ _)
        (G.right_mem_plane _ _ _) (e ▸ G.middle_mem_plane _ _ _) ha₂π ha₃π hb₂π
    exact hab₂ (G.eq_of_mem_line_of_mem_line h₂₃ hb₂
      ((G.collinear_iff_of_ne ha₂₃).1 hcol)).symm
  have hrb : ∀ {a b : P}, a ∈ π → b ∈ π → b ∈ G.line c a → c ≠ a →
      ∃ x', x' ∈ G.line r a ∩ G.line s b := by
    intro a b haπ hbπ hba hca
    have hcra : ¬ G.Collinear c r a := fun h' => hrπ (by
      rcases h'.swap23 with e | h'
      · exact absurd e hca
      · exact hπ.line_subset hcπ haπ h')
    have hS := G.isSubspace_plane hcra
    have hsρ : s ∈ G.plane c r a := G.line_subset_plane _ _ _ hs1
    have hbρ : b ∈ G.plane c r a := G.line_subset_plane₁₃ hcra hba
    have hra : r ≠ a := fun e => hrπ (by rw [e]; exact haπ)
    have hsb : s ≠ b := fun e => hsπ (by rw [e]; exact hbπ)
    exact G.inter_nonempty_of_mem_plane hcra (G.middle_mem_plane _ _ _)
      (G.right_mem_plane _ _ _) hsρ hbρ hra hsb
  obtain ⟨p'₁₂, hp'₁₂⟩ := hrb ha₂π hb₂π hb₂ hca₂
  obtain ⟨p'₁₃, hp'₁₃⟩ := hrb ha₃π hb₃π hb₃ hca₃
  have hcol' : G.Collinear p'₁₂ p'₁₃ p₂₃ :=
    G.collinear_of_plane_ne hra hsb hne₂ hp'₁₂ hp'₁₃ hp₂₃
  have hproj : ∀ {a b x x' : P}, a ∈ π → b ∈ π → b ∈ G.line c a → a ≠ b → c ≠ b →
      ¬ G.Collinear c a₁ a → x ∈ G.line a₁ a ∩ G.line b₁ b → x' ∈ G.line r a ∩ G.line s b →
      x' ≠ q ∧ x ∈ G.line q x' := by
    intro a b x x' haπ hbπ hba hab hcb hca hx hx'
    have ha₁a : a₁ ≠ a := (G.ne_of_not_collinear hca).2.2
    have hb₁b : b₁ ≠ b := by
      intro e
      have hne3 : G.line c a₁ ≠ G.line c a := fun e' => hca (Or.inr (e' ▸ G.right_mem_line c a))
      exact hcb ((G.eq_of_mem_of_mem (G.line_mem_lines hca₁)
        (G.line_mem_lines (G.ne_of_not_collinear hca).2.1) hne3 (G.left_mem_line c a₁)
        (G.left_mem_line c a) hb₁ (by rw [e]; exact hba)).trans e)
    have hα : ¬ G.Collinear a₁ a q := G.not_collinear_of_not_mem hπ ha₁a ha₁π haπ hq
    have hβ : ¬ G.Collinear b₁ b q := G.not_collinear_of_not_mem hπ hb₁b hb₁π hbπ hq
    have hαS := G.isSubspace_plane hα
    have hβS := G.isSubspace_plane hβ
    have hαβ : G.plane a₁ a q ≠ G.plane b₁ b q := by
      intro e
      have hαπ : G.plane a₁ a q ≠ π := fun e' => by
        have h' := G.right_mem_plane a₁ a q
        rw [e'] at h'
        exact hq h'
      have hb₁α : b₁ ∈ G.plane a₁ a q := by rw [e]; exact G.left_mem_plane _ _ _
      have hcol := G.collinear_of_mem_plane_of_mem_plane hα ha hαπ (G.left_mem_plane _ _ _)
        (G.middle_mem_plane _ _ _) hb₁α ha₁π haπ hb₁π
      exact hab₁ (G.eq_of_mem_line_of_mem_line hca hb₁
        ((G.collinear_iff_of_ne ha₁a).1 hcol)).symm
    have hrα : r ∈ G.plane a₁ a q :=
      hαS.line_subset (G.right_mem_plane _ _ _) (G.left_mem_plane _ _ _) hr
    have hsβ : s ∈ G.plane b₁ b q :=
      hβS.line_subset (G.right_mem_plane _ _ _) (G.left_mem_plane _ _ _) hs2
    have hx'α : x' ∈ G.plane a₁ a q := hαS.line_subset hrα (G.middle_mem_plane _ _ _) hx'.1
    have hx'β : x' ∈ G.plane b₁ b q := hβS.line_subset hsβ (G.middle_mem_plane _ _ _) hx'.2
    have hcol := G.collinear_of_mem_plane_of_mem_plane hα hβ hαβ (G.right_mem_plane _ _ _)
      hx'α (G.line_subset_plane _ _ _ hx.1) (G.right_mem_plane _ _ _) hx'β
      (G.line_subset_plane _ _ _ hx.2)
    have hx'q : x' ≠ q := by
      intro e
      have hqra : q ∈ G.line r a := e ▸ hx'.1
      have h1 : G.line r q = G.line r a := G.line_eq_of_mem hqra (Ne.symm hrq)
      have haq : a ∈ G.line q a₁ := by
        rw [← hlr, G.line_comm, h1]
        exact G.right_mem_line r a
      exact hq (hπ.line_subset ha₁π haπ
        (G.line_eq_line ha₁a (G.right_mem_line q a₁) haq ▸ G.left_mem_line q a₁))
    exact ⟨hx'q, (G.collinear_iff_of_ne (Ne.symm hx'q)).1 hcol⟩
  obtain ⟨hq12, hp12⟩ := hproj ha₂π hb₂π hb₂ hab₂ hcb₂ h₁₂ hp₁₂ hp'₁₂
  obtain ⟨hq13, hp13⟩ := hproj ha₃π hb₃π hb₃ hab₃ hcb₃ h₁₃ hp₁₃ hp'₁₃
  have hp₁₂π : p₁₂ ∈ π := G.line_subset_plane _ _ _ hp₁₂.1
  have hp₁₃π : p₁₃ ∈ π := G.line_subset_plane₁₃ ha hp₁₃.1
  have hp₂₃π : p₂₃ ∈ π := G.line_subset_plane₂₃ ha hp₂₃.1
  by_cases he : p'₁₂ = p'₁₃
  · rw [← he] at hp13
    exact Or.inl (G.eq_of_mem_line_of_not_mem hπ hq hp12 hp13 hp₁₂π hp₁₃π)
  have hm : p₂₃ ∈ G.line p'₁₂ p'₁₃ := (G.collinear_iff_of_ne he).1 hcol'
  by_cases hqm : q ∈ G.line p'₁₂ p'₁₃
  · have hm1 : G.line q p'₁₂ = G.line p'₁₂ p'₁₃ :=
      G.line_eq_line (Ne.symm hq12) hqm (G.left_mem_line _ _)
    have hm2 : G.line q p'₁₃ = G.line p'₁₂ p'₁₃ :=
      G.line_eq_line (Ne.symm hq13) hqm (G.right_mem_line _ _)
    rw [hm1] at hp12
    rw [hm2] at hp13
    have e1 : p₁₂ = p₁₃ := G.eq_of_mem_line_of_not_mem hπ hq (hm1 ▸ hp12) (hm1 ▸ hp13)
      hp₁₂π hp₁₃π
    exact Or.inl e1
  have hτ : ¬ G.Collinear p'₁₂ p'₁₃ q := fun h' => hqm ((G.collinear_iff_of_ne he).1 h')
  have hτS := G.isSubspace_plane hτ
  have hτπ : G.plane p'₁₂ p'₁₃ q ≠ π := fun e => by
    have h' := G.right_mem_plane p'₁₂ p'₁₃ q
    rw [e] at h'
    exact hq h'
  exact G.collinear_of_mem_plane_of_mem_plane hτ ha hτπ
    (hτS.line_subset (G.right_mem_plane _ _ _) (G.left_mem_plane _ _ _) hp12)
    (hτS.line_subset (G.right_mem_plane _ _ _) (G.middle_mem_plane _ _ _) hp13)
    (G.line_subset_plane _ _ _ hm) hp₁₂π hp₁₃π hp₂₃π

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
