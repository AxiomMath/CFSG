module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

set_option linter.unusedSectionVars false


private theorem i167CLin_jrigid_aux1 {M : Type} [Group M] [Finite M] {b e : ℕ}
    (hmodel : StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e) {lab : GLALabel}
    (hlab : HasLabel M (fun l : GLALabel => l = lab)) :
    canonLabel lab = (⟨.A, b - 1, e⟩ : GLALabel) := by
  simp only [StatedClassicalModel, StatedLieAdmissible] at hmodel
  obtain ⟨hadm, E, hfield, hfin, hE, hiso⟩ := hmodel
  letI : Field E := hfield
  letI : Finite E := hfin
  obtain ⟨-, -, hb2, -, -⟩ := hadm
  exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput
    CFSG.StandardType.ggLabelRigidInput_holds) M lab b e E hb2 hE hlab hiso

private theorem i167CLin_jrigid_aux2 {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {M : Type}
    [Group M] [Finite M] (hq : CFSG.Open.IsQuasisimple M) (hp3 : p = 3)
    (hPS : Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M)) {b e n : ℕ}
    (hmodel : StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e)
    (hodd : Odd n) (hn5 : 5 ≤ n) (hcat : catalogIs (PSimple 3 J) (isLnA n 2)) :
    p = 3 ∧ e = 1 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ b = n ∧ catalogIs (PSimple 3 J) (isLnA n 2) := by
  subst hp3
  obtain ⟨ePS⟩ := hPS
  have hcatM : catalogIs (M ⧸ Subgroup.center M) (isLnA n 2) := (catalogIs_congr ePS).mp hcat
  obtain ⟨lab, hlab, hcanon⟩ := i167COrth_label_isLnA hq hn5 hcatM
  have key : (⟨.A, n - 1, 1⟩ : GLALabel) = ⟨.A, b - 1, e⟩ :=
    hcanon.symm.trans (i167CLin_jrigid_aux1 hmodel hlab)
  have hrank : n - 1 = b - 1 := congrArg (fun l : GLALabel => l.rank) key
  have hn : (1 : ℕ) = e := congrArg (fun l : GLALabel => l.n) key
  have hbn : b = n := by omega
  exact ⟨rfl, hn.symm, n, hodd, hn5, hbn, hcat⟩

private theorem i167CLin_jrigid_aux3 {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {M : Type}
    [Group M] [Finite M] (hq : CFSG.Open.IsQuasisimple M) (hp3 : p = 3)
    (hPS : Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M)) {b e n : ℕ}
    (hmodel : StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e)
    (hn6 : 6 ≤ n) (hcat : catalogIs (PSimple 3 J) (isOmMA n 2)) : False := by
  subst hp3
  obtain ⟨ePS⟩ := hPS
  have hcatM : catalogIs (M ⧸ Subgroup.center M) (isOmMA n 2) := (catalogIs_congr ePS).mp hcat
  have hn4 : 4 ≤ n := by omega
  obtain ⟨lab, hlab, hcanon⟩ := i167COrth_label_isOmMA (k := 1) hq hn4 (le_refl 1) hcatM
  have key : (⟨.twD, n, 1⟩ : GLALabel) = ⟨.A, b - 1, e⟩ :=
    hcanon.symm.trans (i167CLin_jrigid_aux1 hmodel hlab)
  exact absurd (congrArg (fun l : GLALabel => l.tag) key) (by simp)

private theorem i167CLin_jrigid_aux4 {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {M : Type}
    [Group M] [Finite M] (hq : CFSG.Open.IsQuasisimple M)
    (hPS : Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M)) {b e n k : ℕ}
    (hmodel : StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e)
    (hn3 : 3 ≤ n) (hk1 : k = 1 → 5 ≤ n) (hk : 1 ≤ k) (hkdiv : p ∣ 2 ^ k + 1)
    (hcat : catalogIs (PSimple p J) (isOmPA n (2 ^ k))) :
    ∃ k : ℕ, 2 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ e = k ∧ b = 4 ∧
      catalogIs (PSimple p J) (isOmPA 3 (2 ^ k)) := by
  obtain ⟨ePS⟩ := hPS
  have hcatM : catalogIs (M ⧸ Subgroup.center M) (isOmPA n (2 ^ k)) := (catalogIs_congr ePS).mp hcat
  have hk3 : n = 3 → 2 ≤ k := by
    intro hn3'
    by_contra hk2
    have hk1' : k = 1 := by omega
    have := hk1 hk1'
    omega
  obtain ⟨lab, hlab, hcanon⟩ := i167COrth_label_isOmPA hq hn3 hk hk3 hcatM
  have hdictlab := i167CLin_jrigid_aux1 hmodel hlab
  by_cases hn3' : n = 3
  · have hcanon3 : canonLabel lab = (⟨.A, 3, k⟩ : GLALabel) := by
      rw [if_pos hn3'] at hcanon
      exact hcanon
    have key : (⟨.A, 3, k⟩ : GLALabel) = ⟨.A, b - 1, e⟩ := hcanon3.symm.trans hdictlab
    have hrank : 3 = b - 1 := congrArg (fun l : GLALabel => l.rank) key
    have hke : k = e := congrArg (fun l : GLALabel => l.n) key
    have hb4 : b = 4 := by omega
    exact ⟨k, hk3 hn3', hkdiv, hke.symm, hb4, by simpa [hn3'] using hcat⟩
  · exfalso
    have hcanonD : canonLabel lab = (⟨.D, n, k⟩ : GLALabel) := by
      rw [if_neg hn3'] at hcanon
      exact hcanon
    have key : (⟨.D, n, k⟩ : GLALabel) = ⟨.A, b - 1, e⟩ := hcanonD.symm.trans hdictlab
    exact absurd (congrArg (fun l : GLALabel => l.tag) key) (by simp)

theorem i167CLin_jrigid {G : Type} [Group G] {p : ℕ} {J : Subgroup G} (hJt : Type167J p J) {M : Type} [Group M]
    [Finite M] (hq : CFSG.Open.IsQuasisimple M) (hPS : Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M)) {b e : ℕ}
    (hmodel : StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e) :
    (p = 3 ∧ e = 1 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ b = n ∧ catalogIs (PSimple 3 J) (isLnA n 2)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ e = k ∧ b = 4 ∧ catalogIs (PSimple p J) (isOmPA 3 (2 ^ k))) := by
  rcases hJt with ⟨hp3, n, hodd, hn5, hcat⟩ | ⟨hp3, n, _, hn6, hcat⟩ |
    ⟨n, k, _, hn3, hk1, hk, hkdiv, hcat⟩
  · exact Or.inl (i167CLin_jrigid_aux2 hq hp3 hPS hmodel hodd hn5 hcat)
  · exact (i167CLin_jrigid_aux3 hq hp3 hPS hmodel hn6 hcat).elim
  · exact Or.inr (i167CLin_jrigid_aux4 hq hPS hmodel hn3 hk1 hk hkdiv hcat)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
