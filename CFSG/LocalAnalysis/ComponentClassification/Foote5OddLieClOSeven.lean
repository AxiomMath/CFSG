module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOThree

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.seven_mem_facts {J : Finset (Fin d)} {a b c a' b' c' : Fin d} (ha : a ∈ J)
    (hb : b ∈ J) (hc : c ∈ J) (ha' : a' ∈ Jᶜ) (hb' : b' ∈ Jᶜ) (hc' : c' ∈ Jᶜ) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c')
    (f : Fin d → Fin d)
    (hf : ∀ x, f x = if x = a then c else if x = b then a else if x = c then b
      else if x = a' then c' else if x = b' then a' else if x = c' then b' else x) :
    (∀ x, f x ∈ J ↔ x ∈ J) ∧
      (∀ x, x ∈ ({a, c} ∪ {a', c'} : Finset (Fin d)) ↔
        ¬ (f x ∈ ({a, b} ∪ {a', b'} : Finset (Fin d)) ↔
          x ∈ ({a, b} ∪ {a', b'} : Finset (Fin d)))) ∧
      (∀ x, x ∈ ({b, c} ∪ {b', c'} : Finset (Fin d)) ↔
        ¬ (f x ∈ ({a, c} ∪ {a', c'} : Finset (Fin d)) ↔
          x ∈ ({a, c} ∪ {a', c'} : Finset (Fin d)))) := by
  have hne : ∀ {x x' : Fin d}, x ∈ J → x' ∈ Jᶜ → x ≠ x' := fun hx hx' e =>
    Finset.mem_compl.1 hx' (e ▸ hx)
  have e1 := hne ha ha'
  have e2 := hne ha hb'
  have e3 := hne ha hc'
  have e4 := hne hb ha'
  have e5 := hne hb hb'
  have e6 := hne hb hc'
  have e7 := hne hc ha'
  have e8 := hne hc hb'
  have e9 := hne hc hc'
  have ha'J : a' ∉ J := Finset.mem_compl.1 ha'
  have hb'J : b' ∉ J := Finset.mem_compl.1 hb'
  have hc'J : c' ∉ J := Finset.mem_compl.1 hc'
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;> rw [hf x] <;> clear hf <;>
    split_ifs <;> subst_vars <;> simp_all [eq_comm]

variable [Finite K]

theorem ClO.seven_normalizers (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c)
    {a' b' c' : Fin d} (ha' : a' ∈ Jᶜ) (hb' : b' ∈ Jᶜ) (hc' : c' ∈ Jᶜ) (hab' : a' ≠ b')
    (hac' : a' ≠ c') (hbc' : b' ≠ c') (hwab' : w a' = w b') (hwac' : w a' = w c')
    (hm₁ : signGL K ({a, b} ∪ {a', b'}) ∈ matrixDerived (oQ (diagGL hw)))
    (hm₂ : signGL K ({a, c} ∪ {a', c'}) ∈ matrixDerived (oQ (diagGL hw))) :
    (∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw ({a, c} ∪ {a', c'})) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw ({a, c} ∪ {a', c'})))⁻¹ ∈ Ro) ∧
    (∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw ({b, c} ∪ {b', c'})) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw ({b, c} ∪ {b', c'})))⁻¹ ∈ Ro) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hne : ∀ {x x' : Fin d}, x ∈ J → x' ∈ Jᶜ → x ≠ x' := fun hx hx' e =>
    Finset.mem_compl.1 hx' (e ▸ hx)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have hba' := hab'.symm
  have hca' := hac'.symm
  have hcb' := hbc'.symm
  have e1 := hne ha ha'
  have e2 := hne ha hb'
  have e3 := hne ha hc'
  have e4 := hne hb ha'
  have e5 := hne hb hb'
  have e6 := hne hb hc'
  have e7 := hne hc ha'
  have e8 := hne hc hb'
  have e9 := hne hc hc'
  have e1' := e1.symm
  have e2' := e2.symm
  have e3' := e3.symm
  have e4' := e4.symm
  have e5' := e5.symm
  have e6' := e6.symm
  have e7' := e7.symm
  have e8' := e8.symm
  have e9' := e9.symm
  obtain ⟨i1, i2, i3, i4⟩ := ClO.cycle_inv_apply hab hac hbc
  obtain ⟨j1, j2, j3, j4⟩ := ClO.cycle_inv_apply hab' hac' hbc'
  obtain ⟨f1, f2, f3, f4⟩ := ClO.cycle_apply hab hac hbc
  obtain ⟨g1, g2, g3, g4⟩ := ClO.cycle_apply hab' hac' hbc'
  have hc1 := ClO.cycle_cube hab hac hbc
  have hc2 := ClO.cycle_cube hab' hac' hbc'
  have hm1 := ClO.permGL_cycle_mem (K := K) h2 hw hwab hwac
  have hm2 := ClO.permGL_cycle_mem (K := K) h2 hw hwab' hwac'
  generalize ⁅Equiv.swap a b, Equiv.swap a c⁆ = ρ₁ at i1 i2 i3 i4 f1 f2 f3 f4 hc1 hm1
  generalize ⁅Equiv.swap a' b', Equiv.swap a' c'⁆ = ρ₂ at j1 j2 j3 j4 g1 g2 g3 g4 hc2 hm2
  have hval : ∀ x, (ρ₁ * ρ₂)⁻¹ x = if x = a then c else if x = b then a else if x = c then b
      else if x = a' then c' else if x = b' then a' else if x = c' then b' else x := by
    intro x
    rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply]
    by_cases hxa : x = a
    · subst hxa; rw [i1, j4 c e7 e8 e9]; simp
    by_cases hxb : x = b
    · subst hxb; rw [i2, j4 a e1 e2 e3]; simp [hxa]
    by_cases hxc : x = c
    · subst hxc; rw [i3, j4 b e4 e5 e6]; simp [hxa, hxb]
    rw [i4 x hxa hxb hxc]
    by_cases hxa' : x = a'
    · subst hxa'; rw [j1]; simp [hxa, hxb, hxc]
    by_cases hxb' : x = b'
    · subst hxb'; rw [j2]; simp [hxa, hxb, hxc, hxa']
    by_cases hxc' : x = c'
    · subst hxc'; rw [j3]; simp [hxa, hxb, hxc, hxa', hxb']
    rw [j4 x hxa' hxb' hxc']
    simp [hxa, hxb, hxc, hxa', hxb', hxc']
  have hcomm : ρ₁ * ρ₂ = ρ₂ * ρ₁ := by
    ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hx : x = a ∨ x = b ∨ x = c
    · have hx2 : ρ₂ x = x := by
        rcases hx with rfl | rfl | rfl
        · exact g4 _ e1 e2 e3
        · exact g4 _ e4 e5 e6
        · exact g4 _ e7 e8 e9
      rw [hx2]
      rcases hx with rfl | rfl | rfl
      · rw [f1, g4 _ e4 e5 e6]
      · rw [f2, g4 _ e7 e8 e9]
      · rw [f3, g4 _ e1 e2 e3]
    · push Not at hx
      obtain ⟨hxa, hxb, hxc⟩ := hx
      rw [f4 x hxa hxb hxc]
      by_cases hxa' : x = a'
      · subst hxa'; rw [g1, f4 _ e2' e5' e8']
      by_cases hxb' : x = b'
      · subst hxb'; rw [g2, f4 _ e3' e6' e9']
      by_cases hxc' : x = c'
      · subst hxc'; rw [g3, f4 _ e1' e4' e7']
      rw [g4 x hxa' hxb' hxc', f4 x hxa hxb hxc]
  have hρ3 : (ρ₁ * ρ₂) ^ 3 = 1 := by
    rw [(show Commute ρ₁ ρ₂ from hcomm).mul_pow, hc1, hc2, one_mul]
  have hρH : permGL K d (ρ₁ * ρ₂) ∈ matrixDerived (oQ (diagGL hw)) := by
    rw [map_mul]
    exact mul_mem hm1 hm2
  obtain ⟨hρJ, hM₁, hM₂⟩ := ClO.seven_mem_facts ha hb hc ha' hb' hc' hab hac hbc hab' hac'
    hbc' _ hval
  exact ⟨ClO.conj_mem_of_cycle hK hw hRc hρ3 hρJ hρH (M := {a, b} ∪ {a', b'})
    (M' := {a, c} ∪ {a', c'}) hm₁ hM₁, ClO.conj_mem_of_cycle hK hw hRc hρ3 hρJ hρH
      (M := {a, c} ∪ {a', c'}) (M' := {b, c} ∪ {b', c'}) hm₂ hM₂⟩

theorem ClO.seven_split_eq_one_three (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJd : 2 * J.card ≠ d) (hd8 : d ≠ 8) (hJ4 : J.card ≤ 4)
    (hJc4 : Jᶜ.card ≤ 4)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c)
    {a' b' c' : Fin d} (ha' : a' ∈ Jᶜ) (hb' : b' ∈ Jᶜ) (hc' : c' ∈ Jᶜ) (hab' : a' ≠ b')
    (hac' : a' ≠ c') (hbc' : b' ≠ c') (hwab' : w a' = w b') (hwac' : w a' = w c') :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hdisj : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ →
      Disjoint ({x, y} : Finset (Fin d)) {x', y'} := by
    intro x y x' y' hx hy hx' hy'
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    have hzJ : z ∈ J := by rcases hz with rfl | rfl <;> assumption
    have hzJc : z ∈ Jᶜ := by rcases hz' with rfl | rfl <;> assumption
    exact Finset.mem_compl.1 hzJc hzJ
  have hmem : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ → x ≠ y → x' ≠ y' →
      w x = w y → w x' = w y' →
      signGL K ({x, y} ∪ {x', y'}) ∈ matrixDerived (oQ (diagGL hw)) := by
    intro x y x' y' hx hy hx' hy' hxy hxy' hw1 hw2
    have e : signGL K {x, y} * signGL K {x', y'} = signGL K ({x, y} ∪ {x', y'}) :=
      Units.ext (signMat_mul_of_disjoint (hdisj hx hy hx' hy'))
    rw [← e]
    exact mul_mem (signGL_pair_mem_derived h2 hw hxy hw1) (signGL_pair_mem_derived h2 hw hxy' hw2)
  have hprod : signMat K ({a, b} ∪ {a', b'}) * signMat K ({a, c} ∪ {a', c'}) =
      signMat K ({b, c} ∪ {b', c'}) := by
    rw [← signMat_mul_of_disjoint (hdisj ha hb ha' hb'),
      ← signMat_mul_of_disjoint (hdisj ha hc ha' hc'),
      ← signMat_mul_of_disjoint (hdisj hb hc hb' hc'), ← signMat_pair_mul hab hac hbc,
      ← signMat_pair_mul hab' hac' hbc']
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, signMat_mul_comm {a', b'} {a, c}]
  have hpiece : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ → x ≠ y →
      x' ≠ y' → (J ∩ ({x, y} ∪ {x', y'})).card ≤ 2 ∧ (J \ ({x, y} ∪ {x', y'})).card ≤ 2 ∧
        (Jᶜ ∩ ({x, y} ∪ {x', y'})).card ≤ 2 ∧ (Jᶜ \ ({x, y} ∪ {x', y'})).card ≤ 2 := by
    intro x y x' y' hx hy hx' hy' hxy hxy'
    have hJM : J ∩ ({x, y} ∪ {x', y'}) ⊆ {x, y} := by
      intro z hz
      rw [Finset.mem_inter, Finset.mem_union] at hz
      rcases hz.2 with h | h
      · exact h
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact Finset.mem_compl.1 hx' hz.1
        · exact Finset.mem_compl.1 hy' hz.1
    have hJcM : Jᶜ ∩ ({x, y} ∪ {x', y'}) ⊆ {x', y'} := by
      intro z hz
      rw [Finset.mem_inter, Finset.mem_union] at hz
      rcases hz.2 with h | h
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact Finset.mem_compl.1 hz.1 hx
        · exact Finset.mem_compl.1 hz.1 hy
      · exact h
    have hJs : J \ ({x, y} ∪ {x', y'}) ⊆ J \ {x, y} :=
      Finset.sdiff_subset_sdiff (le_refl _) Finset.subset_union_left
    have hJcs : Jᶜ \ ({x, y} ∪ {x', y'}) ⊆ Jᶜ \ {x', y'} :=
      Finset.sdiff_subset_sdiff (le_refl _) Finset.subset_union_right
    refine ⟨(Finset.card_le_card hJM).trans Finset.card_le_two,
      (Finset.card_le_card hJs).trans ?_, (Finset.card_le_card hJcM).trans Finset.card_le_two,
      (Finset.card_le_card hJcs).trans ?_⟩
    · have hJ3 : 3 ≤ J.card := by
        have : ({a, b, c} : Finset (Fin d)) ⊆ J := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card this
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
        omega
      rw [card_sdiff_pair hx hy hxy]
      omega
    · rw [card_sdiff_pair hx' hy' hxy']
      omega
  obtain ⟨hn₁, hn₂⟩ := ClO.seven_normalizers hK hw hRc ha hb hc hab hac hbc hwab hwac ha' hb'
    hc' hab' hac' hbc' hwab' hwac' (hmem ha hb ha' hb' hab hab' hwab hwab')
    (hmem ha hc ha' hc' hac hac' hwac hwac')
  have hprod' : signMat K ({a, c} ∪ {a', c'}) * signMat K ({b, c} ∪ {b', c'}) =
      signMat K ({a, b} ∪ {a', b'}) := by
    rw [← hprod, ← Matrix.mul_assoc, signMat_mul_comm _ ({a, b} ∪ {a', b'}), Matrix.mul_assoc,
      signMat_mul_self, Matrix.mul_one]
  refine ClO.eq_one_three_of_sets h3 hK hw hker hRodd hRi hsurj (I := ∅)
    (M₁ := {a, c} ∪ {a', c'}) (M₂ := {b, c} ∪ {b', c'}) (M₃ := {a, b} ∪ {a', b'}) hJd
    (fun _ _ x hx => absurd hx (Finset.notMem_empty x)) hn₁ hn₂ hprod' ?_ ?_ ?_
  · rintro M (rfl | rfl | rfl)
    · rw [Finset.card_union_of_disjoint (hdisj ha hc ha' hc'), Finset.card_pair hac,
        Finset.card_pair hac']
      omega
    · rw [Finset.card_union_of_disjoint (hdisj hb hc hb' hc'), Finset.card_pair hbc,
        Finset.card_pair hbc']
      omega
    · rw [Finset.card_union_of_disjoint (hdisj ha hb ha' hb'), Finset.card_pair hab,
        Finset.card_pair hab']
      omega
  · rintro M (rfl | rfl | rfl)
    · exact ⟨(hpiece ha hc ha' hc' hac hac').1, (hpiece ha hc ha' hc' hac hac').2.1⟩
    · exact ⟨(hpiece hb hc hb' hc' hbc hbc').1, (hpiece hb hc hb' hc' hbc hbc').2.1⟩
    · exact ⟨(hpiece ha hb ha' hb' hab hab').1, (hpiece ha hb ha' hb' hab hab').2.1⟩
  · rintro M (rfl | rfl | rfl)
    · exact Or.inr (hpiece ha hc ha' hc' hac hac').2.2
    · exact Or.inr (hpiece hb hc hb' hc' hbc hbc').2.2
    · exact Or.inr (hpiece ha hb ha' hb' hab hab').2.2

end CFSG.ComponentClassification.Foote5.OddLieCore
