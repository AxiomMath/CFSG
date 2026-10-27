module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOGenThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOSeven

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem ClO.small_split_eq_one_three_gen (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJ4 : J.card ≤ 4) (hJc : BlockOK K w Jᶜ)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c) :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hJcok := hJc
  obtain ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩ := hJc
  have hJ3 : 3 ≤ J.card := by
    have : ({a, b, c} : Finset (Fin d)) ⊆ J := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
    omega
  have hd := card_compl_add J
  have hcard : ∀ {x y : Fin d}, x ∈ J → y ∈ J → x ≠ y →
      (J ∩ {x, y}).card ≤ 2 ∧ (J \ {x, y}).card ≤ 2 := by
    intro x y hx hy hxy
    refine ⟨?_, by rw [card_sdiff_pair hx hy hxy]; omega⟩
    exact (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_le_two)
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  obtain ⟨hi1, hi2, hi3, hi4⟩ := ClO.cycle_inv_apply hab hac hbc
  have hρJ : ∀ x, (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ x ∈ J ↔ x ∈ J := by
    intro x
    by_cases hxa : x = a
    · subst hxa; rw [hi1]; exact ⟨fun _ => ha, fun _ => hc⟩
    by_cases hxb : x = b
    · subst hxb; rw [hi2]; exact ⟨fun _ => hb, fun _ => ha⟩
    by_cases hxc : x = c
    · subst hxc; rw [hi3]; exact ⟨fun _ => hc, fun _ => hb⟩
    rw [hi4 x hxa hxb hxc]
  have hρ3 := ClO.cycle_cube hab hac hbc
  have hρH := ClO.permGL_cycle_mem (K := K) h2 hw hwab hwac
  have hn₁ := ClO.conj_mem_of_cycle hK hw hRc hρ3 hρJ hρH (M := {a, b}) (M' := {a, c})
    (signGL_pair_mem_derived h2 hw hab hwab) (by
      intro x
      by_cases hxa : x = a
      · subst hxa; rw [hi1]; simp_all
      by_cases hxb : x = b
      · subst hxb; rw [hi2]; simp_all
      by_cases hxc : x = c
      · subst hxc; rw [hi3]; simp_all
      rw [hi4 x hxa hxb hxc]
      simp [hxa, hxc])
  have hn₂ := ClO.conj_mem_of_cycle hK hw hRc hρ3 hρJ hρH (M := {a, c}) (M' := {b, c})
    (signGL_pair_mem_derived h2 hw hac hwac) (by
      intro x
      by_cases hxa : x = a
      · subst hxa; rw [hi1]; simp_all
      by_cases hxb : x = b
      · subst hxb; rw [hi2]; simp_all
      by_cases hxc : x = c
      · subst hxc; rw [hi3]; simp_all
      rw [hi4 x hxa hxb hxc]
      simp [hxb, hxc])
  have h₁₂ : signMat K {a, c} * signMat K {b, c} = signMat K {a, b} := by
    have := signMat_pair_mul (K := K) (Ne.symm hac) (Ne.symm hbc) hab
    rwa [Finset.pair_comm c a, Finset.pair_comm c b] at this
  have hd0 : 0 < d := Fin.pos a
  refine ClO.eq_one_three_gen h3 hK hd0 hw hker hRodd hRi hsurj (I := Jᶜ)
    (M₁ := {a, c}) (M₂ := {b, c}) (M₃ := {a, b})
    (fun g hg => (ClO.iso_of_blockOK hK hw hker hinj (Or.inr rfl) hJcok hRodd hRi hRc
      hg).2.2) hn₁ hn₂ h₁₂ ?_ (fun _ _ => Or.inl fun x hx => hx)
  · rintro M (rfl | rfl | rfl)
    · exact hcard ha hc hac
    · exact hcard hb hc hbc
    · exact hcard ha hb hab

theorem ClO.seven_split_eq_one_three_gen (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJ4 : J.card ≤ 4) (hJc4 : Jᶜ.card ≤ 4)
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
  have hd0 : 0 < d := Fin.pos a
  refine ClO.eq_one_three_gen h3 hK hd0 hw hker hRodd hRi hsurj (I := ∅)
    (M₁ := {a, c} ∪ {a', c'}) (M₂ := {b, c} ∪ {b', c'}) (M₃ := {a, b} ∪ {a', b'})
    (fun _ _ x hx => absurd hx (Finset.notMem_empty x)) hn₁ hn₂ hprod' ?_ ?_
  · rintro M (rfl | rfl | rfl)
    · exact ⟨(hpiece ha hc ha' hc' hac hac').1, (hpiece ha hc ha' hc' hac hac').2.1⟩
    · exact ⟨(hpiece hb hc hb' hc' hbc hbc').1, (hpiece hb hc hb' hc' hbc hbc').2.1⟩
    · exact ⟨(hpiece ha hb ha' hb' hab hab').1, (hpiece ha hb ha' hb' hab hab').2.1⟩
  · rintro M (rfl | rfl | rfl)
    · exact Or.inr (hpiece ha hc ha' hc' hac hac').2.2
    · exact Or.inr (hpiece hb hc hb' hc' hbc hbc').2.2
    · exact Or.inr (hpiece ha hb ha' hb' hab hab').2.2

end CFSG.ComponentClassification.Foote5.OddLieCore
