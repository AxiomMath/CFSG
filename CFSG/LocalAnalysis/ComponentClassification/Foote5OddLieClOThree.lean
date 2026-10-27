module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOCycle
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOSplit

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self
  compInd commute_compInd_iff commute_signMat_iff eq_bot_of_four_group)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.cycle_apply {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅Equiv.swap a b, Equiv.swap a c⁆ a = b ∧ ⁅Equiv.swap a b, Equiv.swap a c⁆ b = c ∧
      ⁅Equiv.swap a b, Equiv.swap a c⁆ c = a ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → ⁅Equiv.swap a b, Equiv.swap a c⁆ x = x := by
  refine ⟨?_, ?_, ?_, fun x hxa hxb hxc => ?_⟩ <;>
    simp [commutatorElement_def, Equiv.swap_apply_def, hab.symm, hac.symm, hbc.symm, *]

theorem ClO.cycle_inv_apply {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ a = c ∧ (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ b = a ∧
      (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ c = b ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ x = x := by
  refine ⟨?_, ?_, ?_, fun x hxa hxb hxc => ?_⟩ <;>
    simp [commutatorElement_def, Equiv.swap_apply_def, hab.symm, hac.symm, hbc.symm, *]

theorem ClO.cycle_cube {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅Equiv.swap a b, Equiv.swap a c⁆ ^ 3 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := ClO.cycle_apply hab hac hbc
  ext x
  by_cases hxa : x = a
  · subst hxa; simp [pow_succ, Equiv.Perm.mul_apply, h1, h2, h3]
  by_cases hxb : x = b
  · subst hxb; simp [pow_succ, Equiv.Perm.mul_apply, h1, h2, h3]
  by_cases hxc : x = c
  · subst hxc; simp [pow_succ, Equiv.Perm.mul_apply, h1, h2, h3]
  simp [pow_succ, Equiv.Perm.mul_apply, h4 x hxa hxb hxc]

variable [Finite K]

theorem ClO.eq_one_three_of_sets (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J I M₁ M₂ M₃ : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJd : 2 * J.card ≠ d)
    (hiso : ∀ g : similarityPairs (oQ (diagGL hw)), oκ _ g ∈ Ro →
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0)
    (hn₁ : ∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₁) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₁))⁻¹ ∈ Ro)
    (hn₂ : ∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₂) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₂))⁻¹ ∈ Ro)
    (h₁₂ : signMat K M₁ * signMat K M₂ = signMat K M₃)
    (hMd : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → 2 * M.card ≠ d)
    (hJM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → (J ∩ M).card ≤ 2 ∧ (J \ M).card ≤ 2)
    (hJcM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) →
      (∀ x ∈ Jᶜ, x ∈ I) ∨ ((Jᶜ ∩ M).card ≤ 2 ∧ (Jᶜ \ M).card ≤ 2)) :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Finite Ro := inferInstance
  have hsq : ∀ M : Finset (Fin d), oκ (oQ (diagGL hw)) (sgnPair h2 hw M) *
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) = 1 := by
    intro M
    rw [← map_mul, sgnPair_mul_self, map_one]
  have hC : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → ∀ y ∈ Ro,
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) * y = y * oκ (oQ (diagGL hw)) (sgnPair h2 hw M) →
      y = 1 := by
    intro M hM y hy hcomm
    have hodd := ClSp.odd_orderOf_of_mem hRodd hy
    obtain ⟨g, rfl⟩ := hsurj y hy
    have hDJ := commute_sign_of_commute h2 hw hker hJd (hRi _ hy)
    have hDM := commute_sign_of_commute h2 hw hker (hMd M hM) hcomm.symm
    exact eq_one_of_blocks_three h3 h2 hw hodd (exists_block_of_commute h2 hDJ hDM
      (hiso g hy) (hJM M hM) (hJcM M hM))
  have hRb : Ro = ⊥ := eq_bot_of_four_group (hsq M₁) (hsq M₂) hn₁ hn₂
    (hC M₁ (Or.inl rfl)) (hC M₂ (Or.inr (Or.inl rfl))) (by
      rw [← map_mul, sgnPair_mul h2 hw M₁ M₂ h₁₂]
      exact hC M₃ (Or.inr (Or.inr rfl)))
  intro y hy
  rw [hRb] at hy
  exact mem_bot.1 hy

theorem ClO.small_split_eq_one_three (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
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
    (hJd : 2 * J.card ≠ d) (hJ4 : J.card ≤ 4) (hJc : BlockOK K w Jᶜ)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c) :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
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
  refine ClO.eq_one_three_of_sets h3 hK hw hker hRodd hRi hsurj (I := Jᶜ) (M₁ := {a, c})
    (M₂ := {b, c}) (M₃ := {a, b}) hJd
    (fun g hg => (ClO.split_core hK hw hker hinj hJd (Or.inr rfl) hI3 hIexc hI₀ hI₀3 hI₀w hI₀c
      hRodd hRi hRc hg).2.2) hn₁ hn₂ h₁₂ ?_ ?_ (fun _ _ => Or.inl fun x hx => hx)
  · rintro M (rfl | rfl | rfl) <;> rw [Finset.card_pair (by assumption)] <;> omega
  · rintro M (rfl | rfl | rfl)
    · exact hcard ha hc hac
    · exact hcard hb hc hbc
    · exact hcard ha hb hab

end CFSG.ComponentClassification.Foote5.OddLieCore
