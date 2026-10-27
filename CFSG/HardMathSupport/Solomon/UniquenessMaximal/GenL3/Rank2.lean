module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_16FieldMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCL3
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

theorem mem_c25Fix_zpowers {Y : Type*} [Group Y] (a : MulAut Y) (y : Y) :
    y ∈ c25Fix (Subgroup.zpowers a) ↔ a y = y := by
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h α hα
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hα
    have key : ∀ n : ℤ, (a ^ n) y = y := by
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ k ih =>
        rw [zpow_add_one, MulAut.mul_apply, h]
        exact ih
      | pred k ih =>
        have h' : a⁻¹ y = y := by
          conv_lhs => rw [← h]
          simp
        rw [zpow_sub_one, MulAut.mul_apply, h']
        exact ih
    exact key n

theorem fixedSub_le_c25Fix_zpowers {Y : Type*} [Group Y] (a : MulAut Y) :
    Lemma512Ns.fixedSub a ≤ c25Fix (Subgroup.zpowers a) :=
  fun y hy => (mem_c25Fix_zpowers a y).2 hy

theorem gen_card_nine {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hL : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 F)))
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hb : ∃ α ∈ A, α ≠ 1 ∧ ¬ IsInnDiagThree α) :
    ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S := by
  have hT : IsThreeType Y := Or.inl hL
  obtain ⟨hF1, hF2⟩ := field3Structure_holds Y hY hT
  obtain ⟨b, hbA, hb1, hbn⟩ := hb
  have hb3 : b ^ 3 = 1 := hA.2 b hbA
  have hbF : IsFieldAutThree b := (hF1 b hb3).resolve_left hbn
  obtain ⟨x, hxA, hxD, hx1⟩ : ∃ x ∈ A, IsInnDiagThree x ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ α ∈ A, IsFieldAutThree α := by
      intro α hα
      by_cases h1 : α = 1
      · exact Or.inl h1
      · have h3 : α ^ 3 = 1 := by
          exact hA.2 α hα
        exact (hF1 α h3).resolve_left fun hD => h1 (hcon α hα hD)
    have := hF2 A hA hall
    omega
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hbx : b * x = x * b := by
    have := hA.1.is_comm.comm ⟨b, hbA⟩ ⟨x, hxA⟩
    simpa using congrArg Subtype.val this
  have hgen := bglFieldGenerationThreeL_holds Y hY hL b x hbF hb1 hb3 hxD hx1 hx3 hbx
  have hxinv : x ^ 2 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
  have hne : ∀ i : ℕ, i < 3 → b * x ^ i ≠ 1 := by
    intro i hi
    interval_cases i
    · simpa using hb1
    · intro h
      apply hbn
      have : b = x⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact i2326s_isInnDiagThree_inv hxD
    · intro h
      apply hbn
      rw [pow_two] at h
      have h' : b = (x * x)⁻¹ := eq_inv_of_mul_eq_one_left h
      have : (x * x)⁻¹ = x := by
        rw [← pow_two, hxinv, inv_inv]
      rw [h', this]
      exact hxD
  refine hgen.trans (iSup₂_le fun i hi => ?_)
  have hg3 : (b * x ^ i) ^ 3 = 1 := by
    rw [(show Commute b (x ^ i) from (Commute.pow_right (show Commute b x from hbx) i)).mul_pow,
      hb3, one_mul, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (b * x ^ i) = 3 := orderOf_eq_prime hg3 (hne i hi)
  have hSA : Subgroup.zpowers (b * x ^ i) ≤ A :=
    Subgroup.zpowers_le.2 (A.mul_mem hbA (A.pow_mem hxA i))
  have hcard : Nat.card A ≤ 3 * Nat.card (Subgroup.zpowers (b * x ^ i)) := by
    rw [Nat.card_zpowers, hord, h9]
  exact le_iSup₂_of_le (Subgroup.zpowers (b * x ^ i)) ⟨hSA, hcard⟩
    (fixedSub_le_c25Fix_zpowers _)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
