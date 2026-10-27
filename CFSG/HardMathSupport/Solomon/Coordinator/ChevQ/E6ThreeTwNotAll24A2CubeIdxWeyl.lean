module

import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIdxRoots
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Roots

private abbrev a2idxW_vec (a0 a1 a2 a3 a4 a5 : ℤ) : Fin Tag.E6.rank → ℤ :=
  ![a0, a1, a2, a3, a4, a5]

private def a2idxW_P : Finset (Fin Tag.E6.rank → ℤ) :=
  {a2idxW_vec 1 0 0 0 0 0, a2idxW_vec 0 0 1 0 0 0, a2idxW_vec 1 0 1 0 0 0,
    a2idxW_vec 0 0 0 0 1 0, a2idxW_vec 0 0 0 0 0 1, a2idxW_vec 0 0 0 0 1 1,
    a2idxW_vec 0 1 0 0 0 0, a2idxW_vec 1 1 2 3 2 1, a2idxW_vec 1 2 2 3 2 1}

private def a2idxW_T : Finset (Fin Tag.E6.rank → ℤ) :=
  {a2idxW_vec 1 0 1 0 0 0, a2idxW_vec 0 0 0 0 1 1, a2idxW_vec 1 2 2 3 2 1}

private theorem a2idxW_add_mem_T : ∀ a ∈ a2idxW_P, ∀ b ∈ a2idxW_P, a + b ∈ a2idxW_P →
    a + b ∈ a2idxW_T := by
  decide +kernel

private theorem a2idxW_T_spec : ∀ t ∈ a2idxW_T, t ∈ a2idxW_P ∧
    ∃ a ∈ a2idxW_P, ∃ b ∈ a2idxW_P, a + b = t := by
  decide +kernel

private theorem a2idxW_pair : ∀ x ∈ a2idxW_P, x ∈ a2idxW_T ∨
    ∃ y ∈ a2idxW_P, x + y ∈ a2idxW_T ∧
      ∀ a ∈ a2idxW_P, ∀ b ∈ a2idxW_P, a + b = x + y → a = x ∨ a = y := by
  decide +kernel

private theorem a2idxW_single_mem : ∀ j : Fin Tag.E6.rank, j ≠ 3 →
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ a2idxW_P := by
  decide +kernel

private theorem a2idxW_theta_mem : a2idxW_vec 1 2 2 3 2 1 ∈ a2idxW_P := by
  decide +kernel

private theorem a2idxW_three_single :
    (3 : ℤ) • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = a2idxW_vec 1 2 2 3 2 1 -
      ((Pi.single 0 1 : Fin Tag.E6.rank → ℤ) + (2 : ℤ) • Pi.single 1 1 + (2 : ℤ) • Pi.single 2 1 +
        (2 : ℤ) • Pi.single 4 1 + Pi.single 5 1) := by
  decide +kernel

private theorem a2idxW_smul_eq_of_sq {G X : Type*} [Group G] [MulAction G X] {u : G} {n : ℕ}
    (hn : Odd n) (hu : u ^ n = 1) {x : X} (h2 : (u * u) • x = x) : u • x = x := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (u * u) ^ m • x = x :=
    (MulAction.stabilizer G x).pow_mem (MulAction.mem_stabilizer_iff.2 h2) m
  have e : u ^ (2 * m + 1) = u * (u * u) ^ m := by rw [pow_succ', pow_mul, sq]
  have h := congrArg (fun g : G => g • x) hu
  simp only [e, mul_smul, hm, one_smul] at h
  exact h

private theorem a2idxW_fix_of_pair {G X : Type*} [Group G] [MulAction G X] {u : G} {n : ℕ}
    (hn : Odd n) (hu : u ^ n = 1) {x y : X} (hx : u • x = x ∨ u • x = y)
    (hy : u • x = y → u • y = x) : u • x = x := by
  rcases hx with h | h
  · exact h
  · exact a2idxW_smul_eq_of_sq hn hu (by rw [mul_smul, h, hy h])

end Roots

section Weyl


private theorem a2idxW_mem_P_iff {γ : Fin Tag.E6.rank → ℤ} :
    γ ∈ a2idxW_P ↔ IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3 ∧ 0 < height (τ := Tag.E6) γ := by
  constructor
  · intro h
    have key : ∀ γ ∈ a2idxW_P, γ ∈ rootFinset Tag.E6 ∧ (3 : ℤ) ∣ γ 3 ∧
        0 < height (τ := Tag.E6) γ := by
      decide +kernel
    obtain ⟨h1, h2, h3⟩ := key γ h
    exact ⟨mem_rootFinset.1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have key : ∀ γ ∈ rootFinset Tag.E6, (3 : ℤ) ∣ γ 3 → 0 < height (τ := Tag.E6) γ →
        γ ∈ a2idxW_P := by
      decide +kernel
    exact key γ (mem_rootFinset.2 h1) h2 h3

private theorem a2idxW_smul_mem_T {u : WeylGroup Tag.E6}
    (hP : ∀ x ∈ a2idxW_P, u • x ∈ a2idxW_P) {t : Fin Tag.E6.rank → ℤ} (ht : t ∈ a2idxW_T) :
    u • t ∈ a2idxW_T := by
  obtain ⟨htP, a, ha, b, hb, rfl⟩ := a2idxW_T_spec t ht
  have h := hP _ htP
  rw [smul_add] at h ⊢
  exact a2idxW_add_mem_T _ (hP a ha) _ (hP b hb) h

private theorem a2idxW_eq_one {u : WeylGroup Tag.E6} {n : ℕ} (hn : Odd n) (hun : u ^ n = 1)
    (hP : ∀ x ∈ a2idxW_P, u • x ∈ a2idxW_P)
    (ht : u • a2idxW_vec 1 0 1 0 0 0 = a2idxW_vec 1 0 1 0 0 0) : u = 1 := by
  have hfixT : ∀ t ∈ a2idxW_T, u • t = t := by
    have h2 := a2idxW_smul_mem_T hP (t := a2idxW_vec 0 0 0 0 1 1) (by decide +kernel)
    have h3 := a2idxW_smul_mem_T hP (t := a2idxW_vec 1 2 2 3 2 1) (by decide +kernel)
    have hne12 : a2idxW_vec 0 0 0 0 1 1 ≠ a2idxW_vec 1 0 1 0 0 0 := by decide +kernel
    have hne13 : a2idxW_vec 1 2 2 3 2 1 ≠ a2idxW_vec 1 0 1 0 0 0 := by decide +kernel
    have hne23 : a2idxW_vec 1 2 2 3 2 1 ≠ a2idxW_vec 0 0 0 0 1 1 := by decide +kernel
    simp only [a2idxW_T, Finset.mem_insert, Finset.mem_singleton] at h2 h3
    have key : u • a2idxW_vec 0 0 0 0 1 1 = a2idxW_vec 0 0 0 0 1 1 ∧
        u • a2idxW_vec 1 2 2 3 2 1 = a2idxW_vec 1 2 2 3 2 1 := by
      rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3
      · exact absurd (smul_left_cancel u (h2.trans ht.symm)) hne12
      · exact absurd (smul_left_cancel u (h2.trans ht.symm)) hne12
      · exact absurd (smul_left_cancel u (h2.trans ht.symm)) hne12
      · exact absurd (smul_left_cancel u (h3.trans ht.symm)) hne13
      · exact absurd (smul_left_cancel u (h3.trans h2.symm)) hne23
      · exact ⟨h2, h3⟩
      · exact absurd (smul_left_cancel u (h3.trans ht.symm)) hne13
      · have h := a2idxW_smul_eq_of_sq hn hun (x := a2idxW_vec 0 0 0 0 1 1)
          (by rw [mul_smul, h2, h3])
        exact absurd (h2.symm.trans h) hne23
      · exact absurd (smul_left_cancel u (h3.trans h2.symm)) hne23
    intro t ht'
    simp only [a2idxW_T, Finset.mem_insert, Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact ht
    · exact key.1
    · exact key.2
  have hfixP : ∀ x ∈ a2idxW_P, u • x = x := by
    intro x hx
    rcases a2idxW_pair x hx with hxT | ⟨y, hy, hxyT, huniq⟩
    · exact hfixT x hxT
    · have hsum : u • x + u • y = x + y := by rw [← smul_add, hfixT _ hxyT]
      refine a2idxW_fix_of_pair hn hun (y := y) (huniq _ (hP x hx) _ (hP y hy) hsum) fun h => ?_
      rw [h] at hsum
      exact add_left_cancel (hsum.trans (add_comm x y))
  refine ext_single fun i => ?_
  rw [one_smul]
  by_cases hi : i = 3
  · subst hi
    have hθ := hfixP _ a2idxW_theta_mem
    have h0 := hfixP _ (a2idxW_single_mem 0 (by decide))
    have h1 := hfixP _ (a2idxW_single_mem 1 (by decide))
    have h2 := hfixP _ (a2idxW_single_mem 2 (by decide))
    have h4 := hfixP _ (a2idxW_single_mem 4 (by decide))
    have h5 := hfixP _ (a2idxW_single_mem 5 (by decide))
    have h3 : (3 : ℤ) • (u • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) =
        (3 : ℤ) • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← smul_comm, a2idxW_three_single, smul_sub, smul_add, smul_add, smul_add, smul_add,
        smul_comm u (2 : ℤ), smul_comm u (2 : ℤ), smul_comm u (2 : ℤ), hθ, h0, h1, h2, h4, h5]
    exact smul_right_injective _ (by norm_num : (3 : ℤ) ≠ 0) h3
  · exact hfixP _ (a2idxW_single_mem i hi)

private theorem a2idxW_align {L : Type} [Field L] {ta : Fin Tag.E6.rank → Lˣ}
    (hw : ∃ w : WeylGroup Tag.E6, kernelRoots (rootCharHom ta) =
      (fun α => w⁻¹ • α) '' {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3}) :
    ∃ v : WeylGroup Tag.E6,
      (∀ α ∈ posRoots (kernelRoots (rootCharHom ta)), v • α ∈ a2idxW_P) ∧
        ∀ γ ∈ a2idxW_P, v⁻¹ • γ ∈ posRoots (kernelRoots (rootCharHom ta)) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hpos⟩ := exists_mul_forall_height_pos (rootCharHom ta) w
  have huχ : u ∈ charStabilizer (rootCharHom ta) := kernelWeylGroup_le hu
  refine ⟨w * u, fun α hα => ?_, fun γ hγ => ?_⟩
  · have h1 : u • α ∈ kernelRoots (rootCharHom ta) := smul_mem_kernelRoots huχ hα.1
    rw [hw] at h1
    obtain ⟨γ, ⟨hr, hd⟩, hγ⟩ := h1
    have hγ' : w⁻¹ • γ = u • α := hγ
    have e : (w * u) • α = γ := by rw [mul_smul, ← hγ', smul_inv_smul]
    have hh := height_smul_pos_of_simpleRoots hpos hα
    rw [e] at hh ⊢
    exact a2idxW_mem_P_iff.2 ⟨hr, hd, hh⟩
  · obtain ⟨hr, hd, hh⟩ := a2idxW_mem_P_iff.1 hγ
    have hk : (w * u)⁻¹ • γ ∈ kernelRoots (rootCharHom ta) := by
      rw [mul_inv_rev, mul_smul]
      refine smul_mem_kernelRoots (inv_mem huχ) ?_
      rw [hw]
      exact ⟨γ, ⟨hr, hd⟩, rfl⟩
    refine ⟨hk, ?_⟩
    rcases IsRoot.height_pos_or_neg hk.1 with h | h
    · exact h
    · exfalso
      have hneg : -((w * u)⁻¹ • γ) ∈ posRoots (kernelRoots (rootCharHom ta)) := by
        refine ⟨⟨IsRoot.neg hk.1, ?_⟩, by rw [height_neg]; linarith⟩
        rw [ofAdd_neg, map_inv, hk.2, inv_one]
      have h' := height_smul_pos_of_simpleRoots hpos hneg
      rw [smul_neg, smul_inv_smul, height_neg] at h'
      linarith

theorem a2cube_card_weylQuotient_dvd_three_of_eq {L : Type} [Field L]
    {ta : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, ta j ^ 3 = 1)
    (hw : ∃ w : WeylGroup Tag.E6, kernelRoots (rootCharHom ta) =
      (fun α => w⁻¹ • α) '' {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3}) :
    Nat.card (↥(rootCharStabilizerSubgroup ta) ⧸
      (kernelReflectionGroup ta).subgroupOf (rootCharStabilizerSubgroup ta)) ∣ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isPGroup_quotient
    Nat.prime_three hap
  let e : kernelPosStabilizer (rootCharHom ta) ≃* (↥(rootCharStabilizerSubgroup ta) ⧸
      (kernelReflectionGroup ta).subgroupOf (rootCharStabilizerSubgroup ta)) :=
    kernelPosStabilizerMulEquiv
  have hΩ : IsPGroup 3 (kernelPosStabilizer (rootCharHom ta)) := hQ.of_equiv e.symm
  rw [← Nat.card_congr e.toEquiv]
  obtain ⟨v, hv1, hv2⟩ := a2idxW_align hw
  have hconj : ∀ ω ∈ kernelPosStabilizer (rootCharHom ta), ∀ x ∈ a2idxW_P,
      (v * ω * v⁻¹) • x ∈ a2idxW_P := by
    intro ω hω x hx
    have h2 : ω • v⁻¹ • x ∈ posRoots (kernelRoots (rootCharHom ta)) := by
      rw [← hω.2]
      exact Set.mem_image_of_mem _ (hv2 x hx)
    rw [mul_smul, mul_smul]
    exact hv1 _ h2
  have ht1 : a2idxW_vec 1 0 1 0 0 0 ∈ a2idxW_T := by decide +kernel
  let f : kernelPosStabilizer (rootCharHom ta) → a2idxW_T := fun ω =>
    ⟨(v * ω * v⁻¹) • a2idxW_vec 1 0 1 0 0 0, a2idxW_smul_mem_T (hconj ω ω.2) ht1⟩
  have hf : Function.Injective f := by
    intro ω ω' h
    have h' : (v * ω * v⁻¹) • a2idxW_vec 1 0 1 0 0 0 =
        (v * ω' * v⁻¹) • a2idxW_vec 1 0 1 0 0 0 := congrArg Subtype.val h
    have hg : (ω' : WeylGroup Tag.E6)⁻¹ * ω ∈ kernelPosStabilizer (rootCharHom ta) :=
      mul_mem (inv_mem ω'.2) ω.2
    obtain ⟨k, hk⟩ := hΩ ⟨_, hg⟩
    have hgk : ((ω' : WeylGroup Tag.E6)⁻¹ * ω) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hu := a2idxW_eq_one (u := v * ((ω' : WeylGroup Tag.E6)⁻¹ * ω) * v⁻¹)
      ((by decide : Odd 3).pow) (by rw [conj_pow, hgk, mul_one, mul_inv_cancel]) (hconj _ hg)
      (by
        have e1 : v * ((ω' : WeylGroup Tag.E6)⁻¹ * ω) * v⁻¹ =
            (v * ω' * v⁻¹)⁻¹ * (v * ω * v⁻¹) := by group
        rw [e1, mul_smul, h', inv_smul_smul])
    rw [conj_eq_one_iff, inv_mul_eq_one] at hu
    exact Subtype.ext hu.symm
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hcard
  have hT3 : a2idxW_T.card = 3 := by decide +kernel
  obtain ⟨k, hk⟩ := hΩ.exists_card_eq
  rw [hT3, hk] at hcard
  rw [hk]
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (Nat.pow_dvd_pow 3 hk1).trans (by norm_num)

end Weyl

section Index


theorem a2cube_card_weylQuotient_dvd_three {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {ta : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, ta j ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom ta)).ncard = 18) :
    Nat.card (↥(rootCharStabilizerSubgroup ta) ⧸
      (kernelReflectionGroup ta).subgroupOf (rootCharStabilizerSubgroup ta)) ∣ 3 :=
  a2cube_card_weylQuotient_dvd_three_of_eq hap (a2cube_exists_weyl_kernelRoots_eq h3 hap h18)

end Index

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
