module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcTw
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIdxRoots
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Classes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*}
  [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

private theorem rootReflection_smul_mem_componentRoots_kd264e6 {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) {i : KernelComponent χ} {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ componentRoots χ i) : rootReflection γ • δ ∈ componentRoots χ i := by
  by_cases h0 : iform γ δ = 0
  · rw [rootReflection_smul_of_iform_eq_zero hγ.1 h0]
    exact hδ
  · have hk : rootReflection γ • δ ∈ kernelRoots χ :=
      smul_mem_kernelRoots (rootReflection_mem_charStabilizer hγ) hδ.1
    have h1 : iform (rootReflection γ • δ) γ ≠ 0 := by
      have e := iform_smul (rootReflection γ) δ γ
      rw [rootReflection_smul_self hγ.1, ← neg_one_smul ℤ γ, iform_smul_right] at e
      intro h
      apply h0
      rw [iform_comm, ← e, h, mul_zero]
    refine ⟨hk, ?_⟩
    have e1 : (⟦⟨_, hk⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγ⟩⟧ := mk_eq_of_iform_ne_zero h1
    have e2 : (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) = ⟦⟨δ, hδ.1⟩⟧ := mk_eq_of_iform_ne_zero h0
    exact e1.trans (e2.trans hδ.2)

private theorem image_componentRoots_of_mem_kernelWeylGroup_kd264e6 {u : WeylGroup τ}
    (hu : u ∈ kernelWeylGroup χ) (i : KernelComponent χ) :
    (fun α => u • α) '' componentRoots χ i = componentRoots χ i := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, j, hα, rfl⟩ := hx
    rw [conj_simple_eq_rootReflection]
    refine Set.Subset.antisymm ?_ fun δ hδ => ?_
    · rintro _ ⟨δ, hδ, rfl⟩
      exact rootReflection_smul_mem_componentRoots_kd264e6 hα hδ
    · refine ⟨rootReflection (w • (Pi.single j 1 : Fin τ.rank → ℤ)) • δ,
        rootReflection_smul_mem_componentRoots_kd264e6 hα hδ, ?_⟩
      simp only [smul_smul, rootReflection_mul_self hα.1, one_smul]
  | one => simp
  | mul x y _ _ hx hy =>
    have e : (fun α : Fin τ.rank → ℤ => (x * y) • α) =
        (fun α : Fin τ.rank → ℤ => x • α) ∘ (fun α : Fin τ.rank → ℤ => y • α) :=
      funext fun α => mul_smul x y α
    rw [e, Set.image_comp, hy, hx]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [Set.image_image]
    simp

end Classes

section A2Cube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped Matrix

private abbrev a2v_kd264e6 (a0 a1 a2 a3 a4 a5 : ℤ) : Fin Tag.E6.rank → ℤ :=
  ![a0, a1, a2, a3, a4, a5]

private def a2P_kd264e6 : Finset (Fin Tag.E6.rank → ℤ) :=
  {a2v_kd264e6 1 0 0 0 0 0, a2v_kd264e6 0 0 1 0 0 0, a2v_kd264e6 1 0 1 0 0 0,
    a2v_kd264e6 0 0 0 0 1 0, a2v_kd264e6 0 0 0 0 0 1, a2v_kd264e6 0 0 0 0 1 1,
    a2v_kd264e6 0 1 0 0 0 0, a2v_kd264e6 1 1 2 3 2 1, a2v_kd264e6 1 2 2 3 2 1}

private def a2T_kd264e6 : Finset (Fin Tag.E6.rank → ℤ) :=
  {a2v_kd264e6 1 0 1 0 0 0, a2v_kd264e6 0 0 0 0 1 1, a2v_kd264e6 1 2 2 3 2 1}

private theorem a2_add_mem_T_kd264e6 : ∀ a ∈ a2P_kd264e6, ∀ b ∈ a2P_kd264e6,
    a + b ∈ a2P_kd264e6 → a + b ∈ a2T_kd264e6 := by
  decide +kernel

private theorem a2_T_spec_kd264e6 : ∀ t ∈ a2T_kd264e6, t ∈ a2P_kd264e6 ∧
    ∃ a ∈ a2P_kd264e6, ∃ b ∈ a2P_kd264e6, a + b = t := by
  decide +kernel

private theorem a2_pair_kd264e6 : ∀ x ∈ a2P_kd264e6, x ∈ a2T_kd264e6 ∨
    ∃ y ∈ a2P_kd264e6, x + y ∈ a2T_kd264e6 ∧
      ∀ a ∈ a2P_kd264e6, ∀ b ∈ a2P_kd264e6, a + b = x + y → a = x ∨ a = y := by
  decide +kernel

private theorem a2_single_mem_kd264e6 : ∀ j : Fin Tag.E6.rank, j ≠ 3 →
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ a2P_kd264e6 := by
  decide +kernel

private theorem a2_theta_mem_kd264e6 : a2v_kd264e6 1 2 2 3 2 1 ∈ a2P_kd264e6 := by
  decide +kernel

private theorem a2_three_single_kd264e6 :
    (3 : ℤ) • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = a2v_kd264e6 1 2 2 3 2 1 -
      ((Pi.single 0 1 : Fin Tag.E6.rank → ℤ) + (2 : ℤ) • Pi.single 1 1 + (2 : ℤ) • Pi.single 2 1 +
        (2 : ℤ) • Pi.single 4 1 + Pi.single 5 1) := by
  decide +kernel

private theorem a2_factA_kd264e6 : ∀ x ∈ a2P_kd264e6, ∃ t ∈ a2T_kd264e6, iform x t ≠ 0 := by
  decide +kernel

private theorem a2_factB_kd264e6 : ∀ x ∈ a2P_kd264e6, ∀ y ∈ a2P_kd264e6, iform x y ≠ 0 →
    ∀ t ∈ a2T_kd264e6, (iform x t = 0 ↔ iform y t = 0) := by
  decide +kernel

private theorem a2_factC_kd264e6 : ∀ s ∈ a2T_kd264e6, ∀ s' ∈ a2T_kd264e6, iform s s' ≠ 0 →
    s = s' := by
  decide +kernel

private theorem smul_eq_of_sq_kd264e6 {G X : Type*} [Group G] [MulAction G X] {u : G} {n : ℕ}
    (hn : Odd n) (hu : u ^ n = 1) {x : X} (h2 : (u * u) • x = x) : u • x = x := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (u * u) ^ m • x = x :=
    (MulAction.stabilizer G x).pow_mem (MulAction.mem_stabilizer_iff.2 h2) m
  have e : u ^ (2 * m + 1) = u * (u * u) ^ m := by rw [pow_succ', pow_mul, sq]
  have h := congrArg (fun g : G => g • x) hu
  simp only [e, mul_smul, hm, one_smul] at h
  exact h

private theorem fix_of_pair_kd264e6 {G X : Type*} [Group G] [MulAction G X] {u : G} {n : ℕ}
    (hn : Odd n) (hu : u ^ n = 1) {x y : X} (hx : u • x = x ∨ u • x = y)
    (hy : u • x = y → u • y = x) : u • x = x := by
  rcases hx with h | h
  · exact h
  · exact smul_eq_of_sq_kd264e6 hn hu (by rw [mul_smul, h, hy h])

private theorem fix_two_of_fix_one_kd264e6 {G X : Type*} [Group G] [MulAction G X] {u : G}
    {n : ℕ} (hn : Odd n) (hun : u ^ n = 1) {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : u • b = a ∨ u • b = b ∨ u • b = c) (hc : u • c = a ∨ u • c = b ∨ u • c = c)
    (ha : u • a = a) : u • b = b ∧ u • c = c := by
  rcases hb with hb | hb | hb
  · exact absurd (smul_left_cancel u (hb.trans ha.symm)) (Ne.symm hab)
  · refine ⟨hb, ?_⟩
    rcases hc with hc | hc | hc
    · exact absurd (smul_left_cancel u (hc.trans ha.symm)) (Ne.symm hac)
    · exact absurd (smul_left_cancel u (hc.trans hb.symm)) (Ne.symm hbc)
    · exact hc
  · exfalso
    rcases hc with hc | hc | hc
    · exact absurd (smul_left_cancel u (hc.trans ha.symm)) (Ne.symm hac)
    · have h := smul_eq_of_sq_kd264e6 hn hun (x := b) (by rw [mul_smul, hb, hc])
      exact hbc (h.symm.trans hb)
    · exact hbc (smul_left_cancel u (hb.trans hc.symm))


private theorem a2_mem_P_iff_kd264e6 {γ : Fin Tag.E6.rank → ℤ} :
    γ ∈ a2P_kd264e6 ↔ IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3 ∧ 0 < height (τ := Tag.E6) γ := by
  constructor
  · intro h
    have key : ∀ γ ∈ a2P_kd264e6, γ ∈ rootFinset Tag.E6 ∧ (3 : ℤ) ∣ γ 3 ∧
        0 < height (τ := Tag.E6) γ := by
      decide +kernel
    obtain ⟨h1, h2, h3⟩ := key γ h
    exact ⟨mem_rootFinset.1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have key : ∀ γ ∈ rootFinset Tag.E6, (3 : ℤ) ∣ γ 3 → 0 < height (τ := Tag.E6) γ →
        γ ∈ a2P_kd264e6 := by
      decide +kernel
    exact key γ (mem_rootFinset.2 h1) h2 h3

private theorem a2_smul_mem_T_kd264e6 {u : WeylGroup Tag.E6}
    (hP : ∀ x ∈ a2P_kd264e6, u • x ∈ a2P_kd264e6) {t : Fin Tag.E6.rank → ℤ}
    (ht : t ∈ a2T_kd264e6) : u • t ∈ a2T_kd264e6 := by
  obtain ⟨htP, a, ha, b, hb, rfl⟩ := a2_T_spec_kd264e6 t ht
  have h := hP _ htP
  rw [smul_add] at h ⊢
  exact a2_add_mem_T_kd264e6 _ (hP a ha) _ (hP b hb) h

private theorem a2_eq_one_kd264e6 {u : WeylGroup Tag.E6} {n : ℕ} (hn : Odd n) (hun : u ^ n = 1)
    (hP : ∀ x ∈ a2P_kd264e6, u • x ∈ a2P_kd264e6) {t : Fin Tag.E6.rank → ℤ}
    (htT : t ∈ a2T_kd264e6) (ht : u • t = t) : u = 1 := by
  have hT1 := a2_smul_mem_T_kd264e6 hP (t := a2v_kd264e6 1 0 1 0 0 0) (by decide +kernel)
  have hT2 := a2_smul_mem_T_kd264e6 hP (t := a2v_kd264e6 0 0 0 0 1 1) (by decide +kernel)
  have hT3 := a2_smul_mem_T_kd264e6 hP (t := a2v_kd264e6 1 2 2 3 2 1) (by decide +kernel)
  have hne12 : a2v_kd264e6 1 0 1 0 0 0 ≠ a2v_kd264e6 0 0 0 0 1 1 := by decide +kernel
  have hne13 : a2v_kd264e6 1 0 1 0 0 0 ≠ a2v_kd264e6 1 2 2 3 2 1 := by decide +kernel
  have hne23 : a2v_kd264e6 0 0 0 0 1 1 ≠ a2v_kd264e6 1 2 2 3 2 1 := by decide +kernel
  simp only [a2T_kd264e6, Finset.mem_insert, Finset.mem_singleton] at hT1 hT2 hT3 htT
  have hfixT : ∀ s ∈ a2T_kd264e6, u • s = s := by
    have key : u • a2v_kd264e6 1 0 1 0 0 0 = a2v_kd264e6 1 0 1 0 0 0 ∧
        u • a2v_kd264e6 0 0 0 0 1 1 = a2v_kd264e6 0 0 0 0 1 1 ∧
        u • a2v_kd264e6 1 2 2 3 2 1 = a2v_kd264e6 1 2 2 3 2 1 := by
      rcases htT with rfl | rfl | rfl
      · obtain ⟨h2, h3⟩ := fix_two_of_fix_one_kd264e6 hn hun hne12 hne13 hne23 hT2 hT3 ht
        exact ⟨ht, h2, h3⟩
      · obtain ⟨h1, h3⟩ := fix_two_of_fix_one_kd264e6 hn hun hne12.symm hne23 hne13
          (by rcases hT1 with h | h | h <;> simp [h]) (by rcases hT3 with h | h | h <;> simp [h]) ht
        exact ⟨h1, ht, h3⟩
      · obtain ⟨h1, h2⟩ := fix_two_of_fix_one_kd264e6 hn hun hne13.symm hne23.symm hne12
          (by rcases hT1 with h | h | h <;> simp [h]) (by rcases hT2 with h | h | h <;> simp [h]) ht
        exact ⟨h1, h2, ht⟩
    intro s hs
    simp only [a2T_kd264e6, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact key.1
    · exact key.2.1
    · exact key.2.2
  have hfixP : ∀ x ∈ a2P_kd264e6, u • x = x := by
    intro x hx
    rcases a2_pair_kd264e6 x hx with hxT | ⟨y, hy, hxyT, huniq⟩
    · exact hfixT x hxT
    · have hsum : u • x + u • y = x + y := by rw [← smul_add, hfixT _ hxyT]
      refine fix_of_pair_kd264e6 hn hun (y := y) (huniq _ (hP x hx) _ (hP y hy) hsum) fun h => ?_
      rw [h] at hsum
      exact add_left_cancel (hsum.trans (add_comm x y))
  refine ext_single fun i => ?_
  rw [one_smul]
  by_cases hi : i = 3
  · subst hi
    have hθ := hfixP _ a2_theta_mem_kd264e6
    have h0 := hfixP _ (a2_single_mem_kd264e6 0 (by decide))
    have h1 := hfixP _ (a2_single_mem_kd264e6 1 (by decide))
    have h2 := hfixP _ (a2_single_mem_kd264e6 2 (by decide))
    have h4 := hfixP _ (a2_single_mem_kd264e6 4 (by decide))
    have h5 := hfixP _ (a2_single_mem_kd264e6 5 (by decide))
    have h3 : (3 : ℤ) • (u • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) =
        (3 : ℤ) • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) := by
      rw [← smul_comm, a2_three_single_kd264e6, smul_sub, smul_add, smul_add, smul_add, smul_add,
        smul_comm u (2 : ℤ), smul_comm u (2 : ℤ), smul_comm u (2 : ℤ), hθ, h0, h1, h2, h4, h5]
    exact smul_right_injective _ (by norm_num : (3 : ℤ) ≠ 0) h3
  · exact hfixP _ (a2_single_mem_kd264e6 i hi)

private theorem a2_align_kd264e6 {L : Type} [Field L] {ta : Fin Tag.E6.rank → Lˣ}
    (hw : ∃ w : WeylGroup Tag.E6, kernelRoots (rootCharHom ta) =
      (fun α => w⁻¹ • α) '' {γ | IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3}) :
    ∃ v : WeylGroup Tag.E6,
      (∀ α ∈ posRoots (kernelRoots (rootCharHom ta)), v • α ∈ a2P_kd264e6) ∧
        ∀ γ ∈ a2P_kd264e6, v⁻¹ • γ ∈ posRoots (kernelRoots (rootCharHom ta)) := by
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
    exact a2_mem_P_iff_kd264e6.2 ⟨hr, hd, hh⟩
  · obtain ⟨hr, hd, hh⟩ := a2_mem_P_iff_kd264e6.1 hγ
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

private theorem iform_neg_left_kd264e6 (x y : Fin Tag.E6.rank → ℤ) :
    iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

private theorem iform_neg_right_kd264e6 (x y : Fin Tag.E6.rank → ℤ) :
    iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

private theorem iform_sign_kd264e6 (z x s : Fin Tag.E6.rank → ℤ) (h : z = x ∨ z = -x) :
    (iform z s = 0 ↔ iform x s = 0) := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · rw [iform_neg_left_kd264e6, neg_eq_zero]

private theorem iform_sign2_kd264e6 (z x z' y : Fin Tag.E6.rank → ℤ) (h : z = x ∨ z = -x)
    (h' : z' = y ∨ z' = -y) : (iform z z' = 0 ↔ iform x y = 0) := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Iff.rfl
  · rw [iform_neg_right_kd264e6, neg_eq_zero]
  · rw [iform_neg_left_kd264e6, neg_eq_zero]
  · rw [iform_neg_left_kd264e6, iform_neg_right_kd264e6, neg_neg]


theorem mem_kernelReflectionGroup_of_mapsTo_a2CubeClass {L : Type} [Field L]
    [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) (i : KernelComponent (rootCharHom a))
    (hwi : ∀ α ∈ componentRoots (rootCharHom a) i, w • α ∈ componentRoots (rootCharHom a) i) :
    w ∈ kernelReflectionGroup a := by
  classical
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom a) := rfl
  have hwχ : w ∈ charStabilizer (rootCharHom a) := hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  have hωi : ∀ α ∈ componentRoots (rootCharHom a) i,
      (w * u) • α ∈ componentRoots (rootCharHom a) i := by
    intro α hα
    have h1 : u • α ∈ componentRoots (rootCharHom a) i := by
      rw [← image_componentRoots_of_mem_kernelWeylGroup_kd264e6 hu i]
      exact ⟨α, hα, rfl⟩
    rw [mul_smul]
    exact hwi _ h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isPGroup_quotient
    Nat.prime_three hap
  let e : kernelPosStabilizer (rootCharHom a) ≃* (↥(rootCharStabilizerSubgroup a) ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) :=
    kernelPosStabilizerMulEquiv
  have hΩ : IsPGroup 3 (kernelPosStabilizer (rootCharHom a)) := hQ.of_equiv e.symm
  obtain ⟨k, hk⟩ := hΩ ⟨w * u, hωΩ⟩
  have hωk : (w * u) ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨v, hv1, hv2⟩ := a2_align_kd264e6
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.a2cube_exists_weyl_kernelRoots_eq
      h3 hap h18)
  have hconj : ∀ x ∈ a2P_kd264e6, (v * (w * u) * v⁻¹) • x ∈ a2P_kd264e6 := by
    intro x hx
    have h2 : (w * u) • v⁻¹ • x ∈ posRoots (kernelRoots (rootCharHom a)) := by
      rw [← hωΩ.2]
      exact Set.mem_image_of_mem _ (hv2 x hx)
    rw [mul_smul, mul_smul]
    exact hv1 _ h2
  have hsign : ∀ δ ∈ kernelRoots (rootCharHom a), ∃ x ∈ a2P_kd264e6, v • δ = x ∨ v • δ = -x := by
    intro δ hδ
    rcases IsRoot.height_pos_or_neg hδ.1 with h | h
    · exact ⟨v • δ, hv1 δ ⟨hδ, h⟩, Or.inl rfl⟩
    · have hneg : -δ ∈ posRoots (kernelRoots (rootCharHom a)) := by
        refine ⟨⟨IsRoot.neg hδ.1, ?_⟩, by rw [height_neg]; linarith⟩
        rw [ofAdd_neg, map_inv, hδ.2, inv_one]
      exact ⟨v • -δ, hv1 _ hneg, Or.inr (by rw [smul_neg, neg_neg])⟩
  obtain ⟨⟨β₀, hβ₀⟩, hi⟩ := Quotient.exists_rep i
  have hβ₀i : β₀ ∈ componentRoots (rootCharHom a) i := ⟨hβ₀, hi⟩
  obtain ⟨β, hβi, hβpos⟩ : ∃ β ∈ componentRoots (rootCharHom a) i, 0 < height β := by
    rcases IsRoot.height_pos_or_neg hβ₀.1 with h | h
    · exact ⟨β₀, hβ₀i, h⟩
    · refine ⟨-β₀, (isRootComponent_componentRoots i).neg_mem β₀ hβ₀i, ?_⟩
      rw [height_neg]
      linarith
  have hxP : v • β ∈ a2P_kd264e6 := hv1 β ⟨hβi.1, hβpos⟩
  obtain ⟨t, htT, hxt⟩ := a2_factA_kd264e6 _ hxP
  have htP : t ∈ a2P_kd264e6 := (a2_T_spec_kd264e6 t htT).1
  have hβ'S := hv2 t htP
  have hββ' : iform β (v⁻¹ • t) ≠ 0 := by
    rw [← iform_smul v β (v⁻¹ • t), smul_inv_smul]
    exact hxt
  have hβ'i : v⁻¹ • t ∈ componentRoots (rootCharHom a) i :=
    ⟨hβ'S.1, (mk_eq_of_iform_ne_zero (α := ⟨_, hβ'S.1⟩) (β := ⟨β, hβi.1⟩)
      (by rwa [iform_comm])).trans hβi.2⟩
  have hstep : ∀ δ δ' : kernelRoots (rootCharHom a), iform (δ : Fin Tag.E6.rank → ℤ) δ' ≠ 0 →
      (iform (v • (δ : Fin Tag.E6.rank → ℤ)) t = 0 ↔
        iform (v • (δ' : Fin Tag.E6.rank → ℤ)) t = 0) := by
    intro δ δ' hδδ'
    obtain ⟨x, hx, hxδ⟩ := hsign δ δ.2
    obtain ⟨y, hy, hyδ⟩ := hsign δ' δ'.2
    have hvv : iform (v • (δ : Fin Tag.E6.rank → ℤ)) (v • (δ' : Fin Tag.E6.rank → ℤ)) ≠ 0 := by
      rw [iform_smul]
      exact hδδ'
    have hxy : iform x y ≠ 0 := fun h0 => hvv ((iform_sign2_kd264e6 _ _ _ _ hxδ hyδ).2 h0)
    rw [iform_sign_kd264e6 _ _ t hxδ, iform_sign_kd264e6 _ _ t hyδ]
    exact a2_factB_kd264e6 x hx y hy hxy t htT
  have hcls : ∀ δ δ' : kernelRoots (rootCharHom a), Relation.EqvGen (fun α β : kernelRoots
      (rootCharHom a) => (α : Fin Tag.E6.rank → ℤ) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ
        (β : Fin Tag.E6.rank → ℤ)) ≠ 0) δ δ' →
      (iform (v • (δ : Fin Tag.E6.rank → ℤ)) t = 0 ↔
        iform (v • (δ' : Fin Tag.E6.rank → ℤ)) t = 0) := by
    intro δ δ' h
    induction h with
    | rel a b hab =>
      rw [dotProduct_mulVec_eq_iform] at hab
      exact hstep a b hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  have hωβ' := hωi _ hβ'i
  obtain ⟨hk1, hk2⟩ := hωβ'
  have hrel := hcls ⟨_, hk1⟩ ⟨β, hβi.1⟩ (Quotient.exact (hk2.trans hβi.2.symm))
  have hvt : v • ((w * u) • v⁻¹ • t) = (v * (w * u) * v⁻¹) • t := by
    simp only [mul_smul]
  simp only [hvt] at hrel
  have hut : iform ((v * (w * u) * v⁻¹) • t) t ≠ 0 := fun h => hxt (hrel.1 h)
  have hutT := a2_smul_mem_T_kd264e6 hconj htT
  have ht : (v * (w * u) * v⁻¹) • t = t := a2_factC_kd264e6 _ hutT _ htT hut
  have hu'k : (v * (w * u) * v⁻¹) ^ 3 ^ k = 1 := by
    rw [conj_pow, hωk, mul_one, mul_inv_cancel]
  have hu'1 := a2_eq_one_kd264e6 ((by decide : Odd 3).pow) hu'k hconj htT ht
  rw [conj_eq_one_iff] at hu'1
  have hwu : w = u⁻¹ := eq_inv_of_mul_eq_one_left hu'1
  rw [hW, hwu]
  exact inv_mem hu

end A2Cube

section KacCount

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

theorem kernelCount_cases_of_kac_E6 : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
        cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30 ∨
        cntB m0.val m1.val m2.val m3.val m4.val m5.val = 40) ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 18 ∨
      ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 72 := by
  decide +kernel

end KacCount

section Main

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

theorem e6EightCentralizerConn_holds :
    E6EightCentralizerConn := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i hqs hN y hyC hyF hyR
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hA := excAlgTypeAAt_E6_of_kd264alg e6D4OuterNotEight_holds L p₀ S hq8 a hT hap h1 i hqs hN
  obtain ⟨ζ, w₀, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data h3L hap
  have hcnt :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.ncard_kernelRoots_eq_cntB hζ w₀
      hchar
  rcases kernelCount_cases_of_kac_E6 m0 m1 m2 m3 m4 m5 hsum with hconn | h24 | h18 | h72
  ·
    have hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ) := by
      rw [hcnt]
      rcases hconn with h | h | h <;> simp [h]
    have hW :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.e6_stab_le_kernelReflectionGroup_of_conn
        a hap hk
    have h :=
      CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le
        Tag.E6 L a hW
    rw [h] at hyC
    exact hyC
  ·
    have hall : (kernelRoots (rootCharHom a)).ncard = 24 := hcnt.trans h24
    obtain ⟨hr4, hn24⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.d4t2_class_of_card h3L hap hall i
    rw [hr4] at hA
    omega
  rotate_left
  ·
    obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
    exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hncard, h72 x hx]; decide)) h1
  have h18' : (kernelRoots (rootCharHom a)).ncard = 18 := hcnt.trans h18
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    rcases CFSG.LocalAnalysis.GLTheoremA.RationalModel.typeA_frame_cases S Nat.prime_three hT hap
      h1 i hA with ⟨hr1, hn⟩ | h | h
    · exact orbitLength_eq_one_of_rankOne_kd264alg S hq8 hT i hr1 hn hqs hN
    · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
      exfalso
      obtain ⟨K, _, _, f, -, hKcard, hfeq, -, g, hgsurj, hgker⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.RationalModel.exists_slCover_rationalComponent_splitFrame S
          hT i hν hψ hΨ π hπ
      have hs0 := (outer_componentOrbitLength_spec S hT i).1
      have hE : Nat.card K =
          2 ^ (3 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
        rw [hKcard, hfeq, hq8, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
      have hm2 := multiplicity_eq_two_of_compAlgEight (by omega) hs0 hE g hgsurj hgker
        (isQuasisimple_specialLinearGroup hν) hN
      omega
    · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
      exact orbitLength_eq_one_of_unitaryFrame_kd264alg S hq8 hT i hν hψ hΨ π hπ hqs hN
  have hRS := rationalComponent_le_rootSpan_kd264alg S hT i hs1
  obtain ⟨w, hwa, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L a).1 _ hyC
  have hm₁ : h * u ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right (rootSpan_mono
      Set.inter_subset_left hu))
  have hm₂ : v ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  set n := canonicalRep (coxeterSystem Tag.E6) L w with hn
  have hwχ : IsCharConj (rootCharHom a) (rootCharHom a) w := by
    intro x
    have hw' : w⁻¹ ∈ rootCharStabilizerSubgroup a := (rootCharStabilizerSubgroup a).inv_mem hwa
    exact (hw' x).symm
  obtain ⟨i', hi'⟩ := KacData.componentRoots_smul_of_isCharConj hwχ i
  have himg : (fun α => w • α) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i' := by
    rw [hi', Set.image_image]
    simp
  have htrans := (canonical_weyl_root_transport Tag.E6 L).1 w (componentRoots (rootCharHom a) i)
    (fun α hα => hα.1.1)
  rw [himg] at htrans
  have hyR' : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map
      (MulAut.conj (h * u * n * v)).toMonoidHom = rationalComponent S.ρ S.Γ (rootCharHom a) i := hyR
  have hRi' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (componentRoots (rootCharHom a) i') := by
    intro r hr
    rw [← hyR'] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hx1 : v * x * v⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) :=
      (mem_componentRootSpan_iff_conj_of_mem hm₂ i x).1 (hRS hx)
    have hx2 : n * (v * x * v⁻¹) * n⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i') := by
      have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hx1
      rw [htrans] at this
      simpa [MulAut.conj_apply] using this
    have hx3 := (mem_componentRootSpan_iff_conj_of_mem hm₁ i' _).1 hx2
    have e : (MulAut.conj (h * u * n * v)).toMonoidHom x =
        h * u * (n * (v * x * v⁻¹) * n⁻¹) * (h * u)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hx3
  have hii : i' = i := by
    by_contra hne
    have hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, x * z = z * x := by
      intro x hx z hz
      have hxC := componentRootSpan_le_centralizer L hne (hRi' hx)
      exact (Subgroup.mem_centralizer_iff.1 hxC z (hRS hz)).symm
    obtain ⟨-, -, c, d, hcd⟩ := hqs
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective d
    apply hcd
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm _ c.2 _ d.2)
  have hwi : ∀ α ∈ componentRoots (rootCharHom a) i, w • α ∈ componentRoots (rootCharHom a) i := by
    intro α hα
    rw [← hii, ← himg]
    exact ⟨α, hα, rfl⟩
  have hwS := mem_kernelReflectionGroup_of_mapsTo_a2CubeClass h3L hap h18' hwa i hwi
  have hnM : n ∈ toralRootGroup Tag.E6 L a := by
    have hker := kernelReflectionGroup_le_ker (K := L) a
      (x := (⟨w, hwa⟩ : rootCharStabilizerSubgroup a)) (Subgroup.mem_subgroupOf.2 hwS)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  exact mul_mem (mul_mem hm₁ hnM) hm₂

end Main

theorem lieCompAlg_excUntwisted_kd264e6 :
    LieCompAlg isExcUntwistedIdx :=
  lieCompAlg_excUntwisted_of_E6res_kd264alg e6D4OuterNotEight_holds e6EightCentralizerConn_holds

theorem lieCompAlg_excTwisted_kd264e6 :
    LieCompAlg isExcTwistedIdx :=
  lieCompAlg_excTwisted_of_E6res_kd264alg e6D4OuterNotEight_holds e6EightCentralizerConn_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
