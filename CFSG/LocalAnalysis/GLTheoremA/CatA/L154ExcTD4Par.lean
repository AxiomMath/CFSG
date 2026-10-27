module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Core
public import CFSG.RankThree.Lattice.SteinbergBTE6OrderFiveGraph
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

@[expose] def L154RefJ : Set (WeylGroup Tag.E6) :=
  {s | ∃ γ ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), s = rootReflection γ}

@[expose] def L154D4Ev (x : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ j ∈ d4Nodes Tag.E6, 2 ∣ iform x (Pi.single j 1)

section Refl


theorem l154td4_iform_expand (x γ : Fin Tag.E6.rank → ℤ) :
    iform x γ = ∑ k, γ k * iform x (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single γ]
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (Pi.single k (γ k) : Fin Tag.E6.rank → ℤ) = γ k • (Pi.single k 1) := by
    ext j
    simp [Pi.single_apply]
  rw [h, iform_smul_right]

theorem l154td4_even_iform {x γ : Fin Tag.E6.rank → ℤ} (hx : L154D4Ev x)
    (hγ : ∀ k ∉ d4Nodes Tag.E6, γ k = 0) : 2 ∣ iform x γ := by
  rw [l154td4_iform_expand]
  refine Finset.dvd_sum fun k _ => ?_
  by_cases hk : k ∈ d4Nodes Tag.E6
  · exact Dvd.dvd.mul_left (hx k hk) _
  · rw [hγ k hk, zero_mul]
    exact dvd_zero 2

theorem l154td4_rootReflection_smul {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (x : Fin Tag.E6.rank → ℤ) : rootReflection γ • x = x - iform γ x • γ := by
  rw [rootReflection_smul hγ x]
  have h : corootPair γ x = iform γ x := by
    unfold corootPair
    rw [iform_self_e6 hγ]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [h]

theorem l154td4_parity_refl {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) (x : Fin Tag.E6.rank → ℤ) :
    (L154D4Ev x → L154D4Ev (rootReflection γ • x)) ∧
      (L154D4Ev x → ∀ k, 2 ∣ (rootReflection γ • x - x) k) := by
  have hr := l154td4_rootReflection_smul hγ.1 x
  have hc : L154D4Ev x → 2 ∣ iform γ x := fun hx => by
    rw [iform_comm]
    exact l154td4_even_iform hx hγ.2
  refine ⟨fun hx j hj => ?_, fun hx k => ?_⟩
  · rw [hr, iform_sub_left, iform_smul_left]
    exact dvd_sub (hx j hj) (Dvd.dvd.mul_right (hc hx) _)
  · rw [hr]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left]
    exact dvd_neg.2 (Dvd.dvd.mul_right (hc hx) _)

theorem l154td4_parity {u : WeylGroup Tag.E6} (hu : u ∈ Subgroup.closure L154RefJ) :
    ∀ x, (L154D4Ev x ↔ L154D4Ev (u • x)) ∧ (L154D4Ev x → ∀ k, 2 ∣ (u • x - x) k) := by
  refine Subgroup.closure_induction
    (p := fun w _ => ∀ x, (L154D4Ev x ↔ L154D4Ev (w • x)) ∧
      (L154D4Ev x → ∀ k, 2 ∣ (w • x - x) k)) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨γ, hγ, rfl⟩ x
    refine ⟨⟨(l154td4_parity_refl hγ x).1, fun h => ?_⟩, (l154td4_parity_refl hγ x).2⟩
    have h1 := (l154td4_parity_refl hγ (rootReflection γ • x)).1 h
    rwa [smul_smul, rootReflection_mul_self hγ.1, one_smul] at h1
  · intro x
    exact ⟨by simp, fun _ k => by simp⟩
  · intro u v _ _ ihu ihv x
    rw [mul_smul]
    refine ⟨⟨fun hx => (ihu (v • x)).1.mp ((ihv x).1.mp hx),
      fun hx => (ihv x).1.mpr ((ihu (v • x)).1.mpr hx)⟩, fun hx k => ?_⟩
    have h1 : 2 ∣ (u • (v • x) - v • x) k := (ihu (v • x)).2 ((ihv x).1.mp hx) k
    have h2 : 2 ∣ (v • x - x) k := (ihv x).2 hx k
    have hsum : (u • (v • x) - x) k = (u • (v • x) - v • x) k + (v • x - x) k := by
      simp only [Pi.sub_apply]
      ring
    rw [hsum]
    exact dvd_add h1 h2
  · intro u _ ihu x
    have hux : u • (u⁻¹ • x) = x := smul_inv_smul u x
    have hiff : L154D4Ev x ↔ L154D4Ev (u⁻¹ • x) := by
      have h := (ihu (u⁻¹ • x)).1
      rw [hux] at h
      exact h.symm
    refine ⟨hiff, fun hx k => ?_⟩
    have hd : 2 ∣ (x - u⁻¹ • x) k := by
      have h := (ihu (u⁻¹ • x)).2 (hiff.1 hx) k
      rwa [hux] at h
    have h3 : (u⁻¹ • x - x) k = -((x - u⁻¹ • x) k) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact dvd_neg.2 hd

end Refl

section Leaves

private abbrev l154es (p : Fin Tag.E6.rank) : Fin Tag.E6.rank → ℤ := Pi.single p 1

private theorem l154td4_leaf_mem {p : Fin Tag.E6.rank} (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) :
    p ∈ d4Nodes Tag.E6 := by
  simp only [d4Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  omega

private theorem l154td4_leaf_cases {p : Fin Tag.E6.rank} (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) :
    p = 1 ∨ p = 2 ∨ p = 4 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h
  · left
    ext
    exact h
  · right
    left
    ext
    exact h
  · right
    right
    ext
    exact h

private theorem l154td4_single_mem {i : Fin Tag.E6.rank} (hi : i ∈ d4Nodes Tag.E6) :
    l154es i ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
  ⟨isRoot_single Tag.E6 i,
    fun j hj => Pi.single_eq_of_ne (fun h => hj (by rw [h]; exact hi)) 1⟩

private theorem l154td4_iform_single_single (p j : Fin Tag.E6.rank) :
    iform (Pi.single p 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) =
      Tag.E6.symmetrizedCartan p j := by
  simp [iform, Pi.single_apply]

private theorem l154td4_cartan_pair_even (p q j : Fin Tag.E6.rank)
    (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) (hq : q.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j ∈ d4Nodes Tag.E6) :
    2 ∣ Tag.E6.symmetrizedCartan p j + Tag.E6.symmetrizedCartan q j := by
  rcases l154td4_leaf_cases hp with rfl | rfl | rfl <;>
    rcases l154td4_leaf_cases hq with rfl | rfl | rfl <;>
    fin_cases j <;> simp_all [d4Nodes] <;> decide


private theorem l154td4_ev_add {p q : Fin Tag.E6.rank} (hp : p.val ∈ ({1, 2, 4} : Set ℕ))
    (hq : q.val ∈ ({1, 2, 4} : Set ℕ)) : L154D4Ev (l154es p + l154es q) := by
  intro j hj
  rw [iform_add_left, l154td4_iform_single_single, l154td4_iform_single_single]
  exact l154td4_cartan_pair_even p q j hp hq hj

theorem l154td4_not_inner_sq_leafThreeCycle {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    {u u'' : WeylGroup Tag.E6} (hu : u ∈ Subgroup.closure L154RefJ)
    (hu'' : u'' ∈ Subgroup.closure L154RefJ)
    (f : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      f α = u • permLattice (List.formPerm [a, b, c]) α)
    (hsq : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), f (f α) = u'' • α) : False := by
  have hroot_a := l154td4_single_mem (l154td4_leaf_mem ha)
  have hroot_b := l154td4_single_mem (l154td4_leaf_mem hb)
  have hroot_c := l154td4_single_mem (l154td4_leaf_mem hc)
  have hπa : List.formPerm [a, b, c] a = b := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := a) hab hac, Equiv.swap_apply_left]
  have hπb : List.formPerm [a, b, c] b = c := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := c) (Ne.symm hac) (Ne.symm hbc)]
  have hπc : List.formPerm [a, b, c] c = a := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_right]
  have hwa : f (l154es a) = u • l154es b := by
    have h := hact (l154es a) hroot_a
    rwa [permLattice_single, hπa] at h
  have hwb : f (l154es b) = u • l154es c := by
    have h := hact (l154es b) hroot_b
    rwa [permLattice_single, hπb] at h
  have hwc : f (l154es c) = u • l154es a := by
    have h := hact (l154es c) hroot_c
    rwa [permLattice_single, hπc] at h
  have hsa : f (u • l154es b) = u'' • l154es a := by
    have h := hsq (l154es a) hroot_a
    rwa [hwa] at h
  have hsb : f (u • l154es c) = u'' • l154es b := by
    have h := hsq (l154es b) hroot_b
    rwa [hwb] at h
  have step1 := l154td4_parity hu
  have step3 := l154td4_parity hu''
  have hdiv1 := (step1 (l154es b + l154es c)).2 (l154td4_ev_add hb hc)
  have hdiv2 := (step1 (l154es c + l154es a)).2 (l154td4_ev_add hc ha)
  have hdiv3 := (step3 (l154es a + l154es b)).2 (l154td4_ev_add ha hb)
  obtain ⟨t1, ht1⟩ : ∃ t : Fin Tag.E6.rank → ℤ,
      u • (l154es b + l154es c) - (l154es b + l154es c) = (2 : ℤ) • t :=
    ⟨fun k => (u • (l154es b + l154es c) - (l154es b + l154es c)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv1 k)).symm⟩
  obtain ⟨t2, ht2⟩ : ∃ t : Fin Tag.E6.rank → ℤ,
      u • (l154es c + l154es a) - (l154es c + l154es a) = (2 : ℤ) • t :=
    ⟨fun k => (u • (l154es c + l154es a) - (l154es c + l154es a)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv2 k)).symm⟩
  obtain ⟨t3, ht3⟩ : ∃ t : Fin Tag.E6.rank → ℤ,
      u'' • (l154es a + l154es b) - (l154es a + l154es b) = (2 : ℤ) • t :=
    ⟨fun k => (u'' • (l154es a + l154es b) - (l154es a + l154es b)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv3 k)).symm⟩
  have hy1 : u • l154es b + u • l154es c = (l154es b + l154es c) + (2 : ℤ) • t1 := by
    rw [← smul_add, ← ht1]
    abel
  have hy2 : u • l154es c + u • l154es a = (l154es c + l154es a) + (2 : ℤ) • t2 := by
    rw [← smul_add, ← ht2]
    abel
  have hy3 : u'' • l154es a + u'' • l154es b = (l154es a + l154es b) + (2 : ℤ) • t3 := by
    rw [← smul_add, ← ht3]
    abel
  have hL : f (u • l154es b + u • l154es c) = (l154es a + l154es b) + (2 : ℤ) • t3 := by
    rw [map_add, hsa, hsb, hy3]
  have hR : f ((l154es b + l154es c) + (2 : ℤ) • t1) =
      (l154es c + l154es a) + (2 : ℤ) • (t2 + f t1) := by
    rw [map_add, map_add, map_zsmul, hwb, hwc, smul_add, ← add_assoc, hy2]
  have hmain : (l154es a + l154es b) + (2 : ℤ) • t3 =
      (l154es c + l154es a) + (2 : ℤ) • (t2 + f t1) := by
    calc (l154es a + l154es b) + (2 : ℤ) • t3 = f (u • l154es b + u • l154es c) := hL.symm
      _ = f ((l154es b + l154es c) + (2 : ℤ) • t1) := by rw [hy1]
      _ = _ := hR
  have hca : (l154es a) c = 0 := Pi.single_eq_of_ne (Ne.symm hac) 1
  have hcb : (l154es b) c = 0 := Pi.single_eq_of_ne (Ne.symm hbc) 1
  have hcc : (l154es c) c = 1 := Pi.single_eq_same c 1
  have hval := congrFun hmain c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hca, hcb, hcc] at hval
  omega

end Leaves

section Inner


theorem l154td4_exists_inner_sq {v : WeylGroup Tag.E6} {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    {σ : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ} (h : twistInner Ψ σ) :
    ∃ u'' ∈ Subgroup.closure L154RefJ, ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • σ (v • α) = u'' • α := by
  obtain ⟨w, hw, hσ⟩ := h
  subst hΨ
  refine ⟨v⁻¹ * w * v, CFSG.RankThree.Lattice.conj_mem_closure_rootReflection
    (fun α hα => hα.1) v hw, fun α hα => ?_⟩
  rw [hσ (v • α) ⟨α, hα, rfl⟩, mul_smul, mul_smul]

end Inner

section Parabolic


theorem l154td4_parabolic_le :
    parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) ≤ Subgroup.closure L154RefJ := by
  unfold parabolicWeylGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  refine Subgroup.subset_closure ⟨Pi.single j 1, ⟨isRoot_single Tag.E6 j, fun k hk =>
    Pi.single_eq_of_ne (fun h => hk (by rw [h]; exact hj)) 1⟩, ?_⟩
  have h := rootReflection_eq_conj (τ := Tag.E6) (w := 1) (j := j) (by rw [one_smul])
  rw [h]
  group

end Parabolic

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
