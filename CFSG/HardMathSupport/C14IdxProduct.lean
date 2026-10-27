module

public import CFSG.HardMathSupport.C14IdxLattice
public import CFSG.HardMathSupport.C14IdxDerived
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Pointwise

namespace CFSG.HardMathSupport.C14Idx

private lemma cochar_zero {τ : Tag} {L : Type} [Field L] (c : Lˣ) :
    cochar (0 : Fin τ.rank → ℤ) c = 1 := by
  funext i
  simp [cochar]

private lemma cochar_add {τ : Tag} {L : Type} [Field L] (v w : Fin τ.rank → ℤ) (c : Lˣ) :
    cochar (v + w) c = cochar v c * cochar w c := by
  funext i
  simp [cochar, zpow_add]

private lemma cochar_neg {τ : Tag} {L : Type} [Field L] (v : Fin τ.rank → ℤ) (c : Lˣ) :
    cochar (-v) c = (cochar v c)⁻¹ := by
  funext i
  simp [cochar]

private lemma neg_mem_familyKernel {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ familyKernel a) :
    -γ ∈ familyKernel a := by
  refine ⟨CFSG.LieType.Chevalley.IsRoot.neg hγ.1, fun i => ?_⟩
  rw [show -γ = (-1 : ℤ) • γ by simp, C14IdxDet.rootChar_zsmul, hγ.2 i, one_zpow]

private lemma rootDiagUnit_cochar_mem_sup_of_mem_closure {τ : Tag} {L : Type} [Field L]
    {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (c : Lˣ) {v : Fin τ.rank → ℤ}
    (hv : v ∈ AddSubgroup.closure
      ({lam | C14IdxDet.PerpOf (familyKernel a) lam} ∪ C14Idx.corootVec '' familyKernel a)) :
    rootDiagUnit τ (cochar v c) ∈ famZ a ⊔ rootSpan τ L (familyKernel a) := by
  classical
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · have hgen : rootDiagUnit τ (cochar x c) ∈ famZ a :=
          Subgroup.subset_closure ⟨x, c, hx, rfl⟩
        exact Subgroup.mem_sup_left hgen
      · obtain ⟨β, hβ, rfl⟩ := hx
        have hHSL : rootDiagUnit τ (cochar (C14Idx.corootVec β) c) =
            rootSL2 τ L β (HSL c) := by
          rw [rootSL2_HSL_eq hβ.1 c]
          congr 1
        rw [hHSL]
        exact Subgroup.mem_sup_right (rootSpan_mono (by
          intro γ hγ
          rcases hγ with rfl | rfl
          · exact hβ
          · exact neg_mem_familyKernel a hβ)
          (rootSL2_mem_rootSpan_pair hβ.1 (HSL c)))
  | zero =>
      simpa [cochar_zero, rootDiagUnit_one] using
        (Subgroup.one_mem (famZ a ⊔ rootSpan τ L (familyKernel a)))
  | add x y _ _ hx hy =>
      rw [cochar_add, rootDiagUnit_mul]
      exact mul_mem hx hy
  | neg x _ hx =>
      rw [cochar_neg, ← rootDiagUnit_inv]
      exact inv_mem hx

private lemma famZ_le_normalizer_rootSpan {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) :
    famZ a ≤ Subgroup.normalizer
      ((rootSpan τ L (familyKernel a) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨lam, c, _hlam, rfl⟩
  exact (torusGroup_le_normalizer_rootSpan (S := familyKernel a)
    (fun α hα => hα.1)) (rootDiagUnit_mem_torusGroup (cochar lam c))

private lemma exists_pow_eq_units {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {N : ℕ}
    (hN : 0 < N) (s : Fin τ.rank → Lˣ) :
    ∃ r : Fin τ.rank → Lˣ, ∀ i, r i ^ N = s i := by
  choose y hy using fun i => IsAlgClosed.exists_pow_nat_eq (s i : L) hN
  have hy0 : ∀ i, y i ≠ 0 := by
    intro i h
    have h' := hy i
    rw [h, zero_pow hN.ne'] at h'
    exact (s i).ne_zero h'.symm
  refine ⟨fun i => Units.mk0 (y i) (hy0 i), fun i => ?_⟩
  apply Units.ext
  simpa using hy i

private lemma prod_cochar_eq {τ : Tag} {L : Type} [Field L] {N : ℕ}
    (r s : Fin τ.rank → Lˣ) (hr : ∀ i, r i ^ N = s i) :
    (List.ofFn (fun i => cochar (N • Pi.single i 1) (r i))).prod = s := by
  classical
  rw [List.prod_ofFn]
  funext j
  rw [Finset.prod_apply, Finset.prod_eq_single j]
  · have h1 : (N • Pi.single j 1 : Fin τ.rank → ℤ) j = (N : ℤ) := by simp
    calc (cochar (N • Pi.single j 1) (r j)) j
        = (r j) ^ ((N • Pi.single j 1 : Fin τ.rank → ℤ) j) := rfl
      _ = (r j) ^ (N : ℤ) := by rw [h1]
      _ = r j ^ N := by rw [zpow_natCast]
      _ = s j := hr j
  · intro i _ hij
    have h1 : (N • Pi.single i 1 : Fin τ.rank → ℤ) j = 0 := by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij)]
      simp
    rw [show (cochar (N • Pi.single i 1) (r i)) j =
      (r i) ^ ((N • Pi.single i 1 : Fin τ.rank → ℤ) j) from rfl, h1, zpow_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma rootDiagUnit_list_prod_eq {τ : Tag} {L : Type} [Field L]
    (f : Fin τ.rank → Fin τ.rank → Lˣ) :
    rootDiagUnit τ ((List.ofFn f).prod) =
      (List.ofFn (fun i => rootDiagUnit τ (f i))).prod := by
  change (rootDiagUnitHom τ L) ((List.ofFn f).prod) =
    (List.ofFn (fun i => (rootDiagUnitHom τ L) (f i))).prod
  rw [MonoidHom.map_list_prod (rootDiagUnitHom τ L) (List.ofFn f), List.map_ofFn]
  rfl

private theorem exists_mul_of_mem_torus_sup_rootSpan {τ : Tag} {L : Type} [Field L]
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L S) :
    ∃ t ∈ torusGroup τ L, ∃ q ∈ rootSpan τ L S, y = t * q := by
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L) (rootSpan τ L S)
    (torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L S : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) := hy
  rw [e] at hy'
  obtain ⟨t, ht, q, hq, rfl⟩ := hy'
  exact ⟨t, ht, q, hq, rfl⟩

theorem exists_famZ_mul_rootSpan_eq {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) (s : Fin τ.rank → Lˣ) :
    ∃ z ∈ famZ a, ∃ u ∈ rootSpan τ L (familyKernel a), rootDiagUnit τ s = z * u := by
  classical
  obtain ⟨N, hNpos, hN⟩ := C14IdxDet.exists_pos_nsmul_single_mem_closure_perp_coroot
    (Ψ := familyKernel a) (fun α hα => hα.1)
  obtain ⟨r, hr⟩ := exists_pow_eq_units (N := N) hNpos s
  let f : Fin τ.rank → Fin τ.rank → Lˣ := fun i => cochar (N • Pi.single i 1) (r i)
  let d : Fin τ.rank → ModGL τ L := fun i => rootDiagUnit τ (f i)
  have hfprod : (List.ofFn f).prod = s := prod_cochar_eq r s hr
  have hEq : rootDiagUnit τ s = (List.ofFn d).prod := by
    rw [← hfprod]
    exact rootDiagUnit_list_prod_eq f
  have hd : ∀ i, d i ∈ famZ a ⊔ rootSpan τ L (familyKernel a) :=
    fun i => rootDiagUnit_cochar_mem_sup_of_mem_closure a (r i) (hN i)
  have hmem : (List.ofFn d).prod ∈ famZ a ⊔ rootSpan τ L (familyKernel a) :=
    Subgroup.list_prod_mem _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact hd i)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (famZ a)
    (rootSpan τ L (familyKernel a)) (famZ_le_normalizer_rootSpan a)
  have hmem' : rootDiagUnit τ s ∈ (famZ a : Set (ModGL τ L)) *
      (rootSpan τ L (familyKernel a) : Set (ModGL τ L)) := by
    rw [← hset, hEq]
    exact hmem
  obtain ⟨z, hz, u, hu, hzu⟩ := Set.mem_mul.1 hmem'
  exact ⟨z, hz, u, hu, hzu.symm⟩

theorem exists_famZ_mul_famS_eq {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) :
    ∀ m ∈ famM a, ∃ z ∈ famZ a, ∃ s ∈ famS a, (m : ModGL τ L) = z * s := by
  intro m hm
  have hmFam : (m : ModGL τ L) ∈ familyGroup a := hm
  obtain ⟨t, ht, q, hq, hmtq⟩ := exists_mul_of_mem_torus_sup_rootSpan
    (S := familyKernel a) (fun α hα => hα.1) hmFam
  obtain ⟨s₀, hs₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨z, hz, u, hu, hzu⟩ := exists_famZ_mul_rootSpan_eq a s₀
  have huq : u * q ∈ rootSpan τ L (familyKernel a) := mul_mem hu hq
  have huqS : u * q ∈ (famS a).map (adjointGroup τ L).subtype := by
    rw [map_famS_subtype_eq_rootSpan]
    exact huq
  obtain ⟨s₁, hs₁, hs₁eq⟩ := Subgroup.mem_map.1 huqS
  refine ⟨z, hz, s₁, hs₁, ?_⟩
  calc (m : ModGL τ L) = t * q := hmtq
    _ = rootDiagUnit τ s₀ * q := by rw [hs₀]
    _ = (z * u) * q := by rw [hzu]
    _ = z * (u * q) := by rw [mul_assoc]
    _ = z * (s₁ : ModGL τ L) := by
      rw [show (s₁ : ModGL τ L) = u * q from hs₁eq]

end CFSG.HardMathSupport.C14Idx
