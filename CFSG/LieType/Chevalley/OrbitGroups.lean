module

public import CFSG.LieType.Chevalley.TwistUnipotent
public import CFSG.LieType.Chevalley.RelativeWeylTwist
public import CFSG.LieType.Chevalley.RootConj

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

variable (τ) in
@[expose] def supportCheck (ω S : List (Fin τ.rank)) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m =>
    !(decide (0 < height (τ.rootCertificate.root m)) &&
      decide (height (ω.foldr (reflect τ) (τ.rootCertificate.root m)) < 0)) ||
    S.any fun j => decide (τ.rootCertificate.root m = Pi.single j 1)

theorem exists_eq_simpleRoot_of_supportCheck {ω S : List (Fin τ.rank)}
    (h : supportCheck τ ω S = true) {α : Root τ} (hα : 0 < height α.1)
    (hw : height ((coxeterSystem τ).wordProd ω • α).1 < 0) : ∃ j ∈ S, α = simpleRoot τ j := by
  simp only [supportCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, List.any_eq_true] at h
  rcases h (rootPos α) (rootPos_lt α) with h1 | ⟨j, hj, hjα⟩
  · rw [root_rootPos] at h1
    rw [coe_smul_root, wordProd_smul] at hw
    exact absurd hw (h1 hα)
  · refine ⟨j, hj, Subtype.ext ?_⟩
    rw [← root_rootPos α, hjα]
    rfl

variable (K : Type) [Field K]

theorem Uminus_le_of_supportCheck {ω S : List (Fin τ.rank)} (h : supportCheck τ ω S = true) :
    Uminus τ K ((coxeterSystem τ).wordProd ω) ≤
      ⨆ (j : Fin τ.rank) (_ : j ∈ S), (nativeRootSubgroups τ K).X (simpleRoot τ j) := by
  refine iSup₂_le fun α ⟨hα, hw⟩ => ?_
  obtain ⟨j, hj, rfl⟩ := exists_eq_simpleRoot_of_supportCheck h hα hw
  exact le_iSup₂_of_le (f := fun (j : Fin τ.rank) (_ : j ∈ S) =>
    (nativeRootSubgroups τ K).X (simpleRoot τ j)) j hj le_rfl

variable {K}

theorem xElement_injective (i : Fin τ.rank) : Function.Injective (xElement (K := K) i) := by
  intro a b h
  by_contra hab
  apply xElement_ne_one (K := K) (sub_ne_zero.2 hab) (j := i)
  rw [sub_eq_add_neg, xElement_add, ← xElement_inv, h, mul_inv_cancel]

variable [Finite K]

omit [Finite K] in
theorem xElement_mem_Uminus_simple (i : Fin τ.rank) (a : K) :
    xElement i a ∈ Uminus τ K (simple τ i) := by
  refine mem_Uminus_of_mem_X (height_simpleRoot_pos i) ?_ (xElement_mem_X i a)
  change height (simple τ i • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0
  rw [simple_smul, reflect_single_self, height_neg, height_single]
  omega

omit [Finite K] in
theorem xElement_mem_Uplus_simple {i j : Fin τ.rank} (hij : i ≠ j) (b : K) :
    xElement j b ∈ Uplus τ K (simple τ i) := by
  refine mem_Uplus_of_mem_X (height_simpleRoot_pos j) ?_ (xElement_mem_X j b)
  change 0 < height (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ))
  rw [simple_smul]
  exact height_reflect_pos (isRoot_single τ j) (height_simpleRoot_pos j)
    fun h => hij (simpleRoot_injective (Subtype.ext h)).symm

theorem eq_one_of_mem_Uplus_of_mem_Uminus {w : WeylGroup τ} {x : adjointGroup τ K}
    (h₁ : x ∈ Uplus τ K w) (h₂ : x ∈ Uminus τ K w) : x = 1 := by
  have : x ∈ Uplus τ K w ⊓ Uminus τ K w := ⟨h₁, h₂⟩
  rwa [Uplus_inf_Uminus, Subgroup.mem_bot] at this

theorem eq_of_xElement_mul_eq {i : Fin τ.rank} {a a' : K} {y y' : adjointGroup τ K}
    (hy : y ∈ Uplus τ K (simple τ i)) (hy' : y' ∈ Uplus τ K (simple τ i))
    (h : xElement i a * y = xElement i a' * y') : a = a' ∧ y = y' := by
  have h1 : xElement i (-a' + a) = y' * y⁻¹ := by
    rw [xElement_add, ← xElement_inv]
    calc (xElement i a')⁻¹ * xElement i a = (xElement i a')⁻¹ * (xElement i a * y) * y⁻¹ := by
          group
      _ = (xElement i a')⁻¹ * (xElement i a' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have h2 := eq_one_of_mem_Uplus_of_mem_Uminus (h1 ▸ mul_mem hy' (inv_mem hy))
    (xElement_mem_Uminus_simple i (-a' + a))
  have ha : a = a' := by
    have := xElement_injective i (h2.trans (xElement_zero i).symm)
    linear_combination this
  subst ha
  exact ⟨rfl, mul_left_cancel h⟩

omit [Finite K] in
theorem exists_eq_xElement_of_mem {i : Fin τ.rank} {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X (simpleRoot τ i)) : ∃ a : K, x = xElement i a := by
  obtain ⟨a, ha⟩ := ((nativeRootSubgroups τ K).mem_simple i x).1 hx
  exact ⟨a, Subtype.ext ha⟩

omit [Finite K] in
theorem X_simple_le_normalizer {i j : Fin τ.rank} (hij : i ≠ j) (hc : τ.cartan i j = 0) :
    (nativeRootSubgroups τ K).X (simpleRoot τ i) ≤
      Subgroup.normalizer ((nativeRootSubgroups τ K).X (simpleRoot τ j) : Set _) :=
  RootGroupData.le_normalizer_of_conj_mem fun g hg y hy => by
    rw [(commute_of_mem_simple hij hc hg hy).eq, mul_inv_cancel_right]
    exact hy

omit [Finite K] in
theorem exists_eq_xElement_mul_of_mem_sup {i j : Fin τ.rank} (hij : i ≠ j)
    (hc : τ.cartan i j = 0) {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X (simpleRoot τ i) ⊔
      (nativeRootSubgroups τ K).X (simpleRoot τ j)) :
    ∃ a b : K, x = xElement i a * xElement j b := by
  have hx' : x ∈ (((nativeRootSubgroups τ K).X (simpleRoot τ i) ⊔
      (nativeRootSubgroups τ K).X (simpleRoot τ j) : Subgroup _) : Set _) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (X_simple_le_normalizer hij hc)] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  obtain ⟨a, rfl⟩ := exists_eq_xElement_of_mem hy
  obtain ⟨b, rfl⟩ := exists_eq_xElement_of_mem hz
  exact ⟨a, b, rfl⟩

omit [Finite K] in
theorem exists_eq_xElement_mul_mul_of_mem_sup {i j k : Fin τ.rank} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hcij : τ.cartan i j = 0) (hcik : τ.cartan i k = 0)
    (hcjk : τ.cartan j k = 0) {x : adjointGroup τ K}
    (hx : x ∈ (nativeRootSubgroups τ K).X (simpleRoot τ i) ⊔
      (nativeRootSubgroups τ K).X (simpleRoot τ j) ⊔
        (nativeRootSubgroups τ K).X (simpleRoot τ k)) :
    ∃ a b c : K, x = xElement i a * xElement j b * xElement k c := by
  have hn : (nativeRootSubgroups τ K).X (simpleRoot τ i) ⊔
      (nativeRootSubgroups τ K).X (simpleRoot τ j) ≤
      Subgroup.normalizer ((nativeRootSubgroups τ K).X (simpleRoot τ k) : Set _) :=
    sup_le (X_simple_le_normalizer hik hcik) (X_simple_le_normalizer hjk hcjk)
  have hx' : x ∈ (((nativeRootSubgroups τ K).X (simpleRoot τ i) ⊔
      (nativeRootSubgroups τ K).X (simpleRoot τ j) ⊔
        (nativeRootSubgroups τ K).X (simpleRoot τ k) : Subgroup _) : Set _) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  obtain ⟨a, b, rfl⟩ := exists_eq_xElement_mul_of_mem_sup hij hcij hy
  obtain ⟨c, rfl⟩ := exists_eq_xElement_of_mem hz
  exact ⟨a, b, c, rfl⟩

theorem eq_of_xElement_mul_xElement_eq {i j : Fin τ.rank} (hij : i ≠ j) {a a' b b' : K}
    (h : xElement i a * xElement j b = xElement i a' * xElement j b') : a = a' ∧ b = b' := by
  obtain ⟨ha, hb⟩ := eq_of_xElement_mul_eq (xElement_mem_Uplus_simple hij b)
    (xElement_mem_Uplus_simple hij b') h
  exact ⟨ha, xElement_injective j hb⟩

theorem eq_of_xElement_mul_mul_eq {i j k : Fin τ.rank} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {a a' b b' c c' : K}
    (h : xElement i a * xElement j b * xElement k c = xElement i a' * xElement j b' * xElement k c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [mul_assoc, mul_assoc] at h
  obtain ⟨ha, h'⟩ := eq_of_xElement_mul_eq
    (mul_mem (xElement_mem_Uplus_simple hij b) (xElement_mem_Uplus_simple hik c))
    (mul_mem (xElement_mem_Uplus_simple hij b') (xElement_mem_Uplus_simple hik c')) h
  obtain ⟨hb, hc⟩ := eq_of_xElement_mul_xElement_eq hjk h'
  exact ⟨ha, hb, hc⟩

end CFSG.LieType.Chevalley
