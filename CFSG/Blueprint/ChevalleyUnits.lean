module

public import CFSG.Blueprint.Chevalley

public noncomputable section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

private theorem height_add_smul_single (v : Fin τ.rank → ℤ) (i : Fin τ.rank) (k : ℤ) :
    height (v + k • Pi.single i 1) = height v + k := by
  simp [height, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem height_sub_smul_single (v : Fin τ.rank → ℤ) (i : Fin τ.rank) (k : ℤ) :
    height (v - k • Pi.single i 1) = height v - k := by
  simp [height, Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem height_single (i : Fin τ.rank) : height (Pi.single i (1 : ℤ)) = 1 := by
  simp [height]

private theorem height_neg_single (i : Fin τ.rank) : height (-Pi.single i (1 : ℤ)) = -1 := by
  simp [height]

private theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

private theorem rootVec_mem_supported {β : Fin τ.rank → ℤ} {s : Set (Label τ)}
    (h : ∀ hβ : IsRoot τ β, Sum.inr ⟨β, hβ⟩ ∈ s) : rootVec τ R β ∈ Finsupp.supported R R s := by
  unfold rootVec
  split_ifs with hβ
  · exact Finsupp.single_mem_supported R _ (h hβ)
  · exact zero_mem _

private theorem hVec_mem_supported {j : Fin τ.rank} {s : Set (Label τ)} (h : Sum.inl j ∈ s) :
    hVec τ R j ∈ Finsupp.supported R R s :=
  Finsupp.single_mem_supported R _ h

theorem xOp_single_sub_mem_supported (i : Fin τ.rank) (c : R) (b : Label τ) :
    xOp τ R i c (Finsupp.single b 1) - Finsupp.single b 1 ∈
      Finsupp.supported R R {b' : Label τ | b.weight < b'.weight} := by
  rw [xOp, Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · dsimp only
    rw [hVec, add_sub_cancel_left]
    refine Submodule.smul_mem _ _ (rootVec_mem_supported fun _ => ?_)
    simp [Label.weight, height_single]
  · dsimp only
    split_ifs with h₁ h₂
    · rw [sub_self]
      exact zero_mem _
    · subst h₂
      rw [add_assoc, add_sub_cancel_left]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hVec_mem_supported ?_))
        (Submodule.smul_mem _ _ (rootVec_mem_supported fun _ => ?_))
      · simp [Label.weight, height_neg_single]
      · simp [Label.weight, height_neg_single, height_single]
    · rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_smul, add_zero, Nat.choose_zero_right, Nat.cast_one,
        pow_zero, mul_one, one_smul, rootVec_of_isRoot hα, add_sub_cancel_right]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (rootVec_mem_supported fun _ => ?_)
      simp only [Set.mem_ofPred_eq, Label.weight, height_add_smul_single]
      omega

theorem yOp_single_sub_mem_supported (i : Fin τ.rank) (c : R) (b : Label τ) :
    yOp τ R i c (Finsupp.single b 1) - Finsupp.single b 1 ∈
      Finsupp.supported R R {b' : Label τ | b'.weight < b.weight} := by
  rw [yOp, Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · dsimp only
    rw [hVec, add_sub_cancel_left]
    refine Submodule.smul_mem _ _ (rootVec_mem_supported fun _ => ?_)
    simp [Label.weight, height_neg_single]
  · dsimp only
    split_ifs with h₁ h₂
    · rw [sub_self]
      exact zero_mem _
    · subst h₂
      rw [add_assoc, add_sub_cancel_left]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hVec_mem_supported ?_))
        (Submodule.smul_mem _ _ (rootVec_mem_supported fun _ => ?_))
      · simp [Label.weight, height_single]
      · simp [Label.weight, height_neg_single, height_single]
    · rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_smul, sub_zero, add_zero, Nat.choose_zero_right,
        Nat.cast_one, pow_zero, mul_one, one_smul, rootVec_of_isRoot hα, add_sub_cancel_right]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (rootVec_mem_supported fun _ => ?_)
      simp only [Set.mem_ofPred_eq, Label.weight, height_sub_smul_single]
      omega

private theorem apply_eq_of_sub_single_mem_supported {ι : Type*} {x : ι →₀ R} {a b : ι}
    {s : Set ι} (hx : x - Finsupp.single b 1 ∈ Finsupp.supported R R s) (ha : a ∉ s) :
    x a = Finsupp.single b 1 a := by
  have h := (Finsupp.mem_supported' R _).1 hx a ha
  rwa [Finsupp.sub_apply, sub_eq_zero] at h

private theorem Label.not_precedes_self (b : Label τ) : ¬b.Precedes b := by
  rcases b with j | α
  · simp [Label.Precedes]
  · simp only [Label.Precedes, lt_self_iff_false, false_or, true_and]
    exact lt_irrefl _

theorem xOp_single_apply_self (i : Fin τ.rank) (c : R) (b : Label τ) :
    xOp τ R i c (Finsupp.single b 1) b = 1 := by
  rw [apply_eq_of_sub_single_mem_supported (xOp_single_sub_mem_supported i c b)
    (lt_irrefl b.weight), Finsupp.single_eq_same]

theorem yOp_single_apply_self (i : Fin τ.rank) (c : R) (b : Label τ) :
    yOp τ R i c (Finsupp.single b 1) b = 1 := by
  rw [apply_eq_of_sub_single_mem_supported (yOp_single_sub_mem_supported i c b)
    (lt_irrefl b.weight), Finsupp.single_eq_same]

theorem xOp_single_apply_eq_zero_of_precedes (i : Fin τ.rank) (c : R) {a b : Label τ}
    (h : b.Precedes a) : xOp τ R i c (Finsupp.single b 1) a = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    exact Label.not_precedes_self a h
  have ha : a ∉ {b' : Label τ | b.weight < b'.weight} := fun h' => by
    rw [Set.mem_ofPred_eq] at h'
    rcases h with h | ⟨h, -⟩ <;> omega
  rw [apply_eq_of_sub_single_mem_supported (xOp_single_sub_mem_supported i c b) ha,
    Finsupp.single_eq_of_ne hab]

theorem yOp_single_apply_eq_zero_of_precedes (i : Fin τ.rank) (c : R) {a b : Label τ}
    (h : a.Precedes b) : yOp τ R i c (Finsupp.single b 1) a = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    exact Label.not_precedes_self a h
  have ha : a ∉ {b' : Label τ | b'.weight < b.weight} := fun h' => by
    rw [Set.mem_ofPred_eq] at h'
    rcases h with h | ⟨h, -⟩ <;> omega
  rw [apply_eq_of_sub_single_mem_supported (yOp_single_sub_mem_supported i c b) ha,
    Finsupp.single_eq_of_ne hab]

theorem det_eq_one_of_single_sub_mem_supported {ι : Type*} [Finite ι] (w : ι → ℤ)
    (f : Module.End R (ι →₀ R))
    (hf : ∀ b, f (Finsupp.single b 1) - Finsupp.single b 1 ∈
      Finsupp.supported R R {b' | w b < w b'}) :
    LinearMap.det f = 1 := by
  classical
  have := Fintype.ofFinite ι
  rw [← LinearMap.det_toMatrix Finsupp.basisSingleOne]
  set A := LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne f
  have hA : ∀ a b, A a b = f (Finsupp.single b 1) a := fun a b => by
    simp [A, LinearMap.toMatrix_apply]
  have hoff : ∀ a b, w a ≤ w b → a ≠ b → A a b = 0 := fun a b hab hne => by
    rw [hA, apply_eq_of_sub_single_mem_supported (hf b) (fun h : w b < w a => by omega),
      Finsupp.single_eq_of_ne hne]
  have htri : A.BlockTriangular fun l => -w l := fun a b hab => by
    simp only at hab
    exact hoff a b (by omega) (by rintro rfl; omega)
  rw [htri.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have hblock : A.toSquareBlock (fun l => -w l) k = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, hA, apply_eq_of_sub_single_mem_supported (hf a) (lt_irrefl (w a)),
        Finsupp.single_eq_same]
    · rw [Matrix.one_apply_ne fun h => hab (congrArg Subtype.val h), hoff a b (by omega) hab]
  rw [hblock, Matrix.det_one]

theorem det_xOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank) (c : R) :
    LinearMap.det (xOp τ R i c) = 1 :=
  det_eq_one_of_single_sub_mem_supported Label.weight _ (xOp_single_sub_mem_supported i c)

theorem det_yOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank) (c : R) :
    LinearMap.det (yOp τ R i c) = 1 :=
  det_eq_one_of_single_sub_mem_supported (fun b : Label τ => -b.weight) _ fun b => by
    refine Finsupp.supported_mono ?_ (yOp_single_sub_mem_supported i c b)
    intro b' (hb' : b'.weight < b.weight)
    exact neg_lt_neg hb'

theorem isNilpotent_sub_one_of_single_sub_mem_supported {ι : Type*} [Finite ι] (w : ι → ℤ)
    (f : Module.End R (ι →₀ R))
    (hf : ∀ b, f (Finsupp.single b 1) - Finsupp.single b 1 ∈
      Finsupp.supported R R {b' | w b < w b'}) :
    IsNilpotent (f - 1) := by
  obtain ⟨M, hM⟩ := (Set.finite_range w).bddAbove
  obtain ⟨m, hm⟩ := (Set.finite_range w).bddBelow
  have step : ∀ t : ℤ, Finsupp.supported R R {b | t ≤ w b} ≤
      (Finsupp.supported R R {b | t + 1 ≤ w b}).comap (f - 1) := by
    intro t
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply]
    refine Finsupp.supported_mono (fun b' hb' => ?_) (hf b)
    rw [Set.mem_ofPred_eq] at hb hb' ⊢
    omega
  have key : ∀ (n : ℕ) (x : ι →₀ R),
      ((f - 1) ^ n) x ∈ Finsupp.supported R R {b | m + n ≤ w b} := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [Finsupp.mem_supported]
      intro b _
      rw [Set.mem_ofPred_eq, Nat.cast_zero, add_zero]
      exact hm ⟨b, rfl⟩
    | succ n ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply]
      refine Finsupp.supported_mono (fun b hb => ?_) (step _ (ih x))
      rw [Set.mem_ofPred_eq] at hb ⊢
      omega
  refine ⟨(M - m + 1).toNat, LinearMap.ext fun x => ?_⟩
  have hx := key (M - m + 1).toNat x
  rw [Finsupp.mem_supported] at hx
  rw [LinearMap.zero_apply, ← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  have h1 := hx hb
  rw [Set.mem_ofPred_eq] at h1
  have h2 := hM ⟨b, rfl⟩
  have h3 := Int.self_le_toNat (M - m + 1)
  omega

theorem isNilpotent_xOp_sub_one [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank)
    (c : R) : IsNilpotent (xOp τ R i c - 1) :=
  isNilpotent_sub_one_of_single_sub_mem_supported Label.weight _
    (xOp_single_sub_mem_supported i c)

theorem isNilpotent_yOp_sub_one [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank)
    (c : R) : IsNilpotent (yOp τ R i c - 1) :=
  isNilpotent_sub_one_of_single_sub_mem_supported (fun b : Label τ => -b.weight) _ fun b => by
    refine Finsupp.supported_mono ?_ (yOp_single_sub_mem_supported i c b)
    intro b' (hb' : b'.weight < b.weight)
    exact neg_lt_neg hb'

theorem isUnit_xOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank) (c : R) :
    IsUnit (xOp τ R i c) := by
  convert IsNilpotent.isUnit_one_add (R := Module.End R (RootModule τ R))
    (isNilpotent_xOp_sub_one i c) using 1
  exact (add_sub_cancel (1 : Module.End R (RootModule τ R)) _).symm

theorem isUnit_yOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank) (c : R) :
    IsUnit (yOp τ R i c) := by
  convert IsNilpotent.isUnit_one_add (R := Module.End R (RootModule τ R))
    (isNilpotent_yOp_sub_one i c) using 1
  exact (add_sub_cancel (1 : Module.End R (RootModule τ R)) _).symm

theorem exists_mem_adjointGroup_xOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] {K : Type*}
    [Field K] (i : Fin τ.rank) (c : K) :
    ∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = xOp τ K i c :=
  ⟨(isUnit_xOp i c).unit, Subgroup.subset_closure ⟨i, c, Or.inl (isUnit_xOp i c).unit_spec⟩,
    (isUnit_xOp i c).unit_spec⟩

theorem exists_mem_adjointGroup_yOp [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] {K : Type*}
    [Field K] (i : Fin τ.rank) (c : K) :
    ∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = yOp τ K i c :=
  ⟨(isUnit_yOp i c).unit, Subgroup.subset_closure ⟨i, c, Or.inr (isUnit_yOp i c).unit_spec⟩,
    (isUnit_yOp i c).unit_spec⟩

theorem simple_root_operator_units [Finite {v : Fin τ.rank → ℤ // IsRoot τ v}] (i : Fin τ.rank)
    (c : R) :
    (∀ a b : Label τ, b.Precedes a → xOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, xOp τ R i c (Finsupp.single b 1) b = 1) ∧
      (∀ a b : Label τ, a.Precedes b → yOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, yOp τ R i c (Finsupp.single b 1) b = 1) ∧
      LinearMap.det (xOp τ R i c) = 1 ∧ LinearMap.det (yOp τ R i c) = 1 ∧
      IsUnit (xOp τ R i c) ∧ IsUnit (yOp τ R i c) :=
  ⟨fun _ _ => xOp_single_apply_eq_zero_of_precedes i c, xOp_single_apply_self i c,
    fun _ _ => yOp_single_apply_eq_zero_of_precedes i c, yOp_single_apply_self i c,
    det_xOp i c, det_yOp i c, isUnit_xOp i c, isUnit_yOp i c⟩

end CFSG.Blueprint.Chevalley
