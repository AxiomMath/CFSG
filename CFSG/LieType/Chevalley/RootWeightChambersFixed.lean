module

public import CFSG.LieType.Chevalley.RootWeightChambersAmbient
public import CFSG.LieType.Chevalley.FoldedLengthSigns

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootWeightSpace
open scoped RealInnerProductSpace

variable (t : TwistTag)

theorem symmetrizedCartan_twist : t.tag.symmetrizedCartan = t.tag.cartan := by
  cases t <;> exact Matrix.one_mul _

theorem symmetrizer_twist (i : Fin t.tag.rank) : t.tag.symmetrizer i i = 1 := by
  cases t <;> exact Matrix.one_apply_eq i

theorem card_orbit_pos (a : Fin t.foldedTag.rank) : 0 < (t.orbit a).card := by
  obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
  exact Finset.card_pos.2 ⟨i, t.mem_orbit_orbitIndex i⟩

variable {t}

theorem apply_eq_of_orbitIndex_eq
    {x : RootWeightSpace t.tag} (hx : x ∈ twistFixedSpace t)
    {i j : Fin t.tag.rank} (h : t.orbitIndex j = t.orbitIndex i) : x j = x i := by
  have hρ := mem_twistFixedSpace_iff.1 hx
  rcases (t.orbitIndex_eq_iff).1 h with rfl | rfl | rfl
  · rfl
  · exact hρ i
  · rw [hρ, hρ]

theorem inner_single_perm
    {x : RootWeightSpace t.tag} (hx : x ∈ twistFixedSpace t)
    (i : Fin t.tag.rank) :
    ⟪ofLattice (Pi.single (t.perm i) 1), x⟫ = ⟪ofLattice (Pi.single i 1), x⟫ := by
  have hρ := mem_twistFixedSpace_iff.1 hx
  rw [inner_single_left, inner_single_left, symmetrizedCartan_twist,
    ← Equiv.sum_comp t.perm (fun l => (t.tag.cartan (t.perm i) l : ℝ) * x l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [t.cartan_perm, hρ]

theorem inner_single_eq_of_orbitIndex_eq
    {x : RootWeightSpace t.tag}
    (hx : x ∈ twistFixedSpace t) {i j : Fin t.tag.rank} (h : t.orbitIndex j = t.orbitIndex i) :
    ⟪ofLattice (Pi.single j 1), x⟫ = ⟪ofLattice (Pi.single i 1), x⟫ := by
  rcases (t.orbitIndex_eq_iff).1 h with rfl | rfl | rfl
  · rfl
  · exact inner_single_perm hx i
  · rw [inner_single_perm hx, inner_single_perm hx]

theorem ofLattice_orbitSum
    (a : Fin t.foldedTag.rank) :
    ofLattice (t.orbitSum a) = ∑ j ∈ t.orbit a, ofLattice (Pi.single j 1) := by
  rw [TwistTag.orbitSum, ofLattice_sum]

theorem inner_orbitSum
    {x : RootWeightSpace t.tag} (hx : x ∈ twistFixedSpace t)
    {a : Fin t.foldedTag.rank} {j : Fin t.tag.rank} (hj : j ∈ t.orbit a) :
    ⟪ofLattice (t.orbitSum a), x⟫ = (t.orbit a).card * ⟪ofLattice (Pi.single j 1), x⟫ := by
  rw [ofLattice_orbitSum, sum_inner, Finset.sum_congr rfl fun k hk =>
    inner_single_eq_of_orbitIndex_eq hx
      (((t.mem_orbit_iff).1 hk).trans ((t.mem_orbit_iff).1 hj).symm),
    Finset.sum_const, nsmul_eq_mul]

theorem orbitSum_mem_twistFixedSpace
    (a : Fin t.foldedTag.rank) :
    ofLattice (t.orbitSum a) ∈ twistFixedSpace t :=
  ofLattice_mem_twistFixedSpace (t.orbitSum_mem_fixedLattice a)

theorem inner_single_orbitSum
    {a : Fin t.foldedTag.rank} {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) : ⟪ofLattice (Pi.single j 1), ofLattice (t.orbitSum a)⟫ = 2 := by
  rw [ofLattice_orbitSum, inner_sum, Finset.sum_eq_single j]
  · rw [inner_single_left, Finset.sum_eq_single j]
    · simp [symmetrizedCartan_twist, Tag.cartan_self]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k hk hkj
    rw [inner_single_left, Finset.sum_eq_single k]
    · simp [symmetrizedCartan_twist, t.cartan_eq_zero_of_mem_orbit hj hk (Ne.symm hkj)]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · intro h
    exact absurd hj h

theorem inner_orbitSum_self
    (a : Fin t.foldedTag.rank) :
    ⟪ofLattice (t.orbitSum a), ofLattice (t.orbitSum a)⟫ = 2 * (t.orbit a).card := by
  obtain ⟨j, hj⟩ : (t.orbit a).Nonempty := Finset.card_pos.1 (card_orbit_pos t a)
  rw [inner_orbitSum (orbitSum_mem_twistFixedSpace a) hj, inner_single_orbitSum hj]
  ring

theorem inner_orbitSum_self_pos
    (a : Fin t.foldedTag.rank) :
    0 < ⟪ofLattice (t.orbitSum a), ofLattice (t.orbitSum a)⟫ := by
  rw [inner_orbitSum_self]
  have : (0 : ℝ) < (t.orbit a).card := by exact_mod_cast card_orbit_pos t a
  linarith

theorem weylIsometry_simple_twist
    (j : Fin t.tag.rank) (y : RootWeightSpace t.tag) :
    weylIsometry t.tag (simple t.tag j) y =
      y - ⟪ofLattice (Pi.single j 1), y⟫ • ofLattice (Pi.single j 1) := by
  rw [weylIsometry_simple, inner_single_left_eq, symmetrizer_twist, Int.cast_one, one_mul]

theorem inner_single_single
    (j k : Fin t.tag.rank) :
    ⟪ofLattice (Pi.single j 1), ofLattice (Pi.single k 1)⟫ =
      (t.tag.symmetrizedCartan j k : ℝ) := by
  rw [inner_single_left, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem weylIsometry_wordProd_orbit
    {a : Fin t.foldedTag.rank} {x : RootWeightSpace t.tag}
    {d : ℝ} (hd : ∀ j ∈ t.orbit a, ⟪ofLattice (Pi.single j 1), x⟫ = d) :
    ∀ L : List (Fin t.tag.rank), L.Nodup → (∀ j ∈ L, j ∈ t.orbit a) →
      weylIsometry t.tag ((coxeterSystem t.tag).wordProd L) x =
        x - d • ∑ j ∈ L.toFinset, ofLattice (Pi.single j 1 : Fin t.tag.rank → ℤ)
  | [], _, _ => by simp
  | j :: L, hL, hLa => by
    rw [List.nodup_cons] at hL
    have hj : j ∈ t.orbit a := hLa j List.mem_cons_self
    have ih := weylIsometry_wordProd_orbit hd L hL.2 fun k hk => hLa k (List.mem_cons_of_mem _ hk)
    have hjL : j ∉ L.toFinset := fun h => hL.1 (List.mem_toFinset.1 h)
    have h0 : ⟪ofLattice (Pi.single j 1),
        ∑ k ∈ L.toFinset, ofLattice (Pi.single k 1 : Fin t.tag.rank → ℤ)⟫ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkj : j ≠ k := fun h => hjL (h ▸ hk)
      rw [inner_single_single, symmetrizedCartan_twist,
        t.cartan_eq_zero_of_mem_orbit hj (hLa k (List.mem_cons_of_mem _ (List.mem_toFinset.1 hk)))
          hkj, Int.cast_zero]
    rw [CoxeterSystem.wordProd_cons, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      ih, weylIsometry_simple_twist, inner_sub_right, inner_smul_right, h0, mul_zero, sub_zero,
      hd j hj, List.toFinset_cons, Finset.sum_insert hjL, smul_add]
    abel

theorem weylIsometry_orbitReflection
    {x : RootWeightSpace t.tag} (hx : x ∈ twistFixedSpace t)
    (a : Fin t.foldedTag.rank) :
    weylIsometry t.tag (t.orbitReflection a) x =
      x - (2 * ⟪ofLattice (t.orbitSum a), x⟫ /
        ⟪ofLattice (t.orbitSum a), ofLattice (t.orbitSum a)⟫) • ofLattice (t.orbitSum a) := by
  obtain ⟨j, hj⟩ : (t.orbit a).Nonempty := Finset.card_pos.1 (card_orbit_pos t a)
  have hd : ∀ k ∈ t.orbit a, ⟪ofLattice (Pi.single k 1), x⟫ = ⟪ofLattice (Pi.single j 1), x⟫ :=
    fun k hk => inner_single_eq_of_orbitIndex_eq hx
      (((t.mem_orbit_iff).1 hk).trans ((t.mem_orbit_iff).1 hj).symm)
  have hword : (t.orbitWord a).toFinset = t.orbit a := by
    ext k
    rw [List.mem_toFinset, t.mem_orbitWord]
  rw [TwistTag.orbitReflection, weylIsometry_wordProd_orbit hd _ (t.nodup_orbitWord a)
      fun k hk => (t.mem_orbitWord).1 hk, hword, ← ofLattice_orbitSum, inner_orbitSum hx hj,
    inner_orbitSum_self]
  have hc : (0 : ℝ) < (t.orbit a).card := by exact_mod_cast card_orbit_pos t a
  congr 2
  field_simp

theorem sum_smul_orbitSum_apply
    (c : Fin t.foldedTag.rank → ℝ) (j : Fin t.tag.rank) :
    (∑ a, c a • ofLattice (t.orbitSum a)) j = c (t.orbitIndex j) := by
  have h : ∀ a, (c a • ofLattice (t.orbitSum a)) j =
      if t.orbitIndex j = a then c a else 0 := fun a => by
    change c a * ((t.orbitSum a j : ℤ) : ℝ) = _
    rw [t.orbitSum_eq]
    by_cases hja : t.orbitIndex j = a <;> simp [hja]
  rw [RootWeightSpace.sum_apply]
  simp only [h]
  rw [Finset.sum_ite_eq]
  simp

theorem linearIndependent_orbitSum :
    LinearIndependent ℝ fun a : Fin t.foldedTag.rank =>
      (⟨ofLattice (t.orbitSum a), orbitSum_mem_twistFixedSpace a⟩ : twistFixedSpace t) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hc' : ∑ a, c a • ofLattice (t.orbitSum a) = 0 := by
    have := congrArg Subtype.val hc
    simpa using this
  obtain ⟨j, rfl⟩ := t.exists_orbitIndex_eq a
  have := congrArg (fun x : RootWeightSpace t.tag => x j) hc'
  simp only [sum_smul_orbitSum_apply] at this
  simpa using this

theorem span_orbitSum :
    Submodule.span ℝ (Set.range fun a : Fin t.foldedTag.rank =>
      (⟨ofLattice (t.orbitSum a), orbitSum_mem_twistFixedSpace a⟩ : twistFixedSpace t)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  choose rep hrep using t.exists_orbitIndex_eq
  have hx : (x : RootWeightSpace t.tag) =
      ∑ a, (x : RootWeightSpace t.tag) (rep a) • ofLattice (t.orbitSum a) := by
    ext j
    rw [sum_smul_orbitSum_apply]
    exact (apply_eq_of_orbitIndex_eq x.2 (hrep (t.orbitIndex j))).symm
  have hx' : x = ∑ a, (x : RootWeightSpace t.tag) (rep a) •
      (⟨ofLattice (t.orbitSum a), orbitSum_mem_twistFixedSpace a⟩ : twistFixedSpace t) := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hx
  rw [hx']
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem heightVec_mem_twistFixedSpace
    : heightVec t.tag ∈ twistFixedSpace t := by
  change realExt (permLatticeLinear t.perm) (heightVec t.tag) = heightVec t.tag
  refine eq_heightVec_iff.1 fun j => ?_
  rw [inner_single_left]
  simp only [realExt_permLatticeLinear_apply]
  rw [← Equiv.sum_comp t.perm]
  simp only [Equiv.symm_apply_apply]
  have h := inner_single_heightVec (τ := t.tag) (t.perm.symm j)
  rw [inner_single_left] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hc := t.cartan_perm (t.perm.symm j) l
  rw [Equiv.apply_symm_apply] at hc
  rw [symmetrizedCartan_twist, hc]

theorem inner_orbitSum_heightVec_pos
    (a : Fin t.foldedTag.rank) :
    0 < ⟪ofLattice (t.orbitSum a), heightVec t.tag⟫ := by
  obtain ⟨j, hj⟩ : (t.orbit a).Nonempty := Finset.card_pos.1 (card_orbit_pos t a)
  rw [inner_orbitSum heightVec_mem_twistFixedSpace hj, inner_single_heightVec, mul_one]
  exact_mod_cast card_orbit_pos t a

theorem inner_weylIsometry_orbitSum_nonpos
    {w : WeylGroup t.tag} {a : Fin t.foldedTag.rank}
    (hneg : ∀ j ∈ t.orbit a, height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) < 0)
    {x : RootWeightSpace t.tag} (hx : ∀ k, 0 ≤ ⟪ofLattice (Pi.single k 1), x⟫) :
    ⟪weylIsometry t.tag w (ofLattice (t.orbitSum a)), x⟫ ≤ 0 := by
  rw [weylIsometry_ofLattice]
  refine inner_ofLattice_nonpos_of_single (fun k => ?_) hx
  rw [TwistTag.orbitSum, Finset.smul_sum, Finset.sum_apply]
  exact Finset.sum_nonpos fun j hj =>
    (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single t.tag j) w)).1 (hneg j hj) k

theorem eq_one_of_forall_weylIsometry_eq
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (h : ∀ x ∈ twistFixedSpace t, weylIsometry t.tag w x = x) : w = 1 :=
  eq_one_of_forall_smul_fixedLattice t hw fun v hv => ofLattice_injective (by
    rw [← weylIsometry_ofLattice]
    exact h _ (ofLattice_mem_twistFixedSpace hv))

theorem exists_orbitLength_mul_lt
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) (h1 : w ≠ 1) :
    ∃ a, t.orbitLength (w * t.orbitReflection a) < t.orbitLength w ∧
      ∀ j ∈ t.orbit a, height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) < 0 := by
  obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t hw h1
  have := (length_mul_orbitReflection_of_neg t hw ha).1
  exact ⟨a, by omega, ha⟩

end CFSG.LieType.Chevalley
