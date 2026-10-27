module

public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.OppositeNoncommutativity
public import CFSG.GroupActions.SplitBNPair

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.GroupActions
open scoped Pointwise

variable (τ : Tag) (K : Type) [Field K]

abbrev borelSub
    : Subgroup (adjointGroup τ K) :=
  (borelGroup τ K).subgroupOf (adjointGroup τ K)

abbrev monomialSub
    : Subgroup (adjointGroup τ K) :=
  (monomialSubgroup τ K).subgroupOf (adjointGroup τ K)

abbrev posUnipotentSub
    : Subgroup (adjointGroup τ K) :=
  (posUnipotent τ K).subgroupOf (adjointGroup τ K)

abbrev torusSub
    : Subgroup (adjointGroup τ K) :=
  (torusGroup τ K).subgroupOf (adjointGroup τ K)

@[expose] def weylRep
    (i : Fin τ.rank) : monomialSub τ K :=
  ⟨⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩, weylElt_mem_monomialSubgroup i⟩

variable {τ K}

theorem borelGroup_le_adjointGroup'
    : borelGroup τ K ≤ adjointGroup τ K :=
  ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem monomialSubgroup_le_adjointGroup' :
    monomialSubgroup τ K ≤ adjointGroup τ K :=
  ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).2

theorem posUnipotent_le_adjointGroup
    : posUnipotent τ K ≤ adjointGroup τ K :=
  le_sup_right.trans borelGroup_le_adjointGroup'

theorem borelSub_inf_monomialSub :
    borelSub τ K ⊓ monomialSub τ K = torusSub τ K := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [← Subgroup.mem_inf, (borel_weyl_intersection τ K).1]

theorem mem_torusGroup_of_mem_inf
    {g : adjointGroup τ K}
    (hg : g ∈ borelSub τ K ⊓ monomialSub τ K) : (g : ModGL τ K) ∈ torusGroup τ K := by
  rw [borelSub_inf_monomialSub] at hg
  exact hg

instance normal_borelSub_inf_monomialSub :
    ((borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K)).Normal := by
  have hN := (Subgroup.normal_subgroupOf_iff le_sup_left).1
    (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.1
  refine (Subgroup.normal_subgroupOf_iff inf_le_right).2 fun h k hh hk => ?_
  rw [borelSub_inf_monomialSub] at hh ⊢
  exact hN _ _ hh hk

theorem mem_borelSub_doubleCoset
    {g z : adjointGroup τ K}
    (h : (z : ModGL τ K) ∈
      (borelGroup τ K : Set (ModGL τ K)) * {(g : ModGL τ K)} * (borelGroup τ K : Set _)) :
    z ∈ (borelSub τ K : Set (adjointGroup τ K)) * {g} * (borelSub τ K : Set _) := by
  obtain ⟨b, hb, b', hb', hz⟩ := DoubleCoset.mem_doubleCoset.1 h
  exact DoubleCoset.mem_doubleCoset.2 ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, hb,
    ⟨b', borelGroup_le_adjointGroup' hb'⟩, hb', Subtype.ext hz⟩

@[expose] def monomialSubHom :
    monomialSub τ K →* WeylGroup τ :=
  (weylQuotientHom τ K).comp
    (Subgroup.subgroupOfEquivOfLe monomialSubgroup_le_adjointGroup').toMonoidHom

theorem monomialSubHom_weylRep
    (i : Fin τ.rank) :
    monomialSubHom (weylRep τ K i) = simple τ i :=
  weylQuotientHom_eq (mapsRootLines_weylElt i)

theorem monomialSubHom_surjective :
    Function.Surjective (monomialSubHom (τ := τ) (K := K)) :=
  fun w => ⟨⟨⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩,
    Subgroup.mem_sup_right (canonicalRep_mem_closure _ K w)⟩,
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)⟩

theorem monomialSubHom_ker :
    (monomialSubHom (τ := τ) (K := K)).ker =
      (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, borelSub_inf_monomialSub]
  constructor
  · intro hx
    obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets x.2
    replace hxk : ((x : adjointGroup τ K) : ModGL τ K) = k * canonicalRep (coxeterSystem τ) K w :=
      hxk
    have hmaps : MapsRootLines ((x : adjointGroup τ K) : ModGL τ K) w := by
      rw [hxk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
    have hw : w = 1 := (Eq.symm (weylQuotientHom_eq hmaps : monomialSubHom x = w)).trans hx
    change ((x : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K
    rw [hxk, hw, canonicalRep_one, mul_one]
    exact hk
  · intro hx
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hx)

@[expose] def monomialSubQuotientEquiv :
    monomialSub τ K ⧸ (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K) ≃*
      WeylGroup τ :=
  (QuotientGroup.quotientMulEquivOfEq monomialSubHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ monomialSubHom_surjective)

theorem monomialSubQuotientEquiv_mk
    (x : monomialSub τ K) :
    monomialSubQuotientEquiv (x : monomialSub τ K ⧸
      (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K)) = monomialSubHom x :=
  rfl

theorem simple_injective
    : Function.Injective (simple τ) := fun i j h => by
  by_contra hij
  have := congrArg (fun w : WeylGroup τ => (w • (Pi.single i 1 : Fin τ.rank → ℤ)) i) h
  simp only [simple_smul, reflect_single_self, reflect_apply_of_ne j hij, Pi.neg_apply,
    Pi.single_eq_same] at this
  omega

theorem orderOf_simple
    (i : Fin τ.rank) : orderOf (simple τ i) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ((coxeterSystem τ).simple_sq i) fun h => ?_
  have := (coxeterSystem τ).length_simple i
  rw [show (coxeterSystem τ).simple i = 1 from h, (coxeterSystem τ).length_one] at this
  exact zero_ne_one this

theorem borelSub_sup_monomialSub
    : borelSub τ K ⊔ monomialSub τ K = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  have hg : (g : ModGL τ K) ∈ (adjointGroup τ K : Set (ModGL τ K)) := g.2
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hw
  have e : g = ⟨b, borelGroup_le_adjointGroup' hb⟩ *
      ⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩ *
      ⟨b', borelGroup_le_adjointGroup' hb'⟩ := Subtype.ext hbb.symm
  rw [e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right
    (Subgroup.mem_sup_right (canonicalRep_mem_closure _ K w)))) (Subgroup.mem_sup_left hb')

theorem weylElt_mul_borelGroup_mul_canonicalRep_subset
    (i : Fin τ.rank) (w : WeylGroup τ) :
    ({weylElt τ K i 1} : Set (ModGL τ K)) * (borelGroup τ K : Set (ModGL τ K)) *
        {canonicalRep (coxeterSystem τ) K w} ⊆
      bruhatCell τ K (simple τ i * w) ∪ bruhatCell τ K w := by
  rintro _ ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
  refine bruhatCell_simple_mul_subset i w ?_
  have := mem_bruhatCell_simple_mul (w := w) (i := i) (one_mem _) hb (one_mem _) (one_mem _)
  simpa using this

theorem weylRep_mul_borelSub_mul_subset
    (i : Fin τ.rank) {x : adjointGroup τ K}
    (hx : x ∈ monomialSub τ K) :
    {((weylRep τ K i : monomialSub τ K) : adjointGroup τ K)} *
        (borelSub τ K : Set (adjointGroup τ K)) * {x} ⊆
      (borelSub τ K : Set (adjointGroup τ K)) *
          {((weylRep τ K i : monomialSub τ K) : adjointGroup τ K) * x} *
          (borelSub τ K : Set (adjointGroup τ K)) ∪
        (borelSub τ K : Set (adjointGroup τ K)) * {x} *
          (borelSub τ K : Set (adjointGroup τ K)) := by
  intro y hy
  obtain ⟨_, ⟨n', hn', b, hb, rfl⟩, q, hq, rfl⟩ := hy
  rw [Set.mem_singleton_iff] at hn' hq
  rw [hn', hq]
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hx
  replace hxk : (x : ModGL τ K) = k * canonicalRep (coxeterSystem τ) K w := hxk
  have hkB : k ∈ borelGroup τ K := torusGroup_le_borelGroup hk
  have hmem : weylElt τ K i 1 * ((b : ModGL τ K) * k) * canonicalRep (coxeterSystem τ) K w ∈
      bruhatCell τ K (simple τ i) * bruhatCell τ K w := by
    have := mem_bruhatCell_simple_mul (w := w) (i := i) (one_mem _) (mul_mem hb hkB) (one_mem _)
      (one_mem _)
    simpa [mul_assoc] using this
  have hy : ((((weylRep τ K i : monomialSub τ K) : adjointGroup τ K) * b * x :
      adjointGroup τ K) : ModGL τ K) =
        weylElt τ K i 1 * ((b : ModGL τ K) * k) * canonicalRep (coxeterSystem τ) K w := by
    change weylElt τ K i 1 * (b : ModGL τ K) * (x : ModGL τ K) = _
    rw [hxk]
    group
  rcases bruhatCell_simple_mul_subset i w hmem with h | h
  · left
    refine mem_borelSub_doubleCoset ?_
    have hnk : weylElt τ K i 1 * k * (weylElt τ K i 1)⁻¹ ∈ torusGroup τ K :=
      (Subgroup.mem_normalizer_iff.1 (weylElt_mem_normalizer_torus τ K i 1) k).1 hk
    have hnn : weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w ∈
        bruhatCell τ K (simple τ i * w) := by
      rw [weylElt_mul_canonicalRep]
      split_ifs
      · exact canonicalRep_mem_bruhatCell _
      · exact mem_bruhatCell.2 ⟨torusElt τ K i (-1),
          torusGroup_le_borelGroup (torusElt_mem_torusGroup i (-1)), 1, one_mem _, by
            rw [mul_one]⟩
    have hnx : ((((weylRep τ K i : monomialSub τ K) : adjointGroup τ K) * x :
        adjointGroup τ K) : ModGL τ K) ∈ bruhatCell τ K (simple τ i * w) := by
      obtain ⟨c, hc, c', hc', hcc⟩ := mem_bruhatCell.1 hnn
      refine mem_bruhatCell.2 ⟨weylElt τ K i 1 * k * (weylElt τ K i 1)⁻¹ * c,
        mul_mem (torusGroup_le_borelGroup hnk) hc, c', hc', ?_⟩
      change _ = weylElt τ K i 1 * (x : ModGL τ K)
      rw [hxk, mul_assoc _ c, mul_assoc _ (c * _), hcc]
      group
    rw [doubleCoset_eq_bruhatCell_of_mem hnx, hy]
    exact h
  · right
    refine mem_borelSub_doubleCoset ?_
    have hxw : (x : ModGL τ K) ∈ bruhatCell τ K w :=
      mem_bruhatCell.2 ⟨k, hkB, 1, one_mem _, by rw [hxk, mul_one]⟩
    rw [doubleCoset_eq_bruhatCell_of_mem hxw, hy]
    exact h

theorem weylElt_mul_xUnit_mul_inv_not_mem
    (i : Fin τ.rank) :
    weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ ∉ borelGroup τ K := by
  intro hmem
  have hy : weylElt τ K i 1 * xUnit τ K i 1 * (weylElt τ K i 1)⁻¹ = yUnit τ K i (-1) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit, weylElt_mul_xOp_mul_inv, coe_yUnit]
    simp
  rw [hy] at hmem
  have hup := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 _ hmem
  have hprec : Label.Precedes (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩ : Label τ)
      (Sum.inr ⟨-Pi.single i 1, isRoot_neg_single τ i⟩) := by
    left
    change height (-Pi.single i 1 : Fin τ.rank → ℤ) < height (Pi.single i 1 : Fin τ.rank → ℤ)
    rw [height_neg, height_single]
    omega
  have h0 := hup _ _ hprec
  rw [← rootVec_eq_single_of_isRoot (isRoot_single τ i), coe_yUnit,
    yOp_apply_rootVec_single] at h0
  simp only [rootVec_eq_single_of_isRoot (isRoot_single τ i),
    rootVec_eq_single_of_isRoot (isRoot_neg_single τ i), hVec, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at h0
  rw [Finsupp.single_eq_of_ne, Finsupp.single_eq_of_ne] at h0
  · norm_num at h0
  · exact fun h => by simp at h
  · intro h
    simp only [Sum.inr.injEq, Subtype.mk.injEq] at h
    exact pi_single_ne_neg_pi_single i h.symm

theorem not_weylRep_conj_subset
    (i : Fin τ.rank) :
    ¬ {((weylRep τ K i : monomialSub τ K) : adjointGroup τ K)} *
        (borelSub τ K : Set (adjointGroup τ K)) *
        {((weylRep τ K i : monomialSub τ K) : adjointGroup τ K)⁻¹} ⊆
      (borelSub τ K : Set (adjointGroup τ K)) := by
  intro hsub
  have hx : (⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩ : adjointGroup τ K) ∈ borelSub τ K :=
    xUnit_mem_borelGroup i 1
  exact weylElt_mul_xUnit_mul_inv_not_mem i (hsub ⟨_, ⟨_, rfl, _, hx, rfl⟩, _, rfl, rfl⟩)

theorem posUnipotentSub_le_borelSub :
    posUnipotentSub τ K ≤ borelSub τ K :=
  Subgroup.subgroupOf_mono _ le_sup_right

theorem normal_posUnipotentSub :
    ((posUnipotentSub τ K).subgroupOf (borelSub τ K)).Normal := by
  have hU := (Subgroup.normal_subgroupOf_iff le_sup_right).1
    (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  exact (Subgroup.normal_subgroupOf_iff posUnipotentSub_le_borelSub).2 fun h k hh hk =>
    hU _ _ hh hk

theorem borelSub_eq_mul :
    (borelSub τ K : Set (adjointGroup τ K)) =
      (posUnipotentSub τ K : Set (adjointGroup τ K)) *
        ((borelSub τ K ⊓ monomialSub τ K : Subgroup (adjointGroup τ K)) : Set _) := by
  obtain ⟨-, -, -, -, -, hUH, -⟩ := triangular_borel_structure.{0, 0} τ K
  ext g
  rw [borelSub_inf_monomialSub]
  constructor
  · intro hg
    have hg' : (g : ModGL τ K) ∈ (posUnipotent τ K : Set (ModGL τ K)) *
        (torusGroup τ K : Set (ModGL τ K)) := by
      rw [← hUH]
      exact hg
    obtain ⟨u, hu, h, hh, huh⟩ := hg'
    exact ⟨⟨u, posUnipotent_le_adjointGroup hu⟩, hu,
      ⟨h, borelGroup_le_adjointGroup' (torusGroup_le_borelGroup hh)⟩, hh, Subtype.ext huh⟩
  · rintro ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (posUnipotentSub_le_borelSub hu) (Subgroup.subgroupOf_mono _
      torusGroup_le_borelGroup hh)

theorem posUnipotentSub_inf_torusSub
    : posUnipotentSub τ K ⊓ torusSub τ K = ⊥ := by
  have hinf := (triangular_borel_structure.{0, 0} τ K).2.2.2.1
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Subtype.ext ?_)
  have h : (g : ModGL τ K) ∈ torusGroup τ K ⊓ posUnipotent τ K :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hg).2, (Subgroup.mem_inf.1 hg).1⟩
  rw [hinf, Subgroup.mem_bot] at h
  exact h

theorem posUnipotentSub_sup_torusSub :
    posUnipotentSub τ K ⊔ torusSub τ K = borelSub τ K := by
  refine le_antisymm (sup_le posUnipotentSub_le_borelSub
    (Subgroup.subgroupOf_mono _ torusGroup_le_borelGroup)) fun g hg => ?_
  have hg' : g ∈ (borelSub τ K : Set (adjointGroup τ K)) := hg
  rw [borelSub_eq_mul, borelSub_inf_monomialSub] at hg'
  obtain ⟨u, hu, h, hh, rfl⟩ := hg'
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hh)

theorem isNilpotent_posUnipotentSub
    : Group.IsNilpotent (posUnipotentSub τ K) :=
  (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup)).2
    ((positive_root_triangularity.{0, 0} τ).1 K).2.2.2.1

variable (τ K) in
theorem chevalley_split_bn_pair :
    SplitBN (borelSub τ K) (monomialSub τ K) (posUnipotentSub τ K) (weylRep τ K) ∧
    borelSub τ K ⊓ monomialSub τ K = torusSub τ K ∧
    (∃ ψ : WeylGroup τ ≃*
        monomialSub τ K ⧸ (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K),
      ∀ i, ψ (simple τ i) = (weylRep τ K i : monomialSub τ K ⧸
        (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K))) ∧
    (∀ (i : Fin τ.rank) (w : WeylGroup τ),
      ({weylElt τ K i 1} : Set (ModGL τ K)) * (borelGroup τ K : Set (ModGL τ K)) *
          {canonicalRep (coxeterSystem τ) K w} ⊆
        bruhatCell τ K (simple τ i * w) ∪ bruhatCell τ K w) ∧
    ((posUnipotentSub τ K).subgroupOf (borelSub τ K)).Normal ∧
    posUnipotentSub τ K ⊓ torusSub τ K = ⊥ ∧
    posUnipotentSub τ K ⊔ torusSub τ K = borelSub τ K ∧
    ∀ [Finite K] (p : ℕ) [CharP K p],
      Finite (posUnipotentSub τ K) ∧ IsPGroup p (posUnipotentSub τ K) := by
  set Q := monomialSub τ K ⧸ (borelSub τ K ⊓ monomialSub τ K).subgroupOf (monomialSub τ K)
  set e : Q ≃* WeylGroup τ := monomialSubQuotientEquiv
  have he : ∀ i, e (weylRep τ K i : Q) = simple τ i := fun i => monomialSubHom_weylRep i
  refine ⟨⟨normal_borelSub_inf_monomialSub, borelSub_sup_monomialSub, fun i j h => ?_,
      fun i => ?_, ?_, fun i x hx => weylRep_mul_borelSub_mul_subset i hx,
      not_weylRep_conj_subset, posUnipotentSub_le_borelSub, normal_posUnipotentSub,
      isNilpotent_posUnipotentSub, fun x hx y hy => ?_, borelSub_eq_mul, ?_⟩,
    borelSub_inf_monomialSub, ⟨e.symm, fun i => (MulEquiv.symm_apply_eq e).2 (he i).symm⟩,
    weylElt_mul_borelGroup_mul_canonicalRep_subset, normal_posUnipotentSub,
    posUnipotentSub_inf_torusSub, posUnipotentSub_sup_torusSub, fun p _ => ?_⟩
  · exact simple_injective (by simpa [he] using congrArg e h)
  · rw [← MulEquiv.orderOf_eq e, he, orderOf_simple]
  · rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.map_top_of_surjective _ e.surjective, MonoidHom.map_closure,
      ← (coxeterSystem τ).subgroup_closure_range_simple]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, he i⟩
  · refine Subtype.ext ?_
    exact (triangular_borel_structure.{0, 0} τ K).1 _ (mem_torusGroup_of_mem_inf hx) _
      (mem_torusGroup_of_mem_inf hy)
  · rw [borelSub_inf_monomialSub]
    exact posUnipotentSub_inf_torusSub
  · obtain ⟨hfin, hp⟩ := ((positive_root_triangularity.{0, 0} τ).2 K p)
      |>.imp_right fun h => h.1
    have e' := Subgroup.subgroupOfEquivOfLe (posUnipotent_le_adjointGroup (τ := τ) (K := K))
    exact ⟨Finite.of_equiv _ e'.symm.toEquiv, hp.of_equiv e'.symm⟩

end CFSG.LieType.Chevalley
