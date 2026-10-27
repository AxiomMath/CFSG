module

public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Abstract

variable {G : Type*} [Group G]

theorem subgroupOf_inf_subgroupOf (H K C : Subgroup G) :
    (H ⊓ K).subgroupOf C = H.subgroupOf C ⊓ K.subgroupOf C :=
  Subgroup.comap_inf _ _ _

theorem subgroupOf_covBy_subgroupOf_iff {C A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    A.subgroupOf C ⋖ B.subgroupOf C ↔ A ⋖ B := by
  let f : Subgroup C ↪o Subgroup G := OrderEmbedding.ofMapLEIff (fun H => H.map C.subtype)
    fun _ _ => Subgroup.map_subtype_le_map_subtype
  have hrange : Set.range f = Set.Iic C := by
    ext H
    constructor
    · rintro ⟨H', rfl⟩
      exact Subgroup.map_subtype_le H'
    · intro h
      exact ⟨H.subgroupOf C, Subgroup.map_subgroupOf_eq_of_le h⟩
  have h := Set.OrdConnected.apply_covBy_apply_iff f (hrange ▸ Set.ordConnected_Iic)
    (a := A.subgroupOf C) (b := B.subgroupOf C)
  have hfA : f (A.subgroupOf C) = A := Subgroup.map_subgroupOf_eq_of_le hA
  have hfB : f (B.subgroupOf C) = B := Subgroup.map_subgroupOf_eq_of_le hB
  rw [hfA, hfB] at h
  exact h.symm

theorem normalizer_subgroupOf_eq {U C : Subgroup G} (hUC : U ≤ C) :
    Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) =
      (C ⊓ Subgroup.normalizer (U : Set G)).subgroupOf C := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨fun hx => ⟨x.2, mem_normalizer_of_mem_normalizer_subgroupOf hUC hx⟩,
    fun ⟨_, hx⟩ => Subgroup.mem_normalizer_iff.2 fun y => (Subgroup.mem_normalizer_iff.1 hx) y⟩

variable {ι : Type*} {C U V B B' : Subgroup G} {P Q X Y : ι → Subgroup G}

theorem map_subgroupOf_eq_of_normalizer (hUC : U ≤ C) (hN : C ⊓ Subgroup.normalizer (U : Set G) = B)
    {β : MulAut C} (hβ : (U.subgroupOf C).map β.toMonoidHom = U.subgroupOf C) :
    (B.subgroupOf C).map β.toMonoidHom = B.subgroupOf C := by
  rw [← hN, ← normalizer_subgroupOf_eq hUC, Subgroup.map_equiv_normalizer_eq, hβ]

theorem exists_map_eq_of_covBy (hcov : ∀ A ≤ C, B ⋖ A ↔ ∃ a, A = P a) (hBC : B ≤ C)
    (hPC : ∀ a, P a ≤ C) {β : MulAut C}
    (hβ : (B.subgroupOf C).map β.toMonoidHom = B.subgroupOf C) (a : ι) :
    ∃ b, ((P a).subgroupOf C).map β.toMonoidHom = (P b).subgroupOf C := by
  have h1 : B.subgroupOf C ⋖ (P a).subgroupOf C :=
    (subgroupOf_covBy_subgroupOf_iff hBC (hPC a)).2 ((hcov _ (hPC a)).2 ⟨a, rfl⟩)
  have h2 : B.subgroupOf C ⋖ ((P a).subgroupOf C).map β.toMonoidHom := by
    rw [← hβ]
    exact (apply_covBy_apply_iff (MulEquiv.mapSubgroup β)).2 h1
  have hA : (((P a).subgroupOf C).map β.toMonoidHom).map C.subtype ≤ C :=
    Subgroup.map_subtype_le _
  have hAA : ((((P a).subgroupOf C).map β.toMonoidHom).map C.subtype).subgroupOf C =
      ((P a).subgroupOf C).map β.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [← hAA, subgroupOf_covBy_subgroupOf_iff hBC hA, hcov _ hA] at h2
  obtain ⟨b, hb⟩ := h2
  exact ⟨b, by rw [← hAA, hb]⟩

theorem exists_perm_map_eq [Finite ι] (hBC : B ≤ C) (hB'C : B' ≤ C) (hPC : ∀ a, P a ≤ C)
    (hQC : ∀ a, Q a ≤ C) (hUC : U ≤ C) (hVC : V ≤ C) (hXC : ∀ a, X a ≤ C)
    (hYC : ∀ a, Y a ≤ C) (hcov : ∀ A ≤ C, B ⋖ A ↔ ∃ a, A = P a)
    (hcov' : ∀ A ≤ C, B' ⋖ A ↔ ∃ a, A = Q a) (hPinj : Function.Injective P)
    (hNU : C ⊓ Subgroup.normalizer (U : Set G) = B) (hNV : C ⊓ Subgroup.normalizer (V : Set G) = B')
    (hPV : ∀ a, P a ⊓ V = Y a) (hQU : ∀ a, Q a ⊓ U = X a)
    (hcomm : ∀ a b, a ≠ b → ∀ x ∈ X a, ∀ y ∈ Y b, Commute x y)
    (hnc : ∀ a, ∃ x ∈ X a, ∃ y ∈ Y a, ¬ Commute x y) {β : MulAut C}
    (hβU : (U.subgroupOf C).map β.toMonoidHom = U.subgroupOf C)
    (hβV : (V.subgroupOf C).map β.toMonoidHom = V.subgroupOf C) :
    ∃ π : Equiv.Perm ι, ∀ a, ((X a).subgroupOf C).map β.toMonoidHom = (X (π a)).subgroupOf C ∧
      ((Y a).subgroupOf C).map β.toMonoidHom = (Y (π a)).subgroupOf C := by
  choose π₁ hπ₁ using exists_map_eq_of_covBy hcov hBC hPC
    (map_subgroupOf_eq_of_normalizer hUC hNU hβU)
  choose π₂ hπ₂ using exists_map_eq_of_covBy hcov' hB'C hQC
    (map_subgroupOf_eq_of_normalizer hVC hNV hβV)
  have hY : ∀ a, ((Y a).subgroupOf C).map β.toMonoidHom = (Y (π₁ a)).subgroupOf C := fun a => by
    rw [← hPV, ← hPV, subgroupOf_inf_subgroupOf, subgroupOf_inf_subgroupOf,
      Subgroup.map_inf_eq _ _ _ β.injective, hπ₁, hβV]
  have hX : ∀ a, ((X a).subgroupOf C).map β.toMonoidHom = (X (π₂ a)).subgroupOf C := fun a => by
    rw [← hQU, ← hQU, subgroupOf_inf_subgroupOf, subgroupOf_inf_subgroupOf,
      Subgroup.map_inf_eq _ _ _ β.injective, hπ₂, hβU]
  have h12 : ∀ a, π₂ a = π₁ a := by
    intro a
    by_contra hne
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc a
    have hx' : β ⟨x, hXC a hx⟩ ∈ (X (π₂ a)).subgroupOf C := by
      rw [← hX a]
      exact ⟨⟨x, hXC a hx⟩, hx, rfl⟩
    have hy' : β ⟨y, hYC a hy⟩ ∈ (Y (π₁ a)).subgroupOf C := by
      rw [← hY a]
      exact ⟨⟨y, hYC a hy⟩, hy, rfl⟩
    have hc : Commute (β ⟨x, hXC a hx⟩) (β ⟨y, hYC a hy⟩) := Submonoid.commute_coe_coe.1
      (hcomm _ _ hne _ (Subgroup.mem_subgroupOf.1 hx') _ (Subgroup.mem_subgroupOf.1 hy'))
    have hc' := hc.map β.symm
    simp only [MulEquiv.symm_apply_apply] at hc'
    exact hxy (Submonoid.commute_coe_coe.2 hc')
  have hinj : Function.Injective π₁ := fun a b h => by
    have h1 : ((P a).subgroupOf C).map β.toMonoidHom = ((P b).subgroupOf C).map β.toMonoidHom := by
      rw [hπ₁, hπ₁, h]
    have h2 := Subgroup.map_injective β.injective h1
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (hPC a), inf_of_le_left (hPC b)] at h2
    exact hPinj h2
  refine ⟨Equiv.ofBijective π₁ hinj.bijective_of_finite, fun a => ⟨?_, hY a⟩⟩
  rw [hX a, h12 a]
  rfl

theorem perm_eq_of_map_eq (hXinj : Function.Injective X) (hXC : ∀ a, X a ≤ C) {β : MulAut C}
    {π π' : Equiv.Perm ι}
    (h : ∀ a, ((X a).subgroupOf C).map β.toMonoidHom = (X (π a)).subgroupOf C)
    (h' : ∀ a, ((X a).subgroupOf C).map β.toMonoidHom = (X (π' a)).subgroupOf C) : π = π' := by
  ext a
  have h1 := (h a).symm.trans (h' a)
  rw [Subgroup.subgroupOf_inj, inf_of_le_left (hXC _), inf_of_le_left (hXC _)] at h1
  exact hXinj h1

end Abstract

theorem commute_xUnit_yUnit_of_ne
    {t : TwistTag} {K : Type} [Field K] {i j : Fin t.tag.rank}
    (hij : i ≠ j) (c d : K) : Commute (xUnit t.tag K i c) (yUnit t.tag K j d) := by
  rw [← pinnedX_single, ← pinnedX_neg_single]
  refine pinnedX_commute_of_rootForm_nonneg t.isSimplyLaced (isRoot_single _ i)
    (isRoot_neg_single _ j) (fun h => ?_) ?_ c d
  · have h1 := congrFun h i
    simp [hij] at h1
  · rw [Matrix.mulVec_neg, dotProduct_neg, single_dotProduct, one_mul, Matrix.mulVec_single_one,
      t.symmetrizedCartan_tag, neg_nonneg]
    revert i j
    cases t <;> decide

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (t K σ) in
@[expose] def orbitXSubgroup
    (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  Subgroup.closure (Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K))

variable (t K σ) in
@[expose] def orbitYSubgroup
    (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  Subgroup.closure (Set.range fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K))

theorem orbitYSubgroup_eq
    (a : Fin t.foldedTag.rank) :
    orbitYSubgroup t K σ a =
      rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ =>
      (mem_rootSpan_negSimpleOrbitRoots_iff a).2 ⟨c, hc⟩)
    fun _ hg => Subgroup.subset_closure ((mem_rootSpan_negSimpleOrbitRoots_iff a).1 hg)

theorem coe_orbitXSubgroup
    (a : Fin t.foldedTag.rank) :
    (orbitXSubgroup t K σ a : Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K) := by
  rw [orbitXSubgroup, closure_range_orbitX, coe_rootSpan_simpleOrbitRoots_inf]

theorem coe_orbitYSubgroup
    (a : Fin t.foldedTag.rank) :
    (orbitYSubgroup t K σ a : Set (ModGL t.tag K)) =
      Set.range fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K) := by
  rw [orbitYSubgroup_eq, coe_rootSpan_negSimpleOrbitRoots_inf]

theorem orbitX_mem_orbitXSubgroup
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈ orbitXSubgroup t K σ a :=
  Subgroup.subset_closure ⟨c, rfl⟩

theorem orbitY_mem_orbitYSubgroup
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈ orbitYSubgroup t K σ a :=
  Subgroup.subset_closure ⟨c, rfl⟩

theorem orbitXSubgroup_le
    (a : Fin t.foldedTag.rank) :
    orbitXSubgroup t K σ a ≤ graphFixedRootGroup t K σ :=
  (Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ => hc ▸
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ (orbitX_mem_graphFixedPosUnipotent t σ a c)

theorem orbitYSubgroup_le
    (a : Fin t.foldedTag.rank) :
    orbitYSubgroup t K σ a ≤ graphFixedRootGroup t K σ :=
  (Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ => hc ▸
    graphFixedNegUnipotent_le_graphFixedRootGroup t K σ (orbitY_mem_graphFixedNegUnipotent t σ a c)

theorem natCard_orbitXSubgroup
    (a : Fin t.foldedTag.rank) :
    Nat.card (orbitXSubgroup t K σ a) = Nat.card (orbitField t K σ a) := by
  have hinj : Function.Injective fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K) :=
    fun c c' h => orbitX_injective σ a (Subtype.ext h)
  rw [← Nat.card_range_of_injective hinj, ← coe_orbitXSubgroup]
  rfl

theorem commute_orbitX_orbitY_of_ne
    {a b : Fin t.foldedTag.rank} (hab : a ≠ b)
    (c : orbitField t K σ a) (d : orbitField t K σ b) :
    Commute (orbitX t K σ a c : ModGL t.tag K) (orbitY t K σ b d : ModGL t.tag K) := by
  rw [coe_orbitX, coe_orbitY]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
  refine commute_xUnit_yUnit_of_ne (fun h => hab ?_) _ _
  have h1 := (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.orbitMin_mem a) k)
  have h2 := (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.orbitMin_mem b) l)
  rw [h] at h1
  exact h1.symm.trans h2

theorem not_commute_orbitX_orbitY
    (a : Fin t.foldedTag.rank) :
    ¬ Commute (orbitX t K σ a 1 : ModGL t.tag K) (orbitY t K σ a 1 : ModGL t.tag K) := by
  intro h
  have hker : uSL (1 : orbitField t K σ a) * vSL 1 * (vSL 1 * uSL 1)⁻¹ ∈
      (orbitRankOneHom t K σ a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, orbitRankOneHom_uSL,
      orbitRankOneHom_vSL, h.eq, mul_inv_cancel]
  obtain ⟨l, -, hl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom hker
  have e : ((uSL (1 : orbitField t K σ a) * vSL 1 : SL2 (orbitField t K σ a)) :
      Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) = (l : orbitField t K σ a) •
        ((vSL 1 * uSL 1 : SL2 (orbitField t K σ a)) : Matrix (Fin 2) (Fin 2) _) := by
    have e1 : uSL (1 : orbitField t K σ a) * vSL 1 =
        uSL 1 * vSL 1 * (vSL 1 * uSL 1)⁻¹ * (vSL 1 * uSL 1) := by group
    rw [e1, Matrix.SpecialLinearGroup.coe_mul _ (vSL 1 * uSL 1), hl, smul_one_mul]
  have e01 := congrFun (congrFun e 0) 1
  have e00 := congrFun (congrFun e 0) 0
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at e01 e00
  have h1 : (1 : orbitField t K σ a) = 0 := by linear_combination e00 - e01
  exact one_ne_zero h1

theorem orbitXSubgroup_injective
    : Function.Injective (orbitXSubgroup t K σ) := by
  intro b c h
  by_contra hbc
  have hx : (orbitX t K σ c 1 : ModGL t.tag K) ∈ orbitXSubgroup t K σ b := by
    rw [h]
    exact orbitX_mem_orbitXSubgroup c 1
  rw [← SetLike.mem_coe, coe_orbitXSubgroup] at hx
  obtain ⟨e, he⟩ := hx
  have hcomm := commute_orbitX_orbitY_of_ne (σ := σ) hbc e 1
  rw [show (orbitX t K σ b e : ModGL t.tag K) = orbitX t K σ c 1 from he] at hcomm
  exact not_commute_orbitX_orbitY c hcomm

theorem graphFixedOppositeBorel_le :
    graphFixedOppositeBorel t K σ ≤ graphFixedRootGroup t K σ :=
  sup_le inf_le_right (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ)

theorem graphFixedOppositeMinimalParabolic_le
    (a : Fin t.foldedTag.rank) :
    graphFixedOppositeMinimalParabolic t K σ a ≤ graphFixedRootGroup t K σ :=
  sup_le graphFixedOppositeBorel_le (orbitXSubgroup_le a)

theorem graphFixedRootGroup_inf_normalizer_graphFixedNegUnipotent
    (hσ : Function.Surjective σ) :
    graphFixedRootGroup t K σ ⊓
        Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) =
      graphFixedOppositeBorel t K σ := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  rw [← map_conj_graphFixedPosUnipotent (K := K) (σ := σ) hmax,
    ← Subgroup.map_equiv_normalizer_eq, ← map_conj_self hn,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ,
    map_conj_graphFixedRootBorel hmax hσ]
  rfl

variable (t K σ) in
@[expose] def graphFixedUnipotentStabilizer :
    Subgroup (MulAut (graphFixedRootGroup t K σ)) where
  carrier := {β | ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)).map
      β.toMonoidHom = (graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ) ∧
    ((graphFixedNegUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)).map
      β.toMonoidHom = (graphFixedNegUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)}
  mul_mem' := by
    rintro β γ ⟨hβU, hβV⟩ ⟨hγU, hγV⟩
    exact ⟨by rw [map_mulAut_mul, hγU, hβU], by rw [map_mulAut_mul, hγV, hβV]⟩
  one_mem' := ⟨map_mulAut_one _, map_mulAut_one _⟩
  inv_mem' := by
    rintro β ⟨hβU, hβV⟩
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hβU]
      rw [← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    · conv_lhs => rw [← hβV]
      rw [← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]

variable (t K σ) in
@[expose] def PermutesSimpleOrbitGroups
    (β : MulAut (graphFixedRootGroup t K σ))
    (π : Equiv.Perm (Fin t.foldedTag.rank)) : Prop :=
  ∀ a, ((orbitXSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ)).map β.toMonoidHom =
      (orbitXSubgroup t K σ (π a)).subgroupOf (graphFixedRootGroup t K σ) ∧
    ((orbitYSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ)).map β.toMonoidHom =
      (orbitYSubgroup t K σ (π a)).subgroupOf (graphFixedRootGroup t K σ)

theorem existsUnique_permutesSimpleOrbitGroups
    (σ : K ≃+* K)
    {β : MulAut (graphFixedRootGroup t K σ.toRingHom)}
    (hβ : β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom) :
    ∃! π, PermutesSimpleOrbitGroups t K σ.toRingHom β π := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨hcov, hPinj, hPV, hcov', -, hQU⟩ := exceptional_fixed_minimal_Borel_intersections t K σ
  obtain ⟨π, hπ⟩ := exists_perm_map_eq (graphFixedRootBorel_le t K σ.toRingHom)
    graphFixedOppositeBorel_le (fun a => graphFixedParabolic_le t K σ.toRingHom {a})
    graphFixedOppositeMinimalParabolic_le
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
    orbitXSubgroup_le orbitYSubgroup_le hcov hcov' hPinj
    (graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ)
    (graphFixedRootGroup_inf_normalizer_graphFixedNegUnipotent hσ)
    (fun a => SetLike.coe_injective ((hPV a).trans (coe_orbitYSubgroup a).symm))
    (fun a => SetLike.coe_injective ((hQU a).trans (coe_orbitXSubgroup a).symm))
    (fun a b hab x hx y hy => by
      rw [← SetLike.mem_coe, coe_orbitXSubgroup] at hx
      rw [← SetLike.mem_coe, coe_orbitYSubgroup] at hy
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact commute_orbitX_orbitY_of_ne hab c d)
    (fun a => ⟨_, orbitX_mem_orbitXSubgroup a 1, _, orbitY_mem_orbitYSubgroup a 1,
      not_commute_orbitX_orbitY a⟩) hβ.1 hβ.2
  exact ⟨π, hπ, fun π' hπ' => perm_eq_of_map_eq orbitXSubgroup_injective orbitXSubgroup_le
    (fun a => (hπ' a).1) (fun a => (hπ a).1)⟩

theorem diagram_fixed_intrinsic_simple_pairs
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) :
    (∀ β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom,
      ∃! π : Equiv.Perm (Fin t.foldedTag.rank), PermutesSimpleOrbitGroups t K σ.toRingHom β π) ∧
    (∃ φ : graphFixedUnipotentStabilizer t K σ.toRingHom →* Equiv.Perm (Fin t.foldedTag.rank),
      ∀ β : graphFixedUnipotentStabilizer t K σ.toRingHom,
        PermutesSimpleOrbitGroups t K σ.toRingHom β (φ β)) ∧
    (∀ β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom, ∀ π,
      PermutesSimpleOrbitGroups t K σ.toRingHom β π →
        ∀ a, Nat.card (orbitField t K σ.toRingHom a) =
          Nat.card (orbitField t K σ.toRingHom (π a))) ∧
    (t = .D4 → ∀ p f : ℕ, p.Prime → 1 ≤ f → Nat.card K = (p ^ f) ^ 3 →
      (∀ c, σ c = c ^ (p ^ f)) → ∀ β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom, ∀ π,
        PermutesSimpleOrbitGroups t K σ.toRingHom β π → π = 1) := by
  have huniq := fun (β : MulAut (graphFixedRootGroup t K σ.toRingHom)) hβ =>
    existsUnique_permutesSimpleOrbitGroups (t := t) σ (β := β) hβ
  have hcard : ∀ (β : MulAut (graphFixedRootGroup t K σ.toRingHom)) π,
      PermutesSimpleOrbitGroups t K σ.toRingHom β π → ∀ a,
        Nat.card (orbitField t K σ.toRingHom a) = Nat.card (orbitField t K σ.toRingHom (π a)) := by
    intro β π hπ a
    have h := congrArg (fun H : Subgroup (graphFixedRootGroup t K σ.toRingHom) => Nat.card H)
      (hπ a).1
    rw [Subgroup.card_map_of_injective β.injective, card_subgroupOf_of_le (orbitXSubgroup_le a),
      card_subgroupOf_of_le (orbitXSubgroup_le (π a)), natCard_orbitXSubgroup,
      natCard_orbitXSubgroup] at h
    exact h
  refine ⟨huniq, ?_, fun β _ π hπ => hcard β π hπ, ?_⟩
  ·
    choose φ hφ using fun β : graphFixedUnipotentStabilizer t K σ.toRingHom =>
      (huniq β β.2).exists
    refine ⟨MonoidHom.mk' φ fun β γ => ?_, hφ⟩
    refine (huniq _ (β * γ).2).unique (hφ (β * γ)) fun a => ?_
    obtain ⟨hγX, hγY⟩ := hφ γ a
    obtain ⟨hβX, hβY⟩ := hφ β (φ γ a)
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_mul, map_mulAut_mul, hγX, hβX]
      rfl
    · rw [Subgroup.coe_mul, map_mulAut_mul, hγY, hβY]
      rfl
  ·
    rintro rfl p f hp hf hK hσq β hβ π hπ
    obtain ⟨σ', hσ', -, hcard', -⟩ := finite_graph_field_parameter_fields TwistTag.D4 hp hf K hK
    have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσq, hσ']
    subst hσσ'
    have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    refine Equiv.ext fun a => ?_
    have h1 := hcard β π hπ a
    rw [hcard', hcard'] at h1
    have h2 := Nat.pow_right_injective hq h1
    have h3 : ∀ a b : Fin TwistTag.D4.foldedTag.rank,
        (TwistTag.D4.orbit a).card = (TwistTag.D4.orbit b).card → a = b := by decide
    exact (h3 _ _ h2).symm

end CFSG.LieType.Chevalley
