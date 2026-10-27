module

public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.LieType.Chevalley.GraphFixedIntrinsicPairs
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.LieType.Chevalley.OppositeNoncommutativity
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section Restrict

variable {G : Type*} [Group G]

@[expose] def mulAutRestrict (H : Subgroup G) (α : MulAut G) (h : H.map α.toMonoidHom = H) :
    MulAut H :=
  (α.subgroupMap H).trans (MulEquiv.subgroupCongr h)

theorem coe_mulAutRestrict (H : Subgroup G) (α : MulAut G) (h : H.map α.toMonoidHom = H)
    (x : H) : (mulAutRestrict H α h x : G) = α x :=
  rfl

theorem map_subgroupOf_mulAutRestrict {H L : Subgroup G} {α : MulAut G}
    (h : L.map α.toMonoidHom = L) (hH : H.map α.toMonoidHom = H) :
    (H.subgroupOf L).map (mulAutRestrict L α h).toMonoidHom = H.subgroupOf L := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [← hH]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [← hH] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyL : y ∈ L := by
      have : α y ∈ L := hyx ▸ x.2
      rw [← h] at this
      obtain ⟨z, hz, hzy⟩ := this
      rwa [← α.injective hzy]
    exact ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext hyx⟩

end Restrict

variable {τ : Tag} {K : Type} [Field K]

theorem commute_xUnit_yUnit_of_ne'
    {i j : Fin τ.rank} (hij : i ≠ j) (c d : K) :
    Commute (xUnit τ K i c) (yUnit τ K j d) := by
  have hne : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single j 1 := fun h => by
    have := congrFun h i
    simp [hij] at this
  have hne' : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -(-Pi.single j 1) := fun h => by
    have := congrFun h i
    simp [hij] at this
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ (isRoot_single τ i)
    (isRoot_neg_single τ j) hne hne'
  have hnil : commPairs τ (Pi.single i 1) (-Pi.single j 1) = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨h1, h2, hroot⟩ := (hmem p).1 hp
    rcases hroot.nonneg_or_nonpos with h | h
    · have := h j
      simp [Ne.symm hij] at this
      omega
    · have := h i
      simp [hij] at this
      omega
  have hF' := hF K c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg,
    ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm, pinnedX_single,
    pinnedX_neg_single] at hF'
  exact hF'

theorem not_commute_xUnit_yUnit
    (i : Fin τ.rank) :
    ¬ Commute (xUnit τ K i 1) (yUnit τ K i 1) := by
  intro h
  obtain ⟨h1, h2, -⟩ := opposite_simple_root_noncommutativity τ K
  apply h2 i 1 1 one_ne_zero one_ne_zero
  rw [← h1]
  have h' := congrArg Units.val h.eq
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit] at h'
  rw [h', sub_self, LinearMap.zero_apply]

theorem negUnipotent_le_adjointGroup
    : negUnipotent τ K ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem oppositeBorel_le_adjointGroup
    : oppositeBorel τ K ≤ adjointGroup τ K :=
  sup_le (le_sup_left.trans borelGroup_le_adjointGroup') negUnipotent_le_adjointGroup

theorem oppositeMinimalParabolic_le_adjointGroup
    (i : Fin τ.rank) :
    oppositeMinimalParabolic τ K i ≤ adjointGroup τ K :=
  sup_le oppositeBorel_le_adjointGroup ((Subgroup.closure_le _).2 (Set.range_subset_iff.2
    fun c => xUnit_mem_adjointGroup i c))

theorem subgroupOf_rootSubgroup_single
    (i : Fin τ.rank) :
    (rootSubgroup τ K (Pi.single i 1)).subgroupOf (adjointGroup τ K) =
      simplePosSubgroup τ K i := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← SetLike.mem_coe, coe_rootSubgroup_single, mem_simplePosSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem subgroupOf_rootSubgroup_neg_single
    (i : Fin τ.rank) :
    (rootSubgroup τ K (-Pi.single i 1)).subgroupOf (adjointGroup τ K) =
      simpleNegSubgroup τ K i := by
  ext g
  rw [Subgroup.mem_subgroupOf, ← SetLike.mem_coe, coe_rootSubgroup_neg_single,
    mem_simpleNegSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

variable (τ K) in
theorem oppositeBorel_normalizer :
    adjointGroup τ K ⊓ Subgroup.normalizer (negUnipotent τ K : Set (ModGL τ K)) =
      oppositeBorel τ K := by
  obtain ⟨w₀, hmax, -, himage, -⟩ := weyl_longest_element τ
  obtain ⟨hS, -, -⟩ := canonical_weyl_root_transport τ K
  set n₀ := canonicalRep (coxeterSystem τ) K w₀
  have hn₀ : n₀ ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w₀
  have hU : (posUnipotent τ K).map (MulAut.conj n₀).toMonoidHom = negUnipotent τ K := by
    rw [posUnipotent, hS w₀ _ fun α hα => hα.1, himage]
    rfl
  have hB : (borelGroup τ K).map (MulAut.conj n₀).toMonoidHom = oppositeBorel τ K :=
    (opposite_Borel_intersection τ K w₀ hmax).2.1
  have hC : (adjointGroup τ K).map (MulAut.conj n₀).toMonoidHom = adjointGroup τ K := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hx
      have := mul_mem (mul_mem hn₀ hx) (inv_mem hn₀)
      simpa [mul_assoc] using this
    · intro hx
      exact mul_mem (mul_mem (inv_mem hn₀) hx) hn₀
  rw [← hU, ← hB, ← (borel_self_normalizers τ K).1, Subgroup.map_inf_eq _ _ _
    (MulAut.conj n₀).injective, hC, ← Subgroup.map_equiv_normalizer_eq]

variable (τ K) in
@[expose] def unipotentPairAut
    : Subgroup (MulAut (adjointGroup τ K)) :=
  pairAutSubgroup ((posUnipotent τ K).subgroupOf (adjointGroup τ K))
    ((negUnipotent τ K).subgroupOf (adjointGroup τ K))

theorem simplePosSubgroup_injective
    : Function.Injective (simplePosSubgroup τ K) := by
  intro i j h
  by_contra hij
  apply not_commute_xUnit_yUnit (τ := τ) (K := K) i
  have hx : (adjX τ K i 1 : adjointGroup τ K) ∈ simplePosSubgroup τ K j := h ▸ ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := hx
  have hc' : xUnit τ K i 1 = xUnit τ K j c := hc
  rw [hc']
  exact commute_xUnit_yUnit_of_ne' (Ne.symm hij) c 1

theorem exists_perm_map_simple
    {α : MulAut (adjointGroup τ K)} (hα : α ∈ unipotentPairAut τ K) :
    ∃ π : Equiv.Perm (Fin τ.rank), ∀ i,
      (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i) ∧
      (simpleNegSubgroup τ K i).map α.toMonoidHom = simpleNegSubgroup τ K (π i) := by
  obtain ⟨hcov, hPinj, hPV, hcov', -, hQU⟩ := exceptional_ordinary_minimal_Borel_intersections τ K
  obtain ⟨π, hπ⟩ := exists_perm_map_eq (G := ModGL τ K) (C := adjointGroup τ K)
    (U := posUnipotent τ K) (V := negUnipotent τ K) (B := borelGroup τ K)
    (B' := oppositeBorel τ K) (P := fun i => parabolicSubgroup τ K {i})
    (Q := oppositeMinimalParabolic τ K) (X := fun i => rootSubgroup τ K (Pi.single i 1))
    (Y := fun i => rootSubgroup τ K (-Pi.single i 1)) borelGroup_le_adjointGroup'
    oppositeBorel_le_adjointGroup (fun i => parabolicSubgroup_le_adjointGroup τ K {i})
    oppositeMinimalParabolic_le_adjointGroup posUnipotent_le_adjointGroup
    negUnipotent_le_adjointGroup (fun i => rootSubgroup_le_adjointGroup _)
    (fun i => rootSubgroup_le_adjointGroup _) hcov hcov' hPinj (borel_self_normalizers τ K).1
    (oppositeBorel_normalizer τ K)
    (fun i => SetLike.coe_injective ((hPV i).trans (coe_rootSubgroup_neg_single i).symm))
    (fun i => SetLike.coe_injective ((hQU i).trans (coe_rootSubgroup_single i).symm))
    (fun a b hab x hx y hy => by
      rw [← SetLike.mem_coe, coe_rootSubgroup_single] at hx
      rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single] at hy
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact commute_xUnit_yUnit_of_ne' hab c d)
    (fun a => ⟨_, mem_rootSubgroup.2 ⟨1, by rw [pinnedX_single]⟩, _,
      mem_rootSubgroup.2 ⟨1, by rw [pinnedX_neg_single]⟩, not_commute_xUnit_yUnit a⟩) hα.1 hα.2
  refine ⟨π, fun i => ?_⟩
  have := hπ i
  simp only [subgroupOf_rootSubgroup_single, subgroupOf_rootSubgroup_neg_single] at this
  exact this

theorem perm_map_simple_unique
    {α : MulAut (adjointGroup τ K)} {π π' : Equiv.Perm (Fin τ.rank)}
    (h : ∀ i, (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i))
    (h' : ∀ i, (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π' i)) :
    π = π' :=
  Equiv.ext fun i => simplePosSubgroup_injective ((h i).symm.trans (h' i))

theorem exists_unique_perm_map_simple
    {α : MulAut (adjointGroup τ K)}
    (hα : α ∈ unipotentPairAut τ K) :
    ∃! π : Equiv.Perm (Fin τ.rank), ∀ i,
      (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i) ∧
      (simpleNegSubgroup τ K i).map α.toMonoidHom = simpleNegSubgroup τ K (π i) :=
  let ⟨π, hπ⟩ := exists_perm_map_simple hα
  ⟨π, hπ, fun _ hπ' => perm_map_simple_unique (fun i => (hπ' i).1) (fun i => (hπ i).1)⟩

variable (τ K) in
@[expose] noncomputable def simplePerm
    (α : unipotentPairAut τ K) : Equiv.Perm (Fin τ.rank) :=
  (exists_perm_map_simple α.2).choose

theorem simplePerm_spec
    (α : unipotentPairAut τ K) (i : Fin τ.rank) :
    (simplePosSubgroup τ K i).map (α : MulAut (adjointGroup τ K)).toMonoidHom =
        simplePosSubgroup τ K (simplePerm τ K α i) ∧
      (simpleNegSubgroup τ K i).map (α : MulAut (adjointGroup τ K)).toMonoidHom =
        simpleNegSubgroup τ K (simplePerm τ K α i) :=
  (exists_perm_map_simple α.2).choose_spec i

variable (τ K) in
@[expose] noncomputable def simplePermHom
    : unipotentPairAut τ K →* Equiv.Perm (Fin τ.rank) :=
  MonoidHom.mk' (simplePerm τ K) fun α β =>
    perm_map_simple_unique (fun i => (simplePerm_spec (α * β) i).1) fun i => by
      rw [Subgroup.coe_mul, show ((α : MulAut (adjointGroup τ K)) * β).toMonoidHom =
          (α : MulAut (adjointGroup τ K)).toMonoidHom.comp
            (β : MulAut (adjointGroup τ K)).toMonoidHom from rfl, ← Subgroup.map_map,
        (simplePerm_spec β i).1, (simplePerm_spec α _).1]
      rfl

theorem simplePermHom_apply
    (α : unipotentPairAut τ K) :
    simplePermHom τ K α = simplePerm τ K α :=
  rfl

theorem range_rankOneRep
    (i : Fin τ.rank) :
    (rankOneRep τ K i).range = rankOneSubgroup (τ := τ) (K := K) i := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨c, rfl⟩ := hg
      rw [SetLike.mem_coe, rankOneRep_upper]
      exact Subgroup.mem_sup_left ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := hg
      rw [SetLike.mem_coe, rankOneRep_lower]
      exact Subgroup.mem_sup_right ⟨c, rfl⟩
  · refine sup_le (fun g hg => ?_) fun g hg => ?_
    · obtain ⟨c, hc⟩ := hg
      exact ⟨sl2Upper K c, by rw [rankOneRep_upper]; exact Subtype.ext hc.symm⟩
    · obtain ⟨c, hc⟩ := hg
      exact ⟨sl2Lower K c, by rw [rankOneRep_lower]; exact Subtype.ext hc.symm⟩

variable (τ K) in
@[expose] def rankOneRepL
    (i : Fin τ.rank) : SL(2, K) →* rankOneSubgroup (τ := τ) (K := K) i :=
  (rankOneRep τ K i).codRestrict (rankOneSubgroup (τ := τ) (K := K) i) fun g => by
    rw [← range_rankOneRep]
    exact ⟨g, rfl⟩

theorem rankOneRepL_surjective
    (i : Fin τ.rank) : Function.Surjective (rankOneRepL τ K i) := by
  rintro ⟨x, hx⟩
  rw [← range_rankOneRep] at hx
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

theorem sl2RootX_rankOneRepL
    (i : Fin τ.rank) :
    sl2RootX (rankOneRepL τ K i) =
      (simplePosSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i) := by
  ext x
  rw [mem_sl2RootX, Subgroup.mem_subgroupOf, mem_simplePosSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by
      change ((rankOneRep τ K i (sl2Upper K c) : adjointGroup τ K) : ModGL τ K) = _
      rw [rankOneRep_upper]
      rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
    change ((rankOneRep τ K i (sl2Upper K c) : adjointGroup τ K) : ModGL τ K) = _
    rw [rankOneRep_upper, hc]
    rfl

theorem sl2RootY_rankOneRepL
    (i : Fin τ.rank) :
    sl2RootY (rankOneRepL τ K i) =
      (simpleNegSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i) := by
  ext x
  rw [mem_sl2RootY, Subgroup.mem_subgroupOf, mem_simpleNegSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by
      change ((rankOneRep τ K i (sl2Lower K c) : adjointGroup τ K) : ModGL τ K) = _
      rw [rankOneRep_lower]
      rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
    change ((rankOneRep τ K i (sl2Lower K c) : adjointGroup τ K) : ModGL τ K) = _
    rw [rankOneRep_lower, hc]
    rfl

theorem derivedSeries_two_rankOnePairAut
    [Finite K] (i : Fin τ.rank) :
    derivedSeries (pairAutSubgroup
      ((simplePosSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))
      ((simpleNegSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))) 2 = ⊥ := by
  have h := exceptional_central_SL2_pair_stabilizer (rankOneRepL τ K i) (rankOneRepL_surjective i)
    fun g hg => rankOneRep_ker i g (congrArg Subtype.val hg)
  rwa [sl2RootX_rankOneRepL, sl2RootY_rankOneRepL] at h

theorem derivedSeries_pi_eq_bot {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] (n : ℕ)
    (h : ∀ i, derivedSeries (G i) n = ⊥) : derivedSeries ((i : ι) → G i) n = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  have := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) n
    (Subgroup.mem_map_of_mem _ hg)
  rw [h i, Subgroup.mem_bot] at this
  exact this

theorem exceptional_ordinary_intrinsic_simple_pairs
    (τ : Tag) (K : Type) [Field K] [Finite K] :
    (∀ α ∈ unipotentPairAut τ K, ∃! π : Equiv.Perm (Fin τ.rank), ∀ i,
      (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i) ∧
      (simpleNegSubgroup τ K i).map α.toMonoidHom = simpleNegSubgroup τ K (π i)) ∧
    ∃ φ : unipotentPairAut τ K →* Equiv.Perm (Fin τ.rank),
      (∀ (α : unipotentPairAut τ K) (i : Fin τ.rank),
        (simplePosSubgroup τ K i).map (α : MulAut (adjointGroup τ K)).toMonoidHom =
          simplePosSubgroup τ K (φ α i) ∧
        (simpleNegSubgroup τ K i).map (α : MulAut (adjointGroup τ K)).toMonoidHom =
          simpleNegSubgroup τ K (φ α i)) ∧
      ∃ ψ : φ.ker →* ((i : Fin τ.rank) →
          pairAutSubgroup
            ((simplePosSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))
            ((simpleNegSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))),
        Function.Injective ψ ∧
        (∀ (α : φ.ker) (i : Fin τ.rank) (x : rankOneSubgroup (τ := τ) (K := K) i),
          (((ψ α i : MulAut (rankOneSubgroup (τ := τ) (K := K) i)) x :
            rankOneSubgroup (τ := τ) (K := K) i) :
            adjointGroup τ K) =
            ((α : unipotentPairAut τ K) : MulAut (adjointGroup τ K)) x) ∧
        derivedSeries φ.ker 2 = ⊥ := by
  refine ⟨fun α hα => exists_unique_perm_map_simple hα, simplePermHom τ K,
    fun α i => simplePerm_spec α i, ?_⟩
  have hX : ∀ (α : (simplePermHom τ K).ker) (i : Fin τ.rank),
      (simplePosSubgroup τ K i).map ((α : unipotentPairAut τ K) :
        MulAut (adjointGroup τ K)).toMonoidHom = simplePosSubgroup τ K i := fun α i => by
    have h := (simplePerm_spec (α : unipotentPairAut τ K) i).1
    rwa [← simplePermHom_apply, α.2, Equiv.Perm.one_apply] at h
  have hY : ∀ (α : (simplePermHom τ K).ker) (i : Fin τ.rank),
      (simpleNegSubgroup τ K i).map ((α : unipotentPairAut τ K) :
        MulAut (adjointGroup τ K)).toMonoidHom = simpleNegSubgroup τ K i := fun α i => by
    have h := (simplePerm_spec (α : unipotentPairAut τ K) i).2
    rwa [← simplePermHom_apply, α.2, Equiv.Perm.one_apply] at h
  have hL : ∀ (α : (simplePermHom τ K).ker) (i : Fin τ.rank),
      (rankOneSubgroup (τ := τ) (K := K) i).map ((α : unipotentPairAut τ K) :
        MulAut (adjointGroup τ K)).toMonoidHom = rankOneSubgroup (τ := τ) (K := K) i :=
      fun α i => by
    rw [rankOneSubgroup, Subgroup.map_sup, hX, hY]
  let ψ : (simplePermHom τ K).ker →* ((i : Fin τ.rank) →
      pairAutSubgroup ((simplePosSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))
        ((simpleNegSubgroup τ K i).subgroupOf (rankOneSubgroup (τ := τ) (K := K) i))) :=
    { toFun := fun α i => ⟨mulAutRestrict (rankOneSubgroup (τ := τ) (K := K) i) _ (hL α i),
        map_subgroupOf_mulAutRestrict (hL α i) (hX α i),
        map_subgroupOf_mulAutRestrict (hL α i) (hY α i)⟩
      map_one' := funext fun i => Subtype.ext (MulEquiv.ext fun x => Subtype.ext rfl)
      map_mul' := fun α β => funext fun i => Subtype.ext (MulEquiv.ext fun x => Subtype.ext rfl) }
  have hψ : ∀ (α : (simplePermHom τ K).ker) (i : Fin τ.rank)
      (x : rankOneSubgroup (τ := τ) (K := K) i),
      (((ψ α i : MulAut (rankOneSubgroup (τ := τ) (K := K) i)) x :
        rankOneSubgroup (τ := τ) (K := K) i) :
        adjointGroup τ K) = ((α : unipotentPairAut τ K) : MulAut (adjointGroup τ K)) x :=
    fun _ _ _ => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have hfix : ∀ (i : Fin τ.rank) (x : adjointGroup τ K), x ∈ rankOneSubgroup (τ := τ) (K := K) i →
        ((α : unipotentPairAut τ K) : MulAut (adjointGroup τ K)) x = x := fun i x hx => by
      have h := congrArg (fun f => (((f i : MulAut (rankOneSubgroup (τ := τ) (K := K) i)) ⟨x, hx⟩ :
        rankOneSubgroup (τ := τ) (K := K) i) : adjointGroup τ K)) hα
      exact h
    refine Subtype.ext (Subtype.ext (mulAut_eq_one_of_fix (fun i c => hfix i _
      (Subgroup.mem_sup_left ⟨c, rfl⟩)) fun i c => hfix i _ (Subgroup.mem_sup_right ⟨c, rfl⟩)))
  refine ⟨ψ, hinj, hψ, ?_⟩
  have h := map_derivedSeries_le_derivedSeries ψ 2
  rwa [derivedSeries_pi_eq_bot 2 fun i => derivedSeries_two_rankOnePairAut i, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hinj] at h

end CFSG.LieType.Chevalley
