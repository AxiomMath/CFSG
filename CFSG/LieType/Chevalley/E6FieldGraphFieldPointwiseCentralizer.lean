module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

namespace FieldGraphFieldPointwise

section Regular

variable {τ : Tag} {K : Type} [Field K]

theorem single_pos (i : Fin τ.rank) :
    IsRoot τ (Pi.single i 1) ∧ 0 < height (Pi.single i 1 : Fin τ.rank → ℤ) :=
  ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩

theorem mem_heightSeries_single
    {g : ModGL τ K} (hg : g ∈ posUnipotent τ K) (i : Fin τ.rank) :
    g ∈ heightSeries τ K (height (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rwa [height_single, heightSeries_one]

variable [Finite K]

theorem rootCoord_single_xUnit
    (i j : Fin τ.rank) (c : K) :
    rootCoord (single_pos i) (xUnit τ K j c) = if j = i then c else 0 := by
  rw [← pinnedX_single]
  split_ifs with h
  · subst h
    exact rootCoord_self _ c
  · refine rootCoord_pinnedX_of_ne _ (single_pos j) (by rw [height_single, height_single])
      (fun h' => h ?_) c
    by_contra hji
    have h1 := congrFun h' j
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hji] at h1
    exact one_ne_zero h1

theorem rootCoord_single_xUnit_mul_xUnit
    (i p q : Fin τ.rank) (s t : K) :
    rootCoord (single_pos i) (xUnit τ K p s * xUnit τ K q t) =
      (if p = i then s else 0) + (if q = i then t else 0) := by
  rw [rootCoord_mul _ (mem_heightSeries_single (xUnit_mem_posUnipotent p s) i)
    (mem_heightSeries_single (xUnit_mem_posUnipotent q t) i), rootCoord_single_xUnit,
    rootCoord_single_xUnit]

theorem rootCoord_single_list_prod
    (j : Fin τ.rank) (L : List (Fin τ.rank))
    (c : Fin τ.rank → K) :
    rootCoord (single_pos j) ((L.map fun i => xUnit τ K i (c i)).prod) =
      (L.map fun i => if i = j then c i else 0).sum := by
  have hL : ∀ g ∈ L.map (fun i => xUnit τ K i (c i)),
      g ∈ heightSeries τ K (height (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact mem_heightSeries_single (xUnit_mem_posUnipotent i _) j
  rw [rootCoord_list_prod _ _ hL, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ => rootCoord_single_xUnit j i (c i))

theorem rootCoord_ite_eq_of_adjX_eq
    {i j : Fin τ.rank} {c d : K}
    (h : adjX τ K i c = adjX τ K j d) (k : Fin τ.rank) :
    (if i = k then c else 0) = (if j = k then d else 0) := by
  have h1 : rootCoord (single_pos k) (xUnit τ K i c) = rootCoord (single_pos k) (xUnit τ K j d) :=
    congrArg (fun g : adjointGroup τ K => rootCoord (single_pos k) (g : ModGL τ K)) h
  rwa [rootCoord_single_xUnit, rootCoord_single_xUnit] at h1

theorem mem_borelGroup_of_conj_regular
    {g y : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hy : y ∈ posUnipotent τ K) (hreg : ∀ i, rootCoord (single_pos i) y ≠ 0)
    (hgy : g * y * g⁻¹ ∈ posUnipotent τ K) : g ∈ borelGroup τ K := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := (bijOn_bruhatCell w).surjOn hw
  change b ∈ borelGroup τ K at hb
  change u ∈ rootSpan τ K (inversionSet w) at hu
  change b * canonicalRep (coxeterSystem τ) K w * u = g at hbu
  subst hbu
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have huU : u ∈ posUnipotent τ K :=
    rootSpan_le_posUnipotent (fun α h => inversionSet_pos (w := w) h) hu
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hy' : u * y * u⁻¹ ∈ posUnipotent τ K := mul_mem (mul_mem huU hy) (inv_mem huU)
  have hny : n * (u * y * u⁻¹) * n⁻¹ ∈ posUnipotent τ K := by
    have hm : b⁻¹ * (b * n * u * y * (b * n * u)⁻¹) * b⁻¹⁻¹ ∈ posUnipotent τ K := by
      rw [← map_conj_posUnipotent_of_mem_borelGroup (inv_mem hb)]
      exact ⟨_, hgy, rfl⟩
    have e : n * (u * y * u⁻¹) * n⁻¹ = b⁻¹ * (b * n * u * y * (b * n * u)⁻¹) * b⁻¹⁻¹ := by
      group
    rw [e]
    exact hm
  have hy'' : u * y * u⁻¹ ∈ (rootSpan τ K (nonInversionSet w) : Set (ModGL τ K)) *
      (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) := by
    rw [← posUnipotent_eq_mul_rootSpan w]
    exact hy'
  obtain ⟨j, hj, i', hi', hji⟩ := hy''
  change j * i' = u * y * u⁻¹ at hji
  have hi'U : n * i' * n⁻¹ ∈ posUnipotent τ K := by
    have e : n * i' * n⁻¹ = (n * j * n⁻¹)⁻¹ * (n * (u * y * u⁻¹) * n⁻¹) := by
      rw [← hji]
      group
    rw [e]
    exact mul_mem (inv_mem (canonicalRep_conj_mem_posUnipotent hj)) hny
  have hi'1 : i' = 1 := by
    have h : n * i' * n⁻¹ ∈ posUnipotent τ K ⊓ negUnipotent τ K :=
      Subgroup.mem_inf.2 ⟨hi'U, canonicalRep_conj_mem_negUnipotent hi'⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    calc i' = n⁻¹ * (n * i' * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  rw [hi'1, mul_one] at hji
  have hw1 : w = 1 := by
    by_contra hw1
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
    have hsub : nonInversionSet w ⊆ coordKerRoots (Pi.single i 1) := by
      rintro β ⟨hβ, hpos, hwβ⟩
      refine ⟨hβ, hpos, by rw [height_single]; omega, ?_⟩
      rintro rfl
      omega
    have h0 := rootCoord_of_mem_coordKer (single_pos i) (rootSpan_mono hsub hj)
    rw [hji, rootCoord_conj _ huU (mem_heightSeries_single hy i)] at h0
    exact hreg i h0
  have hn1 : n = 1 := by rw [hn, hw1, canonicalRep_one]
  rw [hn1, mul_one]
  exact mul_mem hb (hUB huU)

theorem exists_exactNormalAut_eq_of_fix_regular
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {w₀ : WeylGroup τ} (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    {n₀ u : adjointGroup τ K} (hn₀ : (n₀ : ModGL τ K) = canonicalRep (coxeterSystem τ) K w₀)
    (hu : (u : ModGL τ K) ∈ posUnipotent τ K)
    (hreg : ∀ i, rootCoord (single_pos i) (u : ModGL τ K) ≠ 0)
    {β : MulAut (adjointGroup τ K)} (hβu : β u = u)
    (hβv : β (n₀ * u * n₀⁻¹) = n₀ * u * n₀⁻¹) :
    ∃ (a : Fin τ.rank → Kˣ) (φ : K ≃+* K) (ε : Fin (exactE τ)),
      β = exactNormalAut τ K a φ ε := by
  obtain ⟨c, a, φ, ε, rfl⟩ := exists_conj_mul_exactNormalAut hτ β
  have hN := exactNormalAut_mem (τ := τ) (K := K) a φ ε
  have hNx : ∀ x : adjointGroup τ K, (MulAut.conj c * exactNormalAut τ K a φ ε) x = x →
      exactNormalAut τ K a φ ε x = c⁻¹ * x * c := by
    intro x hx
    have h : c * exactNormalAut τ K a φ ε x * c⁻¹ = x := hx
    calc exactNormalAut τ K a φ ε x = c⁻¹ * (c * exactNormalAut τ K a φ ε x * c⁻¹) * c := by
          group
      _ = c⁻¹ * x * c := by rw [h]
  have hNu := congrArg Subtype.val (hNx u hβu)
  have hNv := congrArg Subtype.val (hNx _ hβv)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hNu hNv
  have hcB : (c : ModGL τ K)⁻¹ ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular (inv_mem c.2) hu hreg ?_
    rw [inv_inv, ← hNu]
    exact Subgroup.mem_subgroupOf.1 (apply_mem_of_mem_pairAut hN (Subgroup.mem_subgroupOf.2 hu))
  have hU := map_conj_canonicalRep_longest (K := K) hw₀
  have hvV : ((n₀ * u * n₀⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ negUnipotent τ K := by
    rw [← hU]
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn₀]
    rfl
  have hNvV := Subgroup.mem_subgroupOf.1
    (apply_mem_of_mem_pairAut_right hN (Subgroup.mem_subgroupOf.2 hvV))
  rw [hNv, ← hU] at hNvV
  obtain ⟨z, hz, hzv⟩ := hNvV
  have hzv' : (n₀ : ModGL τ K) * z * (n₀ : ModGL τ K)⁻¹ =
      (c : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * u * (n₀ : ModGL τ K)⁻¹) * c :=
    (congrArg (fun x => x * z * x⁻¹) hn₀).trans hzv
  have hgB : (n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀ ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular
      (mul_mem (mul_mem (inv_mem n₀.2) (inv_mem c.2)) n₀.2) hu hreg ?_
    have e : (n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀ * u *
        ((n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀)⁻¹ = z :=
      calc _ = (n₀ : ModGL τ K)⁻¹ *
            ((c : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * u * (n₀ : ModGL τ K)⁻¹) * c) * n₀ := by
            group
        _ = (n₀ : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * z * (n₀ : ModGL τ K)⁻¹) * n₀ := by
            rw [hzv']
        _ = z := by group
    rw [e]
    exact hz
  obtain ⟨-, hBmap, hBH, -⟩ := opposite_Borel_intersection τ K w₀ hw₀
  have hcH : (c : ModGL τ K)⁻¹ ∈ torusGroup τ K := by
    rw [← hBH]
    refine Subgroup.mem_inf.2 ⟨hcB, ?_⟩
    rw [← hBmap]
    refine ⟨_, hgB, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hn₀]
    group
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (inv_mem_iff.1 hcH)
  have hc : MulAut.conj c = exactNormalAut τ K b 1 0 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_exactNormalAut, exactQ_zero, inv_one, mul_one, mul_one, ← hb]
    change (c : ModGL τ K) * g * (c : ModGL τ K)⁻¹ = _
    congr 2
    exact (Units.ext (entrywise_id _)).symm
  exact ⟨b * a, φ, ε, by rw [hc, exactNormalAut_diag_mul]⟩

end Regular

section Actors

variable {τ : Tag} {K : Type} [Field K]

theorem exactNormalAut_one_zero_eq
    (φ : K ≃+* K) :
    exactNormalAut τ K 1 φ 0 = entrywiseAdjointAut τ φ :=
  MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_exactNormalAut, coe_entrywiseAdjointAut, rootDiagUnit_one, exactQ_zero]
    simp only [one_mul, inv_one, mul_one])

theorem entrywiseAdjointAut_adjX
    (φ : K ≃+* K) (i : Fin τ.rank) (c : K) :
    entrywiseAdjointAut τ φ (adjX τ K i c) = adjX τ K i (φ c) :=
  Subtype.ext (units_map_entrywiseHom_xUnit φ.toRingHom i c)

theorem canonicalRep_mem_fixedFieldImage
    (σ : K ≃+* K) (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ fixedFieldImage τ σ := by
  refine (Subgroup.closure_le _).2 ?_ (canonicalRep_mem_closure (coxeterSystem τ) K w)
  rintro _ ⟨i, rfl⟩
  show weylElt τ K i 1 ∈ fixedFieldImage τ σ
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  refine mul_mem (mul_mem (xUnit_mem_fixedFieldImage i ?_) (yUnit_mem_fixedFieldImage i ?_))
    (xUnit_mem_fixedFieldImage i ?_) <;> simp

theorem graphField_eq_exactNormalAut
    (σ : K ≃+* K) :
    diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ =
      exactNormalAut TwistTag.E6.tag K 1 σ 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut, coe_exactNormalAut,
    rootDiagUnit_one]
  change _ = 1 * diagramMap TwistTag.E6 K ^ 1 * _ * (diagramMap TwistTag.E6 K ^ 1)⁻¹ * 1⁻¹
  rw [pow_one, one_mul, inv_one, mul_one]

theorem exactNormalAut_one_mul_graphField
    (a : Fin TwistTag.E6.tag.rank → Kˣ) (φ σ : K ≃+* K) :
    exactNormalAut TwistTag.E6.tag K a φ 1 *
        (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) =
      exactNormalAut TwistTag.E6.tag K a (φ * σ) 0 := by
  rw [graphField_eq_exactNormalAut, exactNormalAut_mul]
  have h := exactNormalAut_mod (τ := TwistTag.E6.tag) (K := K) a (φ * σ) 2
  rw [show 2 % exactE TwistTag.E6.tag = 0 from rfl] at h
  rw [h]
  congr 1
  funext j
  simp

theorem graphField_apply
    (σ : K ≃+* K) {j : adjointGroup TwistTag.E6.tag K}
    (hj : (j : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) j = j := by
  refine Subtype.ext ?_
  rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut, ← twistHom_apply]
  exact (graphFixedRootGroup_le _ _ _ hj).2

end Actors

section E6

variable {K : Type} [Field K]

abbrev orbitIdx : List (Fin TwistTag.E6.tag.rank) :=
  [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩]

theorem orbitIdx_sum (j : Fin TwistTag.E6.tag.rank) (f : Fin TwistTag.E6.tag.rank → K) :
    (orbitIdx.map fun i => if i = j then f i else 0).sum = f j := by
  fin_cases j <;> simp [orbitIdx, Fin.ext_iff]

def regularElt
    (K : Type) [Field K] : adjointGroup TwistTag.E6.tag K :=
  (orbitIdx.map fun i => adjX TwistTag.E6.tag K i 1).prod

theorem coe_regularElt :
    (regularElt K : ModGL TwistTag.E6.tag K) =
      (orbitIdx.map fun i => xUnit TwistTag.E6.tag K i 1).prod := by
  rw [regularElt, Subgroup.val_list_prod, List.map_map]
  rfl

theorem regularElt_mem_posUnipotent :
    (regularElt K : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K := by
  rw [coe_regularElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_posUnipotent i 1

theorem rootCoord_regularElt
    [Finite K] (j : Fin TwistTag.E6.tag.rank) :
    rootCoord (single_pos j) (regularElt K : ModGL TwistTag.E6.tag K) = 1 := by
  rw [coe_regularElt, rootCoord_single_list_prod, orbitIdx_sum]

theorem regularElt_mem_fixedFieldImage
    (σ : K ≃+* K) :
    (regularElt K : ModGL TwistTag.E6.tag K) ∈ fixedFieldImage TwistTag.E6.tag σ := by
  rw [coe_regularElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_fixedFieldImage i (map_one σ)

theorem coe_orbitX_zero
    (σ : K →+* K) (c : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨0, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨5, by decide⟩ (σ c) := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have hp : TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, hm, hp, Equiv.Perm.one_apply, RingHom.coe_one,
    id_eq]

theorem coe_orbitX_one (σ : K →+* K) :
    (orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨2, by decide⟩ 1 * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ 1 := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hp : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, hm, hp, Equiv.Perm.one_apply, OneMemClass.coe_one,
    map_one]

theorem coe_orbitX_of_card_one
    {a : Fin TwistTag.E6.foldedTag.rank}
    {i : Fin TwistTag.E6.tag.rank} (hc : (TwistTag.E6.orbit a).card = 1)
    (hm : TwistTag.E6.orbitMin a = i) (σ : K →+* K) :
    (orbitX TwistTag.E6 K σ a 1 : ModGL TwistTag.E6.tag K) = xUnit TwistTag.E6.tag K i 1 := by
  rw [coe_orbitX, hc, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_zero, hm, Equiv.Perm.one_apply, OneMemClass.coe_one, map_one]

theorem regularElt_mem_graphFixedRootGroup
    (σ : K →+* K) :
    (regularElt K : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have h : (regularElt K : ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ 1 : ModGL TwistTag.E6.tag K) *
        orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 * orbitX TwistTag.E6 K σ ⟨2, by decide⟩ 1 *
          orbitX TwistTag.E6 K σ ⟨3, by decide⟩ 1 := by
    rw [coe_regularElt, coe_orbitX_zero, coe_orbitX_one,
      coe_orbitX_of_card_one (i := ⟨3, by decide⟩) (by decide) (by decide),
      coe_orbitX_of_card_one (i := ⟨1, by decide⟩) (by decide) (by decide)]
    simp only [orbitIdx, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      OneMemClass.coe_one, map_one, mul_assoc]
  rw [h]
  have hm := fun a => graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ a 1)
  exact mul_mem (mul_mem (mul_mem (hm _) (hm _)) (hm _)) (hm _)

theorem eq_one_of_exactNormalAut_zero_fix
    [Finite K] {a : Fin TwistTag.E6.tag.rank → Kˣ}
    {φ : K ≃+* K} (h : exactNormalAut TwistTag.E6.tag K a φ 0 (regularElt K) = regularElt K) :
    a = 1 := by
  have himg : (exactNormalAut TwistTag.E6.tag K a φ 0 (regularElt K) : ModGL TwistTag.E6.tag K) =
      (orbitIdx.map fun i => xUnit TwistTag.E6.tag K i ((a i : K) * φ 1)).prod := by
    rw [regularElt, map_list_prod, List.map_map, Subgroup.val_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply, exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply]
    rfl
  funext j
  have h1 : rootCoord (single_pos j)
      (exactNormalAut TwistTag.E6.tag K a φ 0 (regularElt K) : ModGL TwistTag.E6.tag K) =
        rootCoord (single_pos j) (regularElt K : ModGL TwistTag.E6.tag K) := by
    rw [h]
  rw [himg, rootCoord_regularElt, rootCoord_single_list_prod, orbitIdx_sum, map_one,
    mul_one] at h1
  exact Units.ext h1

theorem mem_zpowers_of_forall_fixedFieldImage
    [Finite K] (σ : K ≃+* K)
    {β : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hβ : ∀ j : adjointGroup TwistTag.E6.tag K,
      (j : ModGL TwistTag.E6.tag K) ∈ fixedFieldImage TwistTag.E6.tag σ → β j = j) :
    β ∈ Subgroup.zpowers (entrywiseAdjointAut TwistTag.E6.tag σ) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  have hn₀ := canonicalRep_mem_fixedFieldImage (K := K) σ w₀
  have hu := regularElt_mem_fixedFieldImage (K := K) σ
  obtain ⟨a, φ, v, rfl⟩ := exists_exactNormalAut_eq_of_fix_regular (τ := TwistTag.E6.tag)
    (Or.inl rfl) hw₀
    (n₀ := ⟨_, canonicalRep_mem_adjointGroup _ K w₀⟩) (u := regularElt K) (β := β) rfl
    regularElt_mem_posUnipotent (fun j => by rw [rootCoord_regularElt]; exact one_ne_zero)
    (hβ _ hu) (hβ _ (mul_mem (mul_mem hn₀ hu) (inv_mem hn₀)))
  have hv : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by
    have h := v.isLt
    change (v : ℕ) < 2 at h
    omega
  rcases hv with hv | hv
  · rw [hv] at hβ ⊢
    obtain rfl := eq_one_of_exactNormalAut_zero_fix (hβ _ hu)
    rw [exactNormalAut_one_zero_eq] at hβ ⊢
    have hφ : φ ∈ Subgroup.zpowers σ := by
      refine CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed fun c hc => ?_
      have h1 := hβ (adjX TwistTag.E6.tag K ⟨0, by decide⟩ c) (xUnit_mem_fixedFieldImage _ hc)
      rw [entrywiseAdjointAut_adjX] at h1
      exact adjX_injective _ h1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    exact Subgroup.mem_zpowers_iff.2
      ⟨n, (map_zpow (entrywiseAdjointAutHom (τ := TwistTag.E6.tag)) σ n).symm⟩
  · exfalso
    rw [hv] at hβ
    have h1 := hβ (adjX TwistTag.E6.tag K ⟨0, by decide⟩ 1)
      (xUnit_mem_fixedFieldImage _ (map_one σ))
    rw [exactNormalAut_adjX, show exactPerm TwistTag.E6.tag 1 ⟨0, by decide⟩ = ⟨5, by decide⟩
      by decide] at h1
    have h2 := rootCoord_ite_eq_of_adjX_eq h1 ⟨0, by decide⟩
    simp at h2

theorem eq_one_of_forall_graphFixedRootGroup
    [Finite K] (σ : K ≃+* K)
    (hσσ : ∀ c, σ (σ c) = c) {a : Fin TwistTag.E6.tag.rank → Kˣ} {φ : K ≃+* K}
    (h : ∀ j : adjointGroup TwistTag.E6.tag K,
      (j : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom →
        exactNormalAut TwistTag.E6.tag K a φ 0 j = j) :
    exactNormalAut TwistTag.E6.tag K a φ 0 = 1 := by
  obtain rfl := eq_one_of_exactNormalAut_zero_fix
    (h _ (regularElt_mem_graphFixedRootGroup σ.toRingHom))
  rw [exactNormalAut_one_zero_eq] at h ⊢
  suffices hφ : φ = 1 by rw [hφ, entrywiseAdjointAut_one]
  refine RingEquiv.ext fun c => ?_
  show φ c = c
  have hc : c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two]
    exact hσσ c
  have h1 := h _ (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ.toRingHom ⟨0, by decide⟩ ⟨c, hc⟩))
  have h2 := congrArg (fun g : adjointGroup TwistTag.E6.tag K =>
    rootCoord (single_pos ⟨0, by decide⟩) (g : ModGL TwistTag.E6.tag K)) h1
  simp only [coe_entrywiseAdjointAut, coe_orbitX_zero, map_mul, units_map_entrywiseHom_xUnit,
    rootCoord_single_xUnit_mul_xUnit] at h2
  simpa using h2

theorem mem_zpowers_of_forall_graphFixedRootGroup
    [Finite K] (σ : K ≃+* K)
    (hσσ : ∀ c, σ (σ c) = c) {β : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hβ : ∀ j : adjointGroup TwistTag.E6.tag K,
      (j : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom → β j = j) :
    β ∈ Subgroup.zpowers
      (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
  rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
  have hn₀ : canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup hw₁
  have hu := regularElt_mem_graphFixedRootGroup (K := K) σ.toRingHom
  obtain ⟨a, φ, v, rfl⟩ := exists_exactNormalAut_eq_of_fix_regular (τ := TwistTag.E6.tag)
    (Or.inl rfl) hw₀
    (n₀ := ⟨_, canonicalRep_mem_adjointGroup _ K w₀⟩) (u := regularElt K) (β := β) rfl
    regularElt_mem_posUnipotent (fun j => by rw [rootCoord_regularElt]; exact one_ne_zero)
    (hβ _ hu) (hβ _ (mul_mem (mul_mem hn₀ hu) (inv_mem hn₀)))
  have hv : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by
    have h := v.isLt
    change (v : ℕ) < 2 at h
    omega
  rcases hv with hv | hv <;> rw [hv] at hβ ⊢
  · rw [eq_one_of_forall_graphFixedRootGroup σ hσσ hβ]
    exact one_mem _
  · have h1 := eq_one_of_forall_graphFixedRootGroup σ hσσ (a := a) (φ := φ * σ) fun j hj => by
      rw [← exactNormalAut_one_mul_graphField, MulAut.mul_apply, graphField_apply σ hj, hβ j hj]
    rw [← exactNormalAut_one_mul_graphField, mul_eq_one_iff_eq_inv] at h1
    rw [h1]
    exact inv_mem (Subgroup.mem_zpowers _)

end E6

theorem centralizer_inf_eq_zpowers_of_fix {G : Type*} [Group G] {C J : Subgroup G}
    {η : MulAut C} (hZ : Subgroup.center C = ⊥)
    (hNη : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {η})
    (hfix : ∀ β : MulAut C, (∀ j : C, (j : G) ∈ J → β j = j) → β ∈ Subgroup.zpowers η) :
    Subgroup.centralizer {η} ⊓ Subgroup.centralizer
        (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
          Set (MulAut C)) = Subgroup.zpowers η := by
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  refine le_antisymm (fun β hβ => hfix β fun j hj => ?_) ?_
  · obtain ⟨-, hβN⟩ := Subgroup.mem_inf.1 hβ
    have hn : MulAut.conj j ∈ (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :=
      ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have h1 : MulAut.conj j * β = β * MulAut.conj j := Subgroup.mem_centralizer_iff.1 hβN _ hn
    have h2 : MulAut.conj (β j) = MulAut.conj j := by
      rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact hinj h2
  · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNη hn) η (Set.mem_singleton η)).symm⟩)

end FieldGraphFieldPointwise

open FieldGraphFieldPointwise


theorem even_E6_canonical_field_graph_field_pointwise_centralizers
    {e : ℕ} (he : 1 ≤ e)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ e)) :
    Subgroup.centralizer
        {diagramConjAut TwistTag.E6 K ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ} ⊓
      Subgroup.centralizer ((((fixedFieldImage TwistTag.E6.tag σ).subgroupOf
        (adjointGroup TwistTag.E6.tag K)).map MulAut.conj :
          Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))) :
            Set (MulAut (adjointGroup TwistTag.E6.tag K))) =
      Subgroup.zpowers
        (diagramConjAut TwistTag.E6 K ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ) ∧
    Subgroup.centralizer
        {diagramConjAut TwistTag.E6 K ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ} ⊓
      Subgroup.centralizer ((((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K)).map MulAut.conj :
          Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))) :
            Set (MulAut (adjointGroup TwistTag.E6.tag K))) =
      Subgroup.zpowers
        (diagramConjAut TwistTag.E6 K ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup TwistTag.E6.tag K) = ⊥ :=
    center_adjointGroup_eq_bot_field _ K
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, ← pow_mul, ← pow_add, ← two_mul, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  obtain ⟨⟨-, -, -, -, -, -, -, hle0, -⟩, ⟨-, -, -, -, -, -, -, hle1, -⟩⟩ :=
    even_E6_canonical_field_graph_field_derived_fixed_subgroups he K hK σ hσ
  refine ⟨centralizer_inf_eq_zpowers_of_fix hZ hle0 fun β hβ => ?_,
    centralizer_inf_eq_zpowers_of_fix hZ hle1 fun β hβ => ?_⟩
  · rw [pow_zero, one_mul]
    exact mem_zpowers_of_forall_fixedFieldImage σ hβ
  · rw [pow_one]
    exact mem_zpowers_of_forall_graphFixedRootGroup σ hσσ hβ

end CFSG.LieType.Chevalley
