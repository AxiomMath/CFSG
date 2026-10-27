module

public import CFSG.LieType.Ree.LocalBlockSylowAction
public import CFSG.LieType.Ree.LargeReeBlockCollection
public import CFSG.LieType.Ree.NormalPositiveGeneration

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Levi

variable {τ : Tag} {K : Type} [Field K]

theorem single_mem_parabolicRoots {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
  ⟨isRoot_single τ i, fun k hk => Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) 1⟩

theorem neg_single_mem_parabolicRoots
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    (-Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
  ⟨IsRoot.neg (isRoot_single τ i), fun k hk => by
    rw [Pi.neg_apply, Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) 1, neg_zero]⟩

theorem weylElt_mem_rootLevi
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    weylElt τ K i 1 ∈ rootLevi τ K J := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, ← pinnedX_single, ← pinnedX_neg_single]
  exact mul_mem (mul_mem (pinnedX_mem_rootSpan (single_mem_parabolicRoots hi) _)
    (pinnedX_mem_rootSpan (neg_single_mem_parabolicRoots hi) _))
    (pinnedX_mem_rootSpan (single_mem_parabolicRoots hi) _)

theorem canonicalRep_mem_rootLevi
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    canonicalRep (coxeterSystem τ) K w ∈ rootLevi τ K J := by
  obtain ⟨ω, hω, rfl, hletters⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.1 w hw
  rw [canonicalRep_wordProd hω]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_rootLevi (hletters i hi)

end Levi

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem exists_mul_of_mem_rootLevi_of_mem_reeFixedBorel
    {j : Fin t.fixedOrbitCount}
    {g : ModGL t.tag K} (hgL : g ∈ rootLevi t.tag K (t.fixedOrbitSet j))
    (hgB : g ∈ t.reeFixedBorel K a) :
    ∃ h ∈ t.reeFixedTorus K a, ∃ x ∈ t.reeFixedOrbitUnipotent K a j, g = h * x := by
  obtain ⟨hgB', hgΓ⟩ := Subgroup.mem_inf.1 hgB
  obtain ⟨h, hh, v, hv, rfl⟩ :=
    (large_Ree_parabolic_degree_intersection t.tag K (t.fixedOrbitSet j)).2.1 g
      (Subgroup.mem_inf.2 ⟨hgL, hgB'⟩)
  have hv' : v ∈ rootSpan t.tag K (t.fixedOrbitRoots j) := hv
  have hvU : v ∈ posUnipotent t.tag K := rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hv'
  have hha := torusGroup_le_adjointGroup t K hh
  have hva := rootSpan_le_adjointGroup _ hv'
  have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (mul_mem hha hva)
  have e : (⟨h * v, mul_mem hha hva⟩ : adjointGroup t.tag K) = ⟨h, hha⟩ * ⟨v, hva⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul] at hF
  have hFh := finiteReeAut_mem_torusGroup (a := a) hh hha
  have hFv := finiteReeAut_mem_of_map_le (a := a) (map_finiteReeAut_rootSpan_le fun α hα =>
    ⟨(mem_fixedOrbitRoots_iff.1 hα).1, dualRoot_mem_fixedOrbitRoots hα⟩) hv' hva
  obtain ⟨h1, h2⟩ := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.1 _ hFh _ hh _
    (rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hFv) _ hvU hF
  exact ⟨h, Subgroup.mem_inf.2 ⟨hh, mem_reeGamma_of_fixed hha h1⟩, v,
    Subgroup.mem_inf.2 ⟨hv', mem_reeGamma_of_fixed hva h2⟩, rfl⟩

theorem reeFixedTorus_le_normalizer_reeFixedOrbitNegUnipotent
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedTorus K a ≤
      Subgroup.normalizer (t.reeFixedOrbitNegUnipotent K a j : Set (ModGL t.tag K)) :=
  fun _ hh => Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨torusGroup_le_normalizer_rootSpan (fun _ hα => isRoot_of_mem_neg_fixedOrbitRoots hα)
      (Subgroup.mem_inf.1 hh).1, Subgroup.le_normalizer (Subgroup.mem_inf.1 hh).2⟩)

theorem reeFixedTorus_le_normalizer_reeLocalBlock
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedTorus K a ≤
      Subgroup.normalizer (t.reeLocalBlock K a j : Set (ModGL t.tag K)) :=
  fun _ hh => Subgroup.inf_normalizer_le_normalizer_sup (t.reeFixedOrbitUnipotent K a j)
    (t.reeFixedOrbitNegUnipotent K a j) (Subgroup.mem_inf.2
    ⟨reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent j hh,
      reeFixedTorus_le_normalizer_reeFixedOrbitNegUnipotent j hh⟩)

theorem reeFixedTorus_le_normalizer_iSup_reeLocalBlock :
    t.reeFixedTorus K a ≤ Subgroup.normalizer
      ((⨆ j, t.reeLocalBlock K a j : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) :=
  fun _ hh => Subgroup.iInf_normalizer_le_normalizer_iSup _
    (Subgroup.mem_iInf.2 fun j => reeFixedTorus_le_normalizer_reeLocalBlock j hh)

theorem le_normalizer_iSup_reeLocalBlock :
    (⨆ j, t.reeLocalBlock K a j : Subgroup (ModGL t.tag K)) ≤ Subgroup.normalizer
      ((⨆ j, t.reeLocalBlock K a j : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) :=
  Subgroup.le_normalizer

theorem canonicalRep_mem_normalizer_iSup_reeLocalBlock
    (j : Fin t.fixedOrbitCount) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ Subgroup.normalizer
      ((⨆ i, t.reeLocalBlock K a i : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  have hb : m⁻¹ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      t.reeFixedBorel K a := QuotientGroup.eq.1 hmn
  have hbL : m⁻¹ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      rootLevi t.tag K (t.fixedOrbitSet j) :=
    mul_mem (inv_mem (reeLocalBlock_le_rootLevi j hm))
      (canonicalRep_mem_rootLevi (fixedOrbitElement_mem_fixedOrbitWeyl j))
  obtain ⟨h, hh, x, hx, hhx⟩ := exists_mul_of_mem_rootLevi_of_mem_reeFixedBorel hbL hb
  have hMD := le_iSup (fun i => t.reeLocalBlock K a i) j
  have e : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) = m * (h * x) := by
    rw [← hhx, mul_inv_cancel_left]
  rw [e]
  exact mul_mem (le_normalizer_iSup_reeLocalBlock (hMD hm))
    (mul_mem (reeFixedTorus_le_normalizer_iSup_reeLocalBlock hh)
      (le_normalizer_iSup_reeLocalBlock (hMD (reeFixedOrbitUnipotent_le_reeLocalBlock j hx))))

theorem reeFixedMonomial_le_normalizer_iSup_reeLocalBlock :
    t.reeFixedMonomial K a ≤ Subgroup.normalizer
      ((⨆ j, t.reeLocalBlock K a j : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
  rw [reeFixedMonomial_eq_sup]
  refine sup_le reeFixedTorus_le_normalizer_iSup_reeLocalBlock ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, rfl⟩
  exact canonicalRep_mem_normalizer_iSup_reeLocalBlock j

theorem map_conj_reeFixedOrbitUnipotent_le_iSup
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (j : Fin t.fixedOrbitCount) :
    (t.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom ≤
      ⨆ i, t.reeLocalBlock K a i := by
  rintro _ ⟨x, hx, rfl⟩
  have hN := reeFixedMonomial_le_normalizer_iSup_reeLocalBlock (K := K) (a := a)
    (canonicalRep_mem_reeFixedMonomial t K a hw)
  exact (Subgroup.mem_normalizer_iff.1 hN x).1
    (le_iSup (fun i => t.reeLocalBlock K a i) j (reeFixedOrbitUnipotent_le_reeLocalBlock j hx))

theorem reeGamma_le_normalizer_iSup_reeLocalBlock
    (hU : t.reeFixedPosUnipotent K a ≤ ⨆ j, t.reeLocalBlock K a j) :
    t.reeGamma K a ≤ Subgroup.normalizer
      ((⨆ j, t.reeLocalBlock K a j : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
  rw [reeGamma_eq_sup_closure]
  refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hb' : b ∈ (t.reeFixedBorel K a : Set (ModGL t.tag K)) := hb
    rw [reeFixedBorel_eq_mul'] at hb'
    obtain ⟨u, hu, h, hh, rfl⟩ := hb'
    exact mul_mem (le_normalizer_iSup_reeLocalBlock (hU hu))
      (reeFixedTorus_le_normalizer_iSup_reeLocalBlock hh)
  · rintro _ ⟨j, rfl⟩
    exact canonicalRep_mem_normalizer_iSup_reeLocalBlock j

theorem reeLocalBlock_le_reeGamma
    (j : Fin t.fixedOrbitCount) :
    t.reeLocalBlock K a j ≤ t.reeGamma K a :=
  sup_le inf_le_right inf_le_right

theorem reeGamma_eq_iSup_reeLocalBlock
    (hK : Nat.card K = t.prime ^ (2 * a + 1))
    (hU : t.reeFixedPosUnipotent K a ≤ ⨆ j, t.reeLocalBlock K a j) :
    t.reeGamma K a = ⨆ j, t.reeLocalBlock K a j := by
  refine le_antisymm ?_ (iSup_le reeLocalBlock_le_reeGamma)
  rw [← ree_normal_positive_generation t a K hK, Subgroup.closure_le]
  rintro _ ⟨g, hg, u, hu, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (reeGamma_le_normalizer_iSup_reeLocalBlock hU hg) u).1
    (hU hu)

@[expose] def largeReePosIndex : Fin 8 → Fin 16 :=
  ![0, 1, 3, 4, 6, 9, 11, 12]

@[expose] def largeReePosOrder (k : Fin 8) : Set (Fin F4.tag.rank → ℤ) :=
  {x | x ∈ largeReeBlockTable (largeReePosIndex k)}

theorem largeReePosIndex_check :
    (∀ k, ∀ x ∈ largeReeBlockTable (largeReePosIndex k), 0 < height x) ∧
      ∀ i : Fin 16, (∀ x ∈ largeReeBlockTable i, 0 < height x) → ∃ k, largeReePosIndex k = i := by
  decide +kernel

theorem largeReePosIndex_injective : Function.Injective largeReePosIndex := by
  decide

theorem largeReePosOrder_injective : Function.Injective largeReePosOrder :=
  largeReeBlockSet_injective.comp largeReePosIndex_injective

theorem range_largeReePosOrder :
    Set.range largeReePosOrder = largeReePosBlocks := by
  ext Q
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨largeReeBlockSet_mem (largeReePosIndex k),
      (largeReeBlockSet_subset_iff _).2 (largeReePosIndex_check.1 k)⟩
  · rintro ⟨hQ, hpos⟩
    rw [largeReeBlocks_eq_range] at hQ
    obtain ⟨i, rfl⟩ := hQ
    obtain ⟨k, rfl⟩ := largeReePosIndex_check.2 i ((largeReeBlockSet_subset_iff i).1 hpos)
    exact ⟨k, rfl⟩

theorem reeFixedPosUnipotent_le_iSup_reeLocalBlock_F4
    [CharP K F4.prime] :
    F4.reeFixedPosUnipotent K a ≤ ⨆ j, F4.reeLocalBlock K a j := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := (bijOn_list_prod_largeReeBlockGroup K a largeReePosOrder
    largeReePosOrder_injective range_largeReePosOrder).2.2 hu
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  have hQ : largeReePosOrder k ∈ largeReeBlocks := by
    have h := Set.mem_range_self (f := largeReePosOrder) k
    rw [range_largeReePosOrder] at h
    exact h.1
  obtain ⟨w, hw, j, hwj⟩ := hQ
  have hxk : x k ∈ largeReeBlockGroup K a (largeReePosOrder k) := hx k (Set.mem_univ k)
  rw [hwj, largeReeBlockGroup_eq_map K a hw j] at hxk
  exact map_conj_reeFixedOrbitUnipotent_le_iSup hw j hxk

theorem large_Ree_simple_pair_generation
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a =
      F4.reeLocalBlock K a ⟨0, by decide⟩ ⊔ F4.reeLocalBlock K a ⟨1, by decide⟩ := by
  rw [reeGamma_eq_iSup_reeLocalBlock (t := F4) hK reeFixedPosUnipotent_le_iSup_reeLocalBlock_F4]
  refine le_antisymm (iSup_le fun j => ?_)
    (sup_le (le_iSup (fun j => F4.reeLocalBlock K a j) ⟨0, by decide⟩)
      (le_iSup (fun j => F4.reeLocalBlock K a j) ⟨1, by decide⟩))
  obtain ⟨j, hj⟩ := j
  change j < 2 at hj
  interval_cases j
  · exact le_sup_left
  · exact le_sup_right

end ReeTag

end CFSG.LieType.Ree
