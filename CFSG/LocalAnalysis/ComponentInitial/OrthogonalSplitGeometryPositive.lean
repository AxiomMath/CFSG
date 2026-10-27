module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeylLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFlagTransitivity

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise commutatorElement

variable {r : ℕ} {K : Type*} [Field K]

section Height

variable (r) in
@[expose] def simpleHeight : (Fin r → ℤ) →+ ℤ where
  toFun x := ∑ j, ((r : ℤ) - 1 - j) * x j
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

theorem simpleHeight_eps (a : Fin r) : simpleHeight r (eps r a) = r - 1 - a := by
  change ∑ j, ((r : ℤ) - 1 - j) * eps r a j = _
  rw [Finset.sum_eq_single a (fun j _ hj => by rw [eps_eval_ne hj, mul_zero]) (by simp),
    eps_eval_self, mul_one]

theorem simpleHeight_simpleRoot (hr : 2 ≤ r) (i : Fin r) : simpleHeight r (simpleRoot r i) = 1 := by
  by_cases h : i.val + 1 < r
  · rw [simpleRoot_of_lt h, map_add, map_zsmul, map_zsmul, simpleHeight_eps, simpleHeight_eps]
    simp only [one_smul, neg_one_smul]
    push_cast
    ring
  · have hi : i.val = r - 1 := by have := i.isLt; omega
    rw [simpleRoot_of_not_lt h, map_add, map_zsmul, map_zsmul, simpleHeight_eps, simpleHeight_eps,
      one_smul, one_smul, hi]
    simp only
    push_cast [Nat.cast_sub (show 2 ≤ r from hr), Nat.cast_sub (show 1 ≤ r by omega)]
    ring

theorem one_le_simpleHeight {β : Fin r → ℤ} (hβ : β ∈ posRoots r) : 1 ≤ simpleHeight r β := by
  obtain ⟨i, j, hij, rfl | rfl⟩ := hβ
  · rw [map_sub, simpleHeight_eps, simpleHeight_eps]
    have : (i : ℤ) < j := by exact_mod_cast hij
    linarith
  · rw [map_add, simpleHeight_eps, simpleHeight_eps]
    have h1 : (i : ℤ) < j := by exact_mod_cast hij
    have h2 : (j : ℤ) < r := by exact_mod_cast j.isLt
    linarith

theorem add_ne_simpleRoot (hr : 2 ≤ r) {β γ : Fin r → ℤ} (hβ : β ∈ posRoots r)
    (hγ : γ ∈ posRoots r) (i : Fin r) : β + γ ≠ simpleRoot r i := by
  intro h
  have h1 := congrArg (simpleHeight r) h
  rw [map_add, simpleHeight_simpleRoot hr] at h1
  have := one_le_simpleHeight hβ
  have := one_le_simpleHeight hγ
  omega

theorem add_mem_posRoots {β γ : Fin r → ℤ} (hβ : β ∈ posRoots r) (hγ : γ ∈ posRoots r)
    (h : β + γ ∈ roots r) : β + γ ∈ posRoots r := by
  rw [mem_posRoots_iff_rootHeight_pos h, map_add]
  have := rootHeight_pos_of_mem_posRoots hβ
  have := rootHeight_pos_of_mem_posRoots hγ
  omega

theorem ne_neg_of_mem_posRoots {β γ : Fin r → ℤ} (hβ : β ∈ posRoots r) (hγ : γ ∈ posRoots r) :
    γ ≠ -β := by
  rintro rfl
  exact (mem_posRoots_or_neg_mem_posRoots (posRoots_subset_roots hβ)).2 ⟨hβ, hγ⟩

end Height

section Unipotent

theorem unipotent_eq_posUnip : unipotent r K = posUnip r K := by
  refine le_antisymm (iSup₂_le fun α hα => ?_) ?_
  · rintro _ ⟨t, rfl⟩
    rw [posUnip_eq_closure]
    obtain ⟨i, j, hij, rfl | rfl⟩ := hα
    · rw [rootElt_eps_sub_eps' hij]
      exact Subgroup.subset_closure (Or.inl ⟨i, j, t, hij, rfl⟩)
    · rw [rootElt_eps_add_eps' hij]
      exact Subgroup.subset_closure (Or.inr ⟨i, j, t, hij, rfl⟩)
  · rw [posUnip_eq_closure, Subgroup.closure_le]
    rintro _ (⟨i, j, t, hij, rfl⟩ | ⟨i, j, t, hij, rfl⟩)
    · rw [← rootElt_eps_sub_eps' hij]
      exact rootSubgroup_le_unipotent ⟨i, j, hij, Or.inl rfl⟩ (rootElt_mem_rootSubgroup _ t)
    · rw [← rootElt_eps_add_eps' hij]
      exact rootSubgroup_le_unipotent ⟨i, j, hij, Or.inr rfl⟩ (rootElt_mem_rootSubgroup _ t)

theorem unipotent_le_borel : unipotent r K ≤ borel r K := by
  intro g hg
  rw [unipotent_eq_posUnip] at hg
  refine mem_borel.2 ⟨posUnip_le_orthElementaryGroup hg, fun i _ _ => ?_⟩
  exact (mem_posBorel.1 (posUnip_le_posBorel hg)).2 i

theorem torus_le_borel : torus r K ≤ borel r K := by
  rintro _ ⟨hg, d, rfl⟩
  exact mem_borel.2 ⟨hg, fun i _ _ => (mem_posBorel.1 (torusElt_mem_posBorel d)).2 i⟩

theorem flag_eq_top_of_le {i : ℕ} (hi : r ≤ i) : flag r K i = flag r K r := by
  rw [flag_eq_coordSpan, flag_eq_coordSpan]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨j, _, hj⟩ => ⟨j, j.2, hj⟩, fun ⟨j, _, hj⟩ => ⟨j, by omega, hj⟩⟩

theorem borel_le_posBorel : borel r K ≤ posBorel r K := by
  intro g hg
  obtain ⟨hgE, hF⟩ := mem_borel.1 hg
  have hgO := orthElementaryGroup_le (quadPlus r K) hgE
  have hle : ∀ i ≤ r, (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] _) = flag r K i := by
    intro i hir
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [flag_zero, Submodule.map_bot]
    · exact hF i hi0 hir
  have hall : ∀ i : ℕ, (flag r K i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] _) = flag r K i := by
    intro i
    by_cases hir : i ≤ r
    · exact hle i hir
    · rw [flag_eq_top_of_le (by omega)]
      exact hle r le_rfl
  exact mem_posBorel.2 ⟨⟨hgO, (Submodule.mem_stabilizer_submodule_iff_map_eq).2 (hall r)⟩, hall⟩

theorem exists_torus_mul_unipotent {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ borel r K) : ∃ t ∈ torus r K, ∃ u ∈ unipotent r K, g = t * u := by
  have hgB := borel_le_posBorel hg
  set d := posBorelDiag r K ⟨g, hgB⟩ with hd
  have htB := torusElt_mem_posBorel (r := r) (K := K) d
  have hdiag : posBorelDiag r K ⟨torusElt r K d, htB⟩ = d := funext fun i => Units.ext (by
    rw [coe_posBorelDiag, toMatrix'_torusElt, fromBlocks_apply₁₁, diagonal_apply_eq])
  have hu : (torusElt r K d)⁻¹ * g ∈ posUnip r K := by
    have hker : (⟨torusElt r K d, htB⟩ : posBorel r K)⁻¹ * ⟨g, hgB⟩ ∈ (posBorelDiag r K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdiag, ← hd, inv_mul_cancel]
    rw [posBorelDiag_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  rw [← unipotent_eq_posUnip] at hu
  refine ⟨torusElt r K d, Subgroup.mem_inf.2 ⟨?_, d, rfl⟩, _, hu, by group⟩
  have hgE := (mem_borel.1 hg).1
  have huE : (torusElt r K d)⁻¹ * g ∈ orthElementaryGroup (quadPlus r K) := unipotent_le hu
  have : torusElt r K d = g * ((torusElt r K d)⁻¹ * g)⁻¹ := by group
  rw [this]
  exact mul_mem hgE (inv_mem huE)

theorem borel_eq_torus_mul_unipotent :
    (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (torus r K : Set _) * (unipotent r K : Set _) ∧
      (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (unipotent r K : Set _) * (torus r K : Set _) := by
  refine ⟨Set.Subset.antisymm (fun g hg => ?_) ?_, Set.Subset.antisymm (fun g hg => ?_) ?_⟩
  · obtain ⟨t, ht, u, hu, rfl⟩ := exists_torus_mul_unipotent hg
    exact Set.mul_mem_mul ht hu
  · rintro _ ⟨t, ht, u, hu, rfl⟩
    exact mul_mem (torus_le_borel ht) (unipotent_le_borel hu)
  · obtain ⟨t, ht, u, hu, he⟩ := exists_torus_mul_unipotent (inv_mem hg)
    refine ⟨u⁻¹, inv_mem hu, t⁻¹, inv_mem ht, ?_⟩
    change u⁻¹ * t⁻¹ = g
    rw [← _root_.mul_inv_rev, ← he, inv_inv]
  · rintro _ ⟨u, hu, t, ht, rfl⟩
    exact mul_mem (unipotent_le_borel hu) (torus_le_borel ht)

end Unipotent

section Except

variable (r K) in
@[expose] noncomputable def unipotentExcept (i : Fin r) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  ⨆ β ∈ posRoots r \ {simpleRoot r i}, rootSubgroup r K β

theorem rootSubgroup_le_unipotentExcept {i : Fin r} {β : Fin r → ℤ}
    (hβ : β ∈ posRoots r \ {simpleRoot r i}) : rootSubgroup r K β ≤ unipotentExcept r K i :=
  le_iSup₂ (f := fun β (_ : β ∈ posRoots r \ {simpleRoot r i}) => rootSubgroup r K β) β hβ

theorem unipotentExcept_le_unipotent (i : Fin r) : unipotentExcept r K i ≤ unipotent r K :=
  iSup₂_le fun _ hβ => rootSubgroup_le_unipotent hβ.1

theorem map_conj_unipotentExcept_le (hr : 2 ≤ r) (i : Fin r) {γ : Fin r → ℤ}
    (hγ : γ ∈ posRoots r) (t : K) :
    (unipotentExcept r K i).map (MulAut.conj (rootElt r K γ t)).toMonoidHom ≤
      unipotentExcept r K i := by
  rw [unipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  obtain ⟨-, hcomm, hcomm'⟩ := orthogonal_geometry_split_root_commutators (K := K) (r := r)
  have hyU : rootElt r K β u ∈ unipotentExcept r K i :=
    rootSubgroup_le_unipotentExcept hβ (rootElt_mem_rootSubgroup _ _)
  have hconj : (MulAut.conj (rootElt r K γ t)).toMonoidHom (rootElt r K β u) =
      ⁅rootElt r K γ t, rootElt r K β u⁆ * rootElt r K β u := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
    group
  rw [hconj]
  refine mul_mem ?_ hyU
  by_cases hsum : γ + β ∈ roots r
  · obtain ⟨c, -, hc⟩ := hcomm' γ (posRoots_subset_roots hγ) β (posRoots_subset_roots hβ.1) hsum
    rw [hc]
    refine rootSubgroup_le_unipotentExcept ⟨add_mem_posRoots hγ hβ.1 hsum, ?_⟩
      (rootElt_mem_rootSubgroup _ _)
    exact add_ne_simpleRoot hr hγ hβ.1 i
  · have := hcomm γ (posRoots_subset_roots hγ) β (posRoots_subset_roots hβ.1)
      (ne_neg_of_mem_posRoots hβ.1 hγ) hsum t u
    rw [commutatorElement_eq_one_iff_commute.2 this]
    exact one_mem _

theorem unipotentExcept_normal (hr : 2 ≤ r) (i : Fin r) :
    ((unipotentExcept r K i).subgroupOf (unipotent r K)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (unipotentExcept_le_unipotent i)]
  have hle : unipotent r K ≤ Subgroup.normalizer (unipotentExcept r K i : Set _) := by
    refine iSup₂_le fun γ hγ => ?_
    rintro _ ⟨t, rfl⟩
    have h1 : ∀ s : K, ∀ h ∈ unipotentExcept r K i,
        rootElt r K γ s * h * (rootElt r K γ s)⁻¹ ∈ unipotentExcept r K i := fun s h hh =>
      map_conj_unipotentExcept_le hr i hγ s ⟨h, hh, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨h1 t h, fun hh => ?_⟩
    have := h1 (-t) _ hh
    rw [← rootElt_inv, inv_inv] at this
    convert this using 1
    group
  exact fun h k hh hk => (Subgroup.mem_normalizer_iff.1 (hle hk) h).1 hh

theorem unipotentExcept_sup (hr : 2 ≤ r) (i : Fin r) :
    unipotentExcept r K i ⊔ rootSubgroup r K (simpleRoot r i) = unipotent r K := by
  refine le_antisymm (sup_le (unipotentExcept_le_unipotent i)
    (rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr i))) (iSup₂_le fun β hβ => ?_)
  by_cases h : β = simpleRoot r i
  · rw [h]
    exact le_sup_right
  · exact le_trans (rootSubgroup_le_unipotentExcept ⟨hβ, h⟩) le_sup_left

theorem coe_eq_mul_of_normal {G : Type*} [Group G] {L N H : Subgroup G} (hN : N ≤ L)
    (hH : H ≤ L) (hNn : (N.subgroupOf L).Normal) (hL : N ⊔ H = L) :
    (L : Set G) = (N : Set G) * (H : Set G) ∧ (L : Set G) = (H : Set G) * (N : Set G) := by
  have htop : N.subgroupOf L ⊔ H.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN hH, hL, Subgroup.subgroupOf_self]
  have htop' : H.subgroupOf L ⊔ N.subgroupOf L = ⊤ := by rw [sup_comm, htop]
  have h1 := Subgroup.normal_mul (N.subgroupOf L) (H.subgroupOf L)
  have h2 := Subgroup.mul_normal (H.subgroupOf L) (N.subgroupOf L)
  rw [htop, Subgroup.coe_top] at h1
  rw [htop', Subgroup.coe_top] at h2
  refine ⟨Set.Subset.antisymm (fun g hg => ?_) ?_, Set.Subset.antisymm (fun g hg => ?_) ?_⟩
  · have hmem : (⟨g, hg⟩ : L) ∈ (Set.univ : Set L) := Set.mem_univ _
    rw [h1] at hmem
    obtain ⟨n, hn, h, hh, he⟩ := hmem
    exact ⟨n, hn, h, hh, congrArg Subtype.val he⟩
  · rintro _ ⟨n, hn, h, hh, rfl⟩
    exact mul_mem (hN hn) (hH hh)
  · have hmem : (⟨g, hg⟩ : L) ∈ (Set.univ : Set L) := Set.mem_univ _
    rw [h2] at hmem
    obtain ⟨h, hh, n, hn, he⟩ := hmem
    exact ⟨h, hh, n, hn, congrArg Subtype.val he⟩
  · rintro _ ⟨h, hh, n, hn, rfl⟩
    exact mul_mem (hH hh) (hN hn)

theorem map_conj_weylElt_unipotentExcept_le (hr : 2 ≤ r) (i : Fin r) :
    (unipotentExcept r K i).map (MulAut.conj (weylElt r K i)).toMonoidHom ≤ unipotent r K := by
  rw [unipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  have h := map_conj_rootSubgroup_torusWeyl hr ⟨weylElt r K i, weylElt_mem_torusWeyl i⟩
    (posRoots_subset_roots hβ.1)
  rw [torusWeylNu_weylElt hr i] at h
  change (rootSubgroup r K β).map (MulAut.conj (weylElt r K i)).toMonoidHom = _ at h
  rw [h]
  exact rootSubgroup_le_unipotent (simpleRefl_mem_posRoots hr hβ.1 hβ.2)

end Except


theorem orthogonal_geometry_split_positive_root_factorization {K : Type*} [Field K] {r : ℕ}
    (hr : 3 ≤ r) :
    (∀ g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K), g ∈ unipotent r K ↔
      ∃ (A : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
        (A : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
        (∀ i, (A : Matrix (Fin r) (Fin r) K) i i = 1) ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
        LinearMap.toMatrix' (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
          fromBlocks (A : Matrix (Fin r) (Fin r) K) ((A : Matrix (Fin r) (Fin r) K) * C) 0
            ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) ∧
    (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (torus r K : Set _) * (unipotent r K : Set _) ∧
    (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (unipotent r K : Set _) * (torus r K : Set _) ∧
    ∀ i : Fin r, unipotentExcept r K i ≤ unipotent r K ∧
      ((unipotentExcept r K i).subgroupOf (unipotent r K)).Normal ∧
      (unipotent r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (unipotentExcept r K i : Set _) * (rootSubgroup r K (simpleRoot r i) : Set _) ∧
      (unipotent r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) =
        (rootSubgroup r K (simpleRoot r i) : Set _) * (unipotentExcept r K i : Set _) ∧
      (unipotentExcept r K i).map (MulAut.conj (weylElt r K i)).toMonoidHom ≤ unipotent r K := by
  have hr2 : 2 ≤ r := by omega
  refine ⟨fun g => by rw [unipotent_eq_posUnip, mem_posUnip_iff],
    borel_eq_torus_mul_unipotent.1, borel_eq_torus_mul_unipotent.2, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := coe_eq_mul_of_normal (unipotentExcept_le_unipotent (K := K) i)
    (rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr2 i)) (unipotentExcept_normal hr2 i)
    (unipotentExcept_sup hr2 i)
  exact ⟨unipotentExcept_le_unipotent i, unipotentExcept_normal hr2 i, h1, h2,
    map_conj_weylElt_unipotentExcept_le hr2 i⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
