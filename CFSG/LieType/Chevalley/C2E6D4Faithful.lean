module

public import CFSG.LieType.Chevalley.C2E6D4Unipotent
public import CFSG.LieType.Chevalley.C2E6A5CubeFaithful
public import CFSG.LieType.Chevalley.C2E6D4Torus

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise

theorem smul_eq_of_mem_parabolicWeylGroup
    {J : Set (Fin Tag.E6.rank)} {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 J) {v : Fin Tag.E6.rank → ℤ}
    (hv : ∀ j ∈ J, ∑ k, Tag.E6.cartan j k * v k = 0) : w • v = v := by
  have hle : parabolicWeylGroup Tag.E6 J ≤ MulAction.stabilizer (WeylGroup Tag.E6) v := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, simple_smul, reflect, hv j hj, zero_smul,
      sub_zero]
  exact hle hw

@[expose] def invD : Fin Tag.E6.rank → ℤ := (![2, 1, 2, 2, 1, 0] : Fin 6 → ℤ)

theorem pairing_invD : ∀ j : Fin Tag.E6.rank, j ≠ i6 0 → j ≠ i6 5 →
    ∑ k, Tag.E6.cartan j k * invD k = 0 := by
  decide

theorem single_eq_rootD_sub : ∀ i : Fin Tag.E6.rank, i ≠ i6 0 → i ≠ i6 5 →
    ∃ a b : Fin 8, (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = rootD a - rootD b := by
  decide

theorem two_single_zero : (Pi.single (i6 0) 1 + Pi.single (i6 0) 1 : Fin Tag.E6.rank → ℤ) =
    invD - (Pi.single (i6 1) 1 + Pi.single (i6 2) 1 + Pi.single (i6 2) 1 + Pi.single (i6 3) 1 +
      Pi.single (i6 3) 1 + Pi.single (i6 4) 1) := by
  decide

theorem single_five : (Pi.single (i6 5) 1 : Fin Tag.E6.rank → ℤ) =
    rootD 0 - Pi.single (i6 0) 1 - Pi.single (i6 2) 1 - Pi.single (i6 3) 1 -
      Pi.single (i6 4) 1 := by
  decide

theorem eq_one_of_smul_rootD
    {w : WeylGroup Tag.E6} (hw : w ∈ parabolicWeylGroup Tag.E6 setD)
    (h : ∀ j, w • rootD j = rootD j) : w = 1 := by
  have hD : ∀ i : Fin Tag.E6.rank, i ≠ i6 0 → i ≠ i6 5 →
      w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single i 1 := by
    intro i h0 h5
    obtain ⟨a, b, hab⟩ := single_eq_rootD_sub i h0 h5
    rw [hab, smul_sub, h, h]
  have h1 := hD (i6 1) (by decide) (by decide)
  have h2 := hD (i6 2) (by decide) (by decide)
  have h3 := hD (i6 3) (by decide) (by decide)
  have h4 := hD (i6 4) (by decide) (by decide)
  have hx : w • invD = invD := smul_eq_of_mem_parabolicWeylGroup hw fun j hj =>
    pairing_invD j (fun h => (not_mem_setD_iff j).mpr (Or.inl h) hj)
      (fun h => (not_mem_setD_iff j).mpr (Or.inr h) hj)
  have h0 : w • (Pi.single (i6 0) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (i6 0) 1 := by
    have e : w • ((Pi.single (i6 0) 1 : Fin Tag.E6.rank → ℤ) + Pi.single (i6 0) 1) =
        Pi.single (i6 0) 1 + Pi.single (i6 0) 1 := by
      rw [two_single_zero, smul_sub, hx]
      simp only [smul_add, h1, h2, h3, h4]
    rw [smul_add] at e
    funext l
    have := congrFun e l
    simp only [Pi.add_apply] at this
    omega
  have h5 : w • (Pi.single (i6 5) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (i6 5) 1 := by
    rw [single_five, smul_sub, smul_sub, smul_sub, smul_sub, h, h0, h2, h3, h4]
  refine ext_single fun i => ?_
  rw [one_smul]
  by_cases hi0 : i = i6 0
  · rw [hi0]
    exact h0
  by_cases hi5 : i = i6 5
  · rw [hi5]
    exact h5
  exact hD i hi0 hi5

abbrev labD
    (j : Fin 8) : Label Tag.E6 := Sum.inr ⟨rootD j, isRoot_rootD j⟩

theorem exists_rootD_smul
    {w : WeylGroup Tag.E6} (hw : w ∈ parabolicWeylGroup Tag.E6 setD)
    (j : Fin 8) : ∃ j', rootD j' = w • rootD j := by
  refine exists_rootD_eq (IsRoot.smul (isRoot_rootD j) w) ?_ ?_
  · show (w • rootD j) (i6 0) = 1
    rw [smul_apply_of_mem_parabolicWeylGroup hw _ ((not_mem_setD_iff (i6 0)).mpr (Or.inl rfl))]
    exact (rootD_zero_five j).1
  · show (w • rootD j) (i6 5) = 1
    rw [smul_apply_of_mem_parabolicWeylGroup hw _ ((not_mem_setD_iff (i6 5)).mpr (Or.inr rfl))]
    exact (rootD_zero_five j).2

theorem smul_rootD_eq_of_not_precedes
    {w : WeylGroup Tag.E6}
    (hw : w ∈ parabolicWeylGroup Tag.E6 setD)
    (hprec : ∀ j j', rootD j' = w • rootD j → ¬(labD j).Precedes (labD j')) (j : Fin 8) :
    w • rootD j = rootD j := by
  by_contra hj
  classical
  set M : Finset (Fin 8) := Finset.univ.filter fun k => w • rootD k ≠ rootD k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image (fun k => (labD k).position) hM
  have hk : w • rootD k ≠ rootD k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := exists_rootD_smul hw k
  have hne : labD k' ≠ labD k := by
    intro h
    have : rootD k' = rootD k := congrArg (fun l : Label Tag.E6 => match l with
      | .inl _ => rootD k | .inr β => β.1) h
    exact hk (hk' ▸ this)
  have hprec' : (labD k').Precedes (labD k) :=
    (Label.precedes_or_precedes hne).resolve_right (hprec k k' hk')
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hk ?_⟩
    rw [hk'] at h
    exact smul_left_cancel w h
  exact absurd (hmin k' hk'M) (not_le.mpr (Label.position_lt_position hprec'))

theorem borel_apply_vecD_eq_zero
    {c : ModGL Tag.E6 K} (hc : c ∈ borelGroup Tag.E6 K)
    {j j' : Fin 8} (h : (labD j).Precedes (labD j')) :
    (c : Module.End K (RootModule Tag.E6 K)) (vecD j) (labD j') = 0 := by
  have := (triangular_borel_structure.{0, 0} Tag.E6 K).2.2.2.2.2.2.2.2.2.1 c hc (labD j') (labD j) h
  rwa [vecD, rootVec_eq_single (isRoot_rootD j)]

theorem eq_one_of_torusElt_mem_unipotent
    {a : Fin 4 → Kˣ} (h : torusElt 4 K a ∈ unipotent 4 K) :
    a = 1 := by
  rw [unipotent_eq_posUnip] at h
  have h1 := (mem_posUnip.mp h).2
  funext i
  apply Units.ext
  have := h1 i
  rw [toMatrix'_torusElt, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq] at this
  exact this

theorem psiD_injective :
    Function.Injective psiD := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix := (psiD_eq_one_iff g).mp hg
  have hgS : (g : ModGL Tag.E6 K) ∈ (subsystemGroup Tag.E6 K setD : Set (ModGL Tag.E6 K)) := g.2
  rw [(subsystem_root_group_bruhat Tag.E6 K setD).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E6 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E6 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E6 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ groupD := parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K)
    (A := setD) (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E6) K w : Module.End K (RootModule Tag.E6 K))
      (vecD j) = ((b⁻¹ * v⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (vecD j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E6) K w = b⁻¹ * (g : ModGL Tag.E6 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_moduleD_of_mem_groupD (inv_mem hvS) _ (vecD_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', rootD j' = w • rootD j → ¬(labD j).Precedes (labD j') := by
    intro j j' hj' hp
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec w (isRoot_rootD j)
    have h0 := borel_apply_vecD_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hp
    rw [← hn j, hne, ← hj', rootVec_eq_single (isRoot_rootD j'), Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_rootD hw (smul_rootD_eq_of_not_precedes hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E6 K (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (torusD : Set (ModGL Tag.E6 K)) * (unipotentD : Set (ModGL Tag.E6 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E6) (K := K) (A := setD)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  set t' : groupD := ⟨t, torusD_le_groupD ht⟩
  set u' : groupD := ⟨u, unipotentD_le_groupD hu⟩
  have hgtu : g = t' * u' := Subtype.ext hgbv.symm
  have hψ : psiD t' * psiD u' = 1 := by rw [← map_mul, ← hgtu, hg]
  obtain ⟨a, ha⟩ : psiD t' ∈ (torusElt 4 K).range := by
    rw [← map_psiD_torusD]
    exact Subgroup.mem_map_of_mem _ ht
  have hu0 : psiD u' ∈ unipotent 4 K := by
    rw [← map_psiD_unipotentD]
    exact Subgroup.mem_map_of_mem _ hu
  have hua : psiD u' = torusElt 4 K a⁻¹ := by
    rw [map_inv, ha]
    exact eq_inv_of_mul_eq_one_right hψ
  have ha1 : a⁻¹ = 1 := eq_one_of_torusElt_mem_unipotent (hua ▸ hu0)
  have hu1 : psiD u' = 1 := by rw [hua, ha1, map_one]
  have hu'1 : u' = 1 := psiD_injOn_unipotentD (show u' ∈ unipotentD.subgroupOf groupD from hu)
    (one_mem _) (hu1.trans (map_one psiD).symm)
  have ht1 : psiD t' = 1 := by rw [hu1, mul_one] at hψ; exact hψ
  have ht'1 : t' = 1 := eq_one_of_mem_torusD (show t' ∈ torusD.subgroupOf groupD from ht) ht1
  rw [hgtu, hu'1, ht'1, mul_one]

end CFSG.LieType.Chevalley.C2E6Std
