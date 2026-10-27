module

public import CFSG.HardMathSupport.C14IdxCorootLattice
public import CFSG.HardMathSupport.C14IdxCorootConj
public import CFSG.LieType.Chevalley.LeviConjugate
public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcCoroot
public import TauCeti.Algebra.Group.AddSubgroup.RationalSpan

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple coordTuple_eq_prod)
open CFSG.LieType.Chevalley.RootSpace

private lemma toRat_mem_span_of_ofLattice_mem_span_real {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {γ : Fin τ.rank → ℤ} (h : ofLattice γ ∈ Submodule.span ℝ (ofLattice '' Ψ)) :
    (fun i => (γ i : ℚ)) ∈ Submodule.span ℚ ((fun β (i : Fin τ.rank) => (β i : ℚ)) '' Ψ) := by
  classical
  let B : LinearMap.BilinForm ℚ (Fin τ.rank → ℚ) :=
    Matrix.toBilin' (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℚ)
  have hBapp : ∀ x y : Fin τ.rank → ℚ, B x y = ∑ i, x i * y i := by
    intro x y
    rw [show B = Matrix.toBilin' (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℚ) from rfl,
      Matrix.toBilin'_apply]
    simp [Matrix.one_apply, mul_comm]
  have hBsymm : B.IsSymm := by
    rw [show B = Matrix.toBilin' (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℚ) from rfl]
    exact Matrix.isSymm_toBilin'_iff_isSymm.2 Matrix.isSymm_one
  have hBnd : B.Nondegenerate := by
    rw [show B = Matrix.toBilin' (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℚ) from rfl]
    exact LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℚ) (by simp)
  have hmem : (fun i => (γ i : ℚ)) ∈
      B.orthogonal (B.orthogonal (Submodule.span ℚ
        ((fun β (i : Fin τ.rank) => (β i : ℚ)) '' Ψ))) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro lam hlam
    have hβ0 : ∀ β ∈ Ψ, (∑ i, lam i * (β i : ℚ)) = 0 := by
      intro β hβ
      have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hlam)
        (fun i => (β i : ℚ)) (Submodule.subset_span ⟨β, hβ, rfl⟩)
      rw [hBapp] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hreal0 : (∑ i, (lam i : ℝ) * (γ i : ℝ)) = 0 := by
      let f : RootSpace τ →ₗ[ℝ] ℝ :=
        { toFun := fun x => ∑ i, (lam i : ℝ) * x.toPi i
          map_add' := by
            intro x y
            simp [toPi_add, mul_add, Finset.sum_add_distrib]
          map_smul' := by
            intro c x
            simp [toPi_smul, Finset.mul_sum, mul_left_comm] }
      have hf : ∀ β ∈ Ψ, f (ofLattice β) = 0 := by
        intro β hβ
        have h0 := hβ0 β hβ
        have h0' : ((∑ i, lam i * (β i : ℚ) : ℚ) : ℝ) = 0 := by rw [h0]; simp
        simpa [f, toPi_ofPi, ofLattice, mul_comm] using h0'
      have hspan : f (ofLattice γ) = 0 := by
        refine Submodule.span_induction (p := fun x _ => f x = 0) ?_ ?_ ?_ ?_ h
        · rintro _ ⟨β, hβ, rfl⟩
          exact hf β hβ
        · simp [f]
        · intro x y _ _ hx hy
          rw [map_add, hx, hy, add_zero]
        · intro c x _ hx
          rw [map_smul, hx, smul_zero]
      simpa [f, toPi_ofPi, ofLattice, mul_comm] using hspan
    have hcast : ((∑ i, lam i * (γ i : ℚ) : ℚ) : ℝ) = 0 := by
      push_cast
      simpa [mul_comm] using hreal0
    have hQ : (∑ i, lam i * (γ i : ℚ)) = 0 := by
      apply Rat.cast_injective (α := ℝ)
      simpa using hcast
    rw [hBapp]
    simpa [mul_comm] using hQ
  have := (LinearMap.BilinForm.orthogonal_orthogonal hBnd (LinearMap.BilinForm.IsSymm.isRefl hBsymm)
    (Submodule.span ℚ ((fun β (i : Fin τ.rank) => (β i : ℚ)) '' Ψ))).le hmem
  exact this

private lemma exists_nsmul_corootVec_eq_sum
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (Δ : Finset (Fin τ.rank → ℤ)) (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ J)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγV : ofLattice γ ∈ Submodule.span ℝ (ofLattice '' (unionRoots χ J))) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : (Fin τ.rank → ℤ) → ℤ,
      (m : ℤ) • corootVec γ = ∑ β ∈ Δ, n β • corootVec β := by
  classical
  set Ψ := unionRoots χ J with hΨ
  have hrat : (fun i => (γ i : ℚ)) ∈ Submodule.span ℚ
      ((fun β (i : Fin τ.rank) => (β i : ℚ)) '' Ψ) :=
    toRat_mem_span_of_ofLattice_mem_span_real hγV
  have hratP : (fun i => (γ i : ℚ)) ∈ Submodule.span ℚ
      ((fun p : Fin τ.rank → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' (AddSubgroup.closure Ψ)) := by
    refine Submodule.span_mono ?_ hrat
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, AddSubgroup.subset_closure hβ, rfl⟩
  obtain ⟨N, hN, p, hp, hpx⟩ :=
    TauCeti.AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span
      (P := AddSubgroup.closure Ψ) hratP
  have hpγ : p = (N : ℤ) • γ := by
    ext i
    exact_mod_cast hpx i
  have hp' : p ∈ Submodule.span ℤ (id '' Ψ) := by
    rw [Set.image_id, ← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hp
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun (R := ℤ)
    (v := id) (x := p) (s := Ψ)).1 hp'
  have hphi_sum : (CFSG.HardMathSupport.C14Coroot.phi τ) p =
      ∑ i : t, c i • (CFSG.HardMathSupport.C14Coroot.phi τ) (i : Fin τ.rank → ℤ) := by
    rw [← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have h1 : (CFSG.HardMathSupport.C14Coroot.phi τ) p =
      ∑ i : t, (c i * iform (i : Fin τ.rank → ℤ) (i : Fin τ.rank → ℤ)) •
        corootVec (i : Fin τ.rank → ℤ) := by
    rw [hphi_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : IsRoot τ (i : Fin τ.rank → ℤ) := isRoot_of_mem_unionRoots (hΨ ▸ ht i.2)
    rw [CFSG.HardMathSupport.C14Coroot.phi_root hi, smul_smul]
  have hphiN : (CFSG.HardMathSupport.C14Coroot.phi τ) p =
      ((N : ℤ) * iform γ γ) • corootVec γ := by
    rw [hpγ, map_zsmul, CFSG.HardMathSupport.C14Coroot.phi_root hγ, smul_smul]
  set q : Fin τ.rank → ℤ :=
    ∑ i : t, (c i * iform (i : Fin τ.rank → ℤ) (i : Fin τ.rank → ℤ)) •
      corootVec (i : Fin τ.rank → ℤ) with hqdef
  have hq : q = ((N : ℤ) * iform γ γ) • corootVec γ := h1.symm.trans hphiN
  have hqmem : q ∈ AddSubgroup.closure (corootVec '' Ψ) := by
    rw [hqdef]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ ?_ _
    exact AddSubgroup.subset_closure
      (Set.mem_image_of_mem corootVec (ht i.2))
  rw [hΨ] at hqmem
  rw [closure_corootVec_unionRoots_eq, ← hΔ] at hqmem
  have hqspan : q ∈ (Submodule.span ℤ (corootVec '' (Δ : Set (Fin τ.rank → ℤ)))).toAddSubgroup := by
    rwa [Submodule.span_int_eq_addSubgroupClosure]
  obtain ⟨n, hn⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℤ)
    (v := corootVec) (s := Δ)).1 hqspan
  have hpos : 0 < iform γ γ := iform_self_pos_of_isRoot hγ
  refine ⟨N * (iform γ γ).natAbs, Nat.mul_pos hN (Int.natAbs_pos.mpr hpos.ne'), n, ?_⟩
  calc ((N * (iform γ γ).natAbs : ℕ) : ℤ) • corootVec γ
      = ((N : ℤ) * iform γ γ) • corootVec γ := by
        congr 1
        rw [Nat.cast_mul, Int.natAbs_of_nonneg hpos.le]
    _ = q := hq.symm
    _ = ∑ β ∈ Δ, n β • corootVec β := hn.symm

private lemma corootPair_single_single
    {τ : Tag} (j l : Fin τ.rank) :
    corootPair (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single l 1) = τ.cartan j l := by
  have h := corootPair_smul_single (τ := τ) (1 : WeylGroup τ) j (Pi.single l 1)
  simpa [Pi.single_apply] using h

private lemma exists_coordTuple_of_mem_supportedTorus
    {τ : Tag} {L : Type} [Field L]
    {J : Set (Fin τ.rank)} [Fintype J] {g : ModGL τ L}
    (hg : g ∈ supportedTorus τ L J) :
    ∃ Δ' : Finset (Fin τ.rank → ℤ), (∀ β ∈ Δ', IsRoot τ β) ∧
      (∀ β ∈ Δ', β ∈ parabolicRoots τ J) ∧
      ∃ a' : (Fin τ.rank → ℤ) → Lˣ, g = rootDiagUnit τ (coordTuple Δ' a') := by
  classical
  obtain ⟨a, rfl⟩ := hg
  let e : J → (Fin τ.rank → ℤ) := fun j k => if k = (j : Fin τ.rank) then 1 else 0
  have hee : ∀ j : J, e j = Pi.single (j : Fin τ.rank) (1 : ℤ) := by
    intro j
    funext k
    simp [e, Pi.single_apply]
  have he : Function.Injective e := by
    intro i j hij
    by_contra hne
    have h1 := congrFun hij (i : Fin τ.rank)
    have hi : e i (i : Fin τ.rank) = (1 : ℤ) := by simp [e]
    have hj : e j (i : Fin τ.rank) = (0 : ℤ) := by
      simp only [e]
      rw [if_neg]
      exact fun h => hne (Subtype.ext h)
    rw [hi, hj] at h1
    exact one_ne_zero h1
  let Δ' : Finset (Fin τ.rank → ℤ) := Finset.univ.image e
  let a' : (Fin τ.rank → ℤ) → Lˣ :=
    fun γ => if h : γ ∈ Δ' then a (Classical.choose (Finset.mem_image.1 h)) else 1
  have ha'e : ∀ j : J, a' (e j) = a j := by
    intro j
    have hmem : e j ∈ Δ' := Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩
    simp only [a', dif_pos hmem]
    exact congrArg a (he (Classical.choose_spec (Finset.mem_image.1 hmem)).2)
  refine ⟨Δ', fun β hβ => ?_, fun β hβ => ?_, a', ?_⟩
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hβ
    rw [hee j]
    exact isRoot_single τ (j : Fin τ.rank)
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hβ
    rw [hee j]
    exact single_mem_parabolicRoots j.2
  · rw [CFSG.HardMathSupport.Foote.Coordinator.supportedTorusHom_eq' J a]
    congr 1
    funext l
    rw [CFSG.HardMathSupport.Lang.TwE6Step3.rectMono_apply, coordTuple]
    rw [show Δ' = Finset.univ.image e from rfl, Finset.prod_image he.injOn]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ha'e j, hee j]
    congr 1
    exact (corootPair_single_single (j : Fin τ.rank) l).symm

private lemma coordTuple_prod_eq {τ : Tag} {L : Type} [Field L]
    (Δ : Finset (Fin τ.rank → ℤ)) (s : Finset (Fin τ.rank → ℤ))
    (d : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Lˣ) :
    (∏ γ ∈ s, coordTuple Δ (d γ)) = coordTuple Δ (∏ γ ∈ s, d γ) := by
  classical
  induction s using Finset.induction with
  | empty => ext i; simp [coordTuple]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih]
      simp only [← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom_apply]
      rw [map_mul]

private lemma exists_coordTuple_of_prod {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {Δ : Finset (Fin τ.rank → ℤ)} {s : Finset (Fin τ.rank → ℤ)}
    (hdiv : ∀ γ ∈ s, ∃ m : ℕ, 0 < m ∧ ∃ n : (Fin τ.rank → ℤ) → ℤ,
      (m : ℤ) • corootVec γ = ∑ β ∈ Δ, n β • corootVec β)
    (c : (Fin τ.rank → ℤ) → Lˣ) :
    ∃ c' : (Fin τ.rank → ℤ) → Lˣ,
      rootDiagUnit τ (coordTuple s c) = rootDiagUnit τ (coordTuple Δ c') := by
  classical
  have hdiv' : ∀ γ : s, ∃ m : ℕ, 0 < m ∧ ∃ n : (Fin τ.rank → ℤ) → ℤ,
      (m : ℤ) • corootVec (γ : Fin τ.rank → ℤ) = ∑ β ∈ Δ, n β • corootVec β :=
    fun γ => hdiv (γ : Fin τ.rank → ℤ) γ.2
  choose m hmpos n hn using hdiv'
  choose b hb using fun γ : s => IsAlgClosed.exists_pow_nat_eq ((c (γ : Fin τ.rank → ℤ) : L))
    (hmpos γ)
  have hbne : ∀ γ : s, b γ ≠ 0 := by
    intro γ h
    have hc : (c (γ : Fin τ.rank → ℤ) : L) = 0 := by
      rw [← hb γ, h, zero_pow (hmpos γ).ne']
    exact (c (γ : Fin τ.rank → ℤ)).ne_zero hc
  let bu : s → Lˣ := fun γ => Units.mk0 (b γ) (hbne γ)
  have hbu : ∀ γ : s, (bu γ : L) = b γ := fun γ => rfl
  have hbunit : ∀ γ : s, (bu γ) ^ (m γ) = c γ := by
    intro γ
    apply Units.ext
    change ((bu γ : L) ^ (m γ)) = (c γ : L)
    rw [hbu γ]
    exact hb γ
  let d : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Lˣ := fun γ β =>
    if h : γ ∈ s then (bu ⟨γ, h⟩) ^ n ⟨γ, h⟩ β else 1
  have hd : ∀ γ (hγ : γ ∈ s), d γ = fun β => (bu ⟨γ, hγ⟩) ^ n ⟨γ, hγ⟩ β := by
    intro γ hγ
    funext β
    simp only [d, dif_pos hγ]
  have hfac : ∀ γ ∈ s, (fun i => (c γ) ^ corootVec γ i) = coordTuple Δ (d γ) := by
    intro γ hγ
    funext i
    rw [coordTuple]
    calc (c γ) ^ corootVec γ i
        = ((bu ⟨γ, hγ⟩) ^ (m ⟨γ, hγ⟩)) ^ corootVec γ i := by rw [hbunit ⟨γ, hγ⟩]
      _ = (bu ⟨γ, hγ⟩) ^ ((m ⟨γ, hγ⟩ : ℤ) * corootVec γ i) := by
            rw [← zpow_natCast, zpow_mul]
      _ = (bu ⟨γ, hγ⟩) ^ (∑ β ∈ Δ, n ⟨γ, hγ⟩ β * corootVec β i) := by
            have hcoord := congrFun (hn ⟨γ, hγ⟩) i
            simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hcoord
            rw [hcoord]
      _ = ∏ β ∈ Δ, (bu ⟨γ, hγ⟩) ^ (n ⟨γ, hγ⟩ β * corootVec β i) := by
            rw [Finset.prod_zpow_eq_zpow_sum]
      _ = ∏ β ∈ Δ, ((bu ⟨γ, hγ⟩) ^ n ⟨γ, hγ⟩ β) ^ corootVec β i := by
            refine Finset.prod_congr rfl fun β _ => ?_
            rw [zpow_mul]
      _ = ∏ β ∈ Δ, (d γ β) ^ corootPair β (Pi.single i 1) := by
            refine Finset.prod_congr rfl fun β _ => ?_
            rw [hd γ hγ]
            rfl
  refine ⟨∏ γ ∈ s, d γ, ?_⟩
  calc rootDiagUnit τ (coordTuple s c)
      = rootDiagUnit τ (∏ γ ∈ s, (fun i => (c γ) ^ corootVec γ i)) := by
          rw [coordTuple_eq_prod]
          rfl
    _ = rootDiagUnit τ (∏ γ ∈ s, coordTuple Δ (d γ)) := by
          rw [Finset.prod_congr rfl hfac]
    _ = rootDiagUnit τ (coordTuple Δ (∏ γ ∈ s, d γ)) := by
          rw [coordTuple_prod_eq]

theorem exists_coordTuple_of_mem_unionTorus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    (Δ : Finset (Fin τ.rank → ℤ)) (hΔ : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ J)
    {t : ModGL τ L} (ht : t ∈ unionTorus L χ J) :
    ∃ c : (Fin τ.rank → ℤ) → Lˣ, t = rootDiagUnit τ (coordTuple Δ c) := by
  classical
  obtain ⟨htS, htH⟩ := Subgroup.mem_inf.1 ht
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htH
  rw [hl] at htS htH ⊢
  let V : Submodule ℝ (RootSpace τ) :=
    Submodule.span ℝ (ofLattice '' (unionRoots χ J : Set (Fin τ.rank → ℤ)))
  obtain ⟨u, J', hu⟩ := exists_smul_rootsIn_eq_parabolicRoots (τ := τ) V
  let n := canonicalRep (coxeterSystem τ) L u
  let m := canonicalRep (coxeterSystem τ) L u⁻¹
  have hnorm : n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    (canonical_weyl_root_transport τ L).2.2 u
  have hmap := (canonical_weyl_root_transport τ L).1 u (unionRoots χ J)
    (fun α hα => isRoot_of_mem_unionRoots hα)
  have huΨ : ∀ α ∈ unionRoots χ J, u • α ∈ parabolicRoots τ J' := by
    intro α hα
    rw [← hu]
    exact ⟨α, ⟨isRoot_of_mem_unionRoots hα, Submodule.subset_span ⟨α, hα, rfl⟩⟩, rfl⟩
  have hconjS : n * rootDiagUnit τ l * n⁻¹ ∈ rootSpan τ L (parabolicRoots τ J') := by
    have hle : rootSpan τ L ((fun α => u • α) '' unionRoots χ J) ≤
        rootSpan τ L (parabolicRoots τ J') :=
      rootSpan_mono (by rintro _ ⟨α, hα, rfl⟩; exact huΨ α hα)
    refine hle ?_
    rw [← hmap]
    exact ⟨rootDiagUnit τ l, htS, rfl⟩
  have hconjT : n * rootDiagUnit τ l * n⁻¹ ∈ torusGroup τ L :=
    (Subgroup.mem_normalizer_iff.1 hnorm (rootDiagUnit τ l)).1 htH
  have ht' : n * rootDiagUnit τ l * n⁻¹ ∈ supportedTorus τ L J' := by
    rw [← subsystemGroup_inf_torusGroup_eq_supportedTorus]
    exact ⟨by rwa [subsystemGroup_eq_rootSpan], hconjT⟩
  obtain ⟨Δ', hΔ'root, hΔ'par, a', ht'eq⟩ := exists_coordTuple_of_mem_supportedTorus ht'
  let π : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ) :=
    DistribMulAction.toAddEquiv (Fin τ.rank → ℤ) u⁻¹
  have hπ : ∀ x y, iform (π x) (π y) = iform x y := by
    intro x y
    change iform (u⁻¹ • x) (u⁻¹ • y) = iform x y
    rw [iform_smul]
  have hπΦ : ∀ α, IsRoot τ α → IsRoot τ (π α) := by
    intro α hα
    change IsRoot τ (u⁻¹ • α)
    exact CFSG.LieType.Chevalley.IsRoot.smul hα u⁻¹
  have hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
      m * pinnedX τ L α x * m⁻¹ = pinnedX τ L (π α) (ε * x) := by
    intro α hα
    obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (τ := τ) L u⁻¹ hα
    refine ⟨Units.mk0 ε (by intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε), fun x => ?_⟩
    simpa [m, π] using h x
  have hgT : ∀ t : Fin τ.rank → Lˣ,
      ∃ t', m * rootDiagUnit τ t * m⁻¹ = rootDiagUnit τ t' := by
    intro t
    have hmem : m * rootDiagUnit τ t * m⁻¹ ∈ torusGroup τ L :=
      (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ L).2.2 u⁻¹)
        (rootDiagUnit τ t)).1 (rootDiagUnit_mem_torusGroup t)
    exact exists_rootDiagUnit_eq_of_mem_torusGroup hmem
  have hconj := conj_rootDiagUnit_coordTuple (τ := τ) (L := L) (g := m) (π := π)
    hπ hπΦ hgX hgT (Δ := Δ') hΔ'root a'
  obtain ⟨k, hkT, hkn⟩ := canonicalRep_inv_eq (K := L) u
  have hnk : n = m⁻¹ * k⁻¹ := by
    simpa [n, m] using congrArg Inv.inv hkn
  have hd : k⁻¹ * rootDiagUnit τ l * k = rootDiagUnit τ l := by
    obtain ⟨lk, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hkT
    rw [rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    rw [mul_assoc, mul_comm l lk, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmt : m * (n * rootDiagUnit τ l * n⁻¹) * m⁻¹ = rootDiagUnit τ l := by
    rw [hnk]
    calc m * ((m⁻¹ * k⁻¹) * rootDiagUnit τ l * (k * m)) * m⁻¹
        = k⁻¹ * rootDiagUnit τ l * k := by group
      _ = rootDiagUnit τ l := hd
  have ht_eq : rootDiagUnit τ l = rootDiagUnit τ (coordTuple (Δ'.image π)
      fun γ => a' (π.symm γ)) := by
    rw [← hmt, ht'eq]
    exact hconj
  let Δ'' : Finset (Fin τ.rank → ℤ) := Δ'.image π
  let c'' : (Fin τ.rank → ℤ) → Lˣ := fun γ => a' (π.symm γ)
  have ht_eq' : rootDiagUnit τ l = rootDiagUnit τ (coordTuple Δ'' c'') := by
    simpa [Δ'', c''] using ht_eq
  have hdiv : ∀ γ ∈ Δ'', ∃ m : ℕ, 0 < m ∧ ∃ n : (Fin τ.rank → ℤ) → ℤ,
      (m : ℤ) • corootVec γ = ∑ β ∈ Δ, n β • corootVec β := by
    intro γ hγ
    obtain ⟨δ, hδ, hδγ⟩ := Finset.mem_image.1 hγ
    have hγΨ' : γ ∈ {α | IsRoot τ α ∧ ofLattice α ∈ V} := by
      have huγ : u • γ = δ := by
        rw [← hδγ]
        change u • (u⁻¹ • δ) = δ
        rw [← mul_smul, mul_inv_cancel, one_smul]
      have hmem : u • γ ∈ (fun α => u • α) '' {α | IsRoot τ α ∧ ofLattice α ∈ V} := by
        rw [hu, huγ]
        exact hΔ'par δ hδ
      obtain ⟨α, hα, hαeq⟩ := hmem
      have hαγ : α = γ := smul_left_cancel u hαeq
      rwa [hαγ] at hα
    have hγroot : IsRoot τ γ := hγΨ'.1
    have hγV : ofLattice γ ∈ Submodule.span ℝ (ofLattice '' (unionRoots χ J)) := by
      simpa [V] using hγΨ'.2
    exact exists_nsmul_corootVec_eq_sum Δ hΔ hγroot hγV
  obtain ⟨c, hc⟩ := exists_coordTuple_of_prod (Δ := Δ) (s := Δ'') hdiv c''
  exact ⟨c, ht_eq'.trans hc⟩

end CFSG.HardMathSupport.C14Idx
