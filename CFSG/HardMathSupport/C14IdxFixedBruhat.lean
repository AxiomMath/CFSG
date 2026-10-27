module

public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcW1

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Pointwise

private lemma summands_mem_componentRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {α β γ : Fin τ.rank → ℤ} {i : KernelComponent χ}
    (hα : α ∈ componentRoots χ i) (hβ : β ∈ unionRoots χ J)
    (hγ : γ ∈ unionRoots χ J) (h : α = β + γ) :
    β ∈ componentRoots χ i ∧ γ ∈ componentRoots χ i := by
  obtain ⟨j, -, hβj⟩ := mem_unionRoots_iff.1 hβ
  obtain ⟨k, -, hγk⟩ := mem_unionRoots_iff.1 hγ
  have hαr := isRoot_of_mem_componentRoots hα
  have hβr := isRoot_of_mem_componentRoots hβj
  have hγr := isRoot_of_mem_componentRoots hγk
  have hkey : ∀ {x y : Fin τ.rank → ℤ} {p q : KernelComponent χ},
      x ∈ componentRoots χ p → y ∈ componentRoots χ q → p ≠ q → iform x y = 0 :=
    fun hx hy hpq => iform_eq_zero_of_mem_componentRoots hpq hx hy
  rcases eq_or_ne j i with hji | hji
  · subst hji
    have hkj : k = j := by
      by_contra hkj
      have h1 : iform γ β = 0 := hkey hγk hβj hkj
      have h2 : iform γ α = 0 := hkey hγk hα hkj
      have h3 : iform γ (α - β) = 0 := by
        rw [sub_eq_add_neg, iform_add_right, iform_neg_right, h2, h1]
        simp
      have hsub : α - β = γ := by rw [h]; abel
      rw [hsub] at h3
      exact (ne_of_gt (iform_self_pos hγr.ne_zero)) h3
    subst hkj
    exact ⟨hβj, hγk⟩
  · have hki : k = i := by
      by_contra hki
      have h1 : iform α β = 0 := hkey hα hβj (Ne.symm hji)
      have h2 : iform α γ = 0 := hkey hα hγk (Ne.symm hki)
      have h3 : iform α (β + γ) = 0 := by
        rw [iform_add_right, h1, h2]
        simp
      have h3' : iform α α = 0 := by rwa [← h] at h3
      exact (ne_of_gt (iform_self_pos hαr.ne_zero)) h3'
    subst hki
    have hji' : j = k := by
      by_contra hji'
      have h1 : iform β γ = 0 := hkey hβj hγk hji'
      have h2 : iform β α = 0 := hkey hβj hα hji'
      have h3 : iform β (α - γ) = 0 := by
        rw [sub_eq_add_neg, iform_add_right, iform_neg_right, h2, h1]
        simp
      have hsub : α - γ = β := by rw [h]; abel
      rw [hsub] at h3
      exact (ne_of_gt (iform_self_pos hβr.ne_zero)) h3
    subst hji'
    exact ⟨hβj, hγk⟩

theorem mem_simpleRoots_unionRoots_iff
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {β : Fin τ.rank → ℤ} :
    β ∈ simpleRoots (unionRoots χ J) ↔ β ∈ unionSimpleRoots χ J := by
  constructor
  · intro hβ
    obtain ⟨hβr, hβpos, hβs⟩ := mem_simpleRoots.1 hβ
    obtain ⟨i, hi, hβi⟩ := mem_unionRoots_iff.1 hβpos.1
    refine ⟨i, hi, ?_⟩
    rw [mem_simpleRoots]
    exact ⟨hβr, ⟨hβi, hβpos.2⟩, fun γ hγ δ hδ hsum =>
      hβs γ ⟨componentRoots_subset_unionRoots hi hγ.1, hγ.2⟩ δ
        ⟨componentRoots_subset_unionRoots hi hδ.1, hδ.2⟩ hsum⟩
  · rintro ⟨i, hi, hβi⟩
    rw [mem_simpleRoots] at hβi ⊢
    obtain ⟨hβr, hβpos, hβs⟩ := hβi
    refine ⟨hβr, ⟨componentRoots_subset_unionRoots hi hβpos.1, hβpos.2⟩, ?_⟩
    intro γ hγ δ hδ hsum
    obtain ⟨hγi, hδi⟩ := summands_mem_componentRoots hβpos.1 hγ.1 hδ.1 hsum
    exact hβs γ ⟨hγi, hγ.2⟩ δ ⟨hδi, hδ.2⟩ hsum

theorem bijOn_simpleRoots_of_bijOn_posRoots {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hroot : ∀ α ∈ Ψ, IsRoot τ α) (hΨ : Set.BijOn θ Ψ Ψ)
    (hpos : Set.BijOn θ (posRoots Ψ) (posRoots Ψ)) :
    Set.BijOn θ (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) (simpleRoots Ψ : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    change β ∈ simpleRoots Ψ at hβ
    change θ β ∈ simpleRoots Ψ
    rw [mem_simpleRoots] at hβ ⊢
    obtain ⟨-, hβpos, hβs⟩ := hβ
    refine ⟨hroot (θ β) (hΨ.mapsTo hβpos.1), hpos.mapsTo hβpos, ?_⟩
    intro γ hγ δ hδ hsum
    obtain ⟨γ', hγ', hγθ⟩ := hpos.surjOn hγ
    obtain ⟨δ', hδ', hδθ⟩ := hpos.surjOn hδ
    exact hβs γ' hγ' δ' hδ'
      (θ.injective (by rw [map_add, hγθ, hδθ, hsum]))
  · intro α _ β _ h
    exact θ.injective h
  · intro γ hγ
    change γ ∈ simpleRoots Ψ at hγ
    obtain ⟨-, hγpos, hγs⟩ := mem_simpleRoots.1 hγ
    obtain ⟨β, hβpos, hβγ⟩ := hpos.surjOn hγpos
    refine ⟨β, ?_, hβγ⟩
    change β ∈ simpleRoots Ψ
    rw [mem_simpleRoots]
    refine ⟨hroot β hβpos.1, hβpos, ?_⟩
    intro δ hδ ε hε hsum
    exact hγs (θ δ) (hpos.mapsTo hδ) (θ ε) (hpos.mapsTo hε)
      (by rw [← hβγ, ← map_add, hsum])

private lemma canonicalRep_inv_charTwo
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w⁻¹ = (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo,
    inv_mul_cancel, canonicalRep_one]

theorem exists_fixed_bruhat_factor
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)} {e : ℕ}
    {Q : ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQ : (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L)
    (hΨ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    (hΨp : Set.BijOn θ (posRoots (unionRoots χ J)) (posRoots (unionRoots χ J)))
    {s : ModGL τ L} (hs : s ∈ unionRootSpan L χ J) (hσ : frobTwistGL τ L 2 e Q s = s) :
    ∃ w ∈ unionWeylGroup χ J, (∀ α ∈ unionRoots χ J, θ (w • α) = w • θ α) ∧
      ∃ t ∈ unionTorus L χ J, frobTwistGL τ L 2 e Q t = t ∧
      ∃ u ∈ unionUnipotent L χ J, frobTwistGL τ L 2 e Q u = u ∧
      ∃ v ∈ unionUnipotent L χ J, frobTwistGL τ L 2 e Q v = v ∧
      s = t * u * canonicalRep (coxeterSystem τ) L w * v := by
  classical
  let n : (Fin τ.rank → ℤ) → ModGL τ L :=
    fun β => canonicalRep (coxeterSystem τ) L (rootReflection β)
  have hnmem : ∀ β ∈ unionSimpleRoots χ J,
      n β ∈ rootSubgroup τ L β ⊔ rootSubgroup τ L (-β) := by
    intro β hβ
    have hβr := isRoot_of_mem_unionSimpleRoots hβ
    dsimp only [n]
    rw [canonicalRep_rootReflection_eq_charTwo hβr]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩))
      (Subgroup.mem_sup_right (mem_rootSubgroup.2 ⟨1, rfl⟩)))
      (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hn : ∀ β ∈ unionSimpleRoots χ J, n β ∈ rootSubgroup τ L β ⊔
      rootSubgroup τ L (-β) ∧ n β ∈ monomialSubgroup τ L ∧
      MapsRootLines (n β) (rootReflection β) :=
    fun β hβ => ⟨hnmem β hβ, canonicalRep_mem_monomialSubgroup L _,
      mapsRootLines_canonicalRep (R := L) (rootReflection β)⟩
  obtain ⟨-, hcellEq, hcover, hdisj, hbij, hB, huniq, -, -, hequiv⟩ :=
    orthogonal_union_Bruhat_cell_factorization τ L χ J n hn
  have hsin : s ∈ ⋃ w ∈ unionWeylGroup χ J, unionCell L χ J n w := by
    rw [← hcover]
    exact hs
  rw [Set.mem_iUnion] at hsin
  obtain ⟨w, hsin⟩ := hsin
  rw [Set.mem_iUnion] at hsin
  obtain ⟨hw, hsw⟩ := hsin
  let nw : ModGL τ L := canonicalRep (coxeterSystem τ) L w
  have hmono : ∀ v ∈ unionWeylGroup χ J,
      canonicalRep (coxeterSystem τ) L v ∈ unionMonomial L χ J n := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact lift_mem_unionMonomial hβ
    | one =>
      rw [canonicalRep_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [canonicalRep_inv_charTwo]
      exact inv_mem hx
  have hliftw : nw ∈ unionLifts L χ J n w :=
    ⟨hmono w hw, mapsRootLines_canonicalRep (R := L) w⟩
  let θℝ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ) :=
    latticeRealExt (θ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
  have hθℝ_toReal : ∀ v, θℝ (toReal v) = toReal (θ v) :=
    fun v => latticeRealExt_toReal _ v
  have hθℝ : ∀ x y, rform (θℝ x) (θℝ y) = rform x y := by
    dsimp only [θℝ]
    exact latticeRealExt_isometry _ hθ
  have hθΔroot : Set.BijOn θ (unionSimpleRoots χ J) (unionSimpleRoots χ J) := by
    have h := bijOn_simpleRoots_of_bijOn_posRoots (τ := τ) (Ψ := unionRoots χ J) (θ := θ)
      (fun α hα => isRoot_of_mem_unionRoots hα) hΨ hΨp
    rwa [show (simpleRoots (unionRoots χ J) : Set _) = unionSimpleRoots χ J from
      Set.ext fun β => mem_simpleRoots_unionRoots_iff] at h
  have hθℝΨ : Set.BijOn θℝ (toReal '' unionRoots χ J) (toReal '' unionRoots χ J) :=
    bijOn_latticeRealExt (f := (θ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))) θ.injective hΨ.image_eq
  have hθℝΔ : Set.BijOn θℝ (toReal '' unionSimpleRoots χ J)
      (toReal '' unionSimpleRoots χ J) :=
    bijOn_latticeRealExt (f := (θ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)))
      θ.injective hθΔroot.image_eq
  have hQconj : ∀ γ, IsRoot τ γ → ∃ μ : Lˣ, ∀ c : L,
      Q * pinnedX τ L γ c * Q⁻¹ = pinnedX τ L (θ γ) (μ * c) :=
    fun γ hγ => ⟨1, fun c => by simpa only [Units.val_one, one_mul] using hQX γ hγ c⟩
  have hFpin : ∀ α, IsRoot τ α →
      frobTwistGL τ L 2 e Q (pinnedX τ L α 1) = pinnedX τ L (θ α) 1 := by
    intro α hα
    rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, iterateFrobenius_def, one_pow,
      hQX α hα 1]
  let F : MulAut (adjointGroup τ L) := frobTwistAut 2 e Q hQ
  have hcoeF : ∀ x : adjointGroup τ L, (F x : ModGL τ L) = frobTwistGL τ L 2 e Q x :=
    fun x => coe_frobTwistAut 2 e Q hQ x
  obtain ⟨A, hA, -, N, hNpos, hAN⟩ :=
    CFSG.HardMathSupport.C14W1.exists_lattice_map Q hQT
  have hnormQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨t, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
      rw [hA t]
      exact rootDiagUnit_mem_torusGroup _
    · intro hy
      obtain ⟨s', hs'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      have hsurj : CFSG.HardMathSupport.C14Torus.tmap A
          (CFSG.HardMathSupport.C14Torus.tmap (A ^ m) s') = s' := by
        rw [CFSG.HardMathSupport.C14Torus.tmap_tmap, ← pow_succ, hAN,
          CFSG.HardMathSupport.C14Torus.tmap_one_left]
      have htd : y = rootDiagUnit τ (CFSG.HardMathSupport.C14Torus.tmap (A ^ m) s') := by
        have h1 : Q * y * Q⁻¹ = rootDiagUnit τ s' := hs'
        have h2 : Q * rootDiagUnit τ
            (CFSG.HardMathSupport.C14Torus.tmap (A ^ m) s') * Q⁻¹ =
            rootDiagUnit τ s' := by rw [hA, hsurj]
        exact mul_left_cancel (mul_right_cancel (h1.trans h2.symm))
      rw [htd]
      exact rootDiagUnit_mem_torusGroup _
  have hmapTorus : (torusGroup τ L).map (frobTwistGL τ L 2 e Q) = torusGroup τ L :=
    map_frobTwistGL_torusGroup 2 e hnormQ
  have hmapΨ : (rootSpan τ L (unionRoots χ J)).map (frobTwistGL τ L 2 e Q) =
      rootSpan τ L (unionRoots χ J) := by
    rw [map_frobTwistGL_rootSpan_of_conj 2 e hQconj
      (fun α hα => isRoot_of_mem_unionRoots hα), hΨ.image_eq]
  have hmapΨp : (rootSpan τ L (posRoots (unionRoots χ J))).map
      (frobTwistGL τ L 2 e Q) = rootSpan τ L (posRoots (unionRoots χ J)) := by
    rw [map_frobTwistGL_rootSpan_of_conj 2 e hQconj
      (fun α hα => isRoot_of_mem_unionRoots hα.1), hΨp.image_eq]
  have hFH : ((torusGroup τ L).subgroupOf (adjointGroup τ L)).map F.toMonoidHom =
      (torusGroup τ L).subgroupOf (adjointGroup τ L) :=
    map_subgroupOf_adjointGroup (fun x => hcoeF x) torusGroup_le_adjointGroup hmapTorus
  have hFU : ∀ α ∈ unionRoots χ J, ∀ α' ∈ unionRoots χ J,
      θℝ (toReal α) = toReal α' →
      ((rootSubgroup τ L α).subgroupOf (adjointGroup τ L)).map F.toMonoidHom =
        (rootSubgroup τ L α').subgroupOf (adjointGroup τ L) := by
    intro α hα α' _ hαα'
    have hα'eq : α' = θ α := by
      apply toReal_injective
      rw [← hαα', latticeRealExt_toReal]
      rfl
    subst hα'eq
    exact map_subgroupOf_adjointGroup (fun x => hcoeF x)
      (rootSubgroup_le_adjointGroup α)
      (map_frobTwistGL_rootSubgroup_of_conj 2 e hQconj (isRoot_of_mem_unionRoots hα))
  have hFn : ∀ β ∈ unionSimpleRoots χ J, ∀ β' ∈ unionSimpleRoots χ J,
      θℝ (toReal β) = toReal β' → ∀ x : adjointGroup τ L,
      (x : ModGL τ L) = n β →
      ∃ t ∈ unionTorus L χ J, (F x : ModGL τ L) = t * n β' := by
    intro β hβ β' _ hββ' x hx
    have hβ'eq : β' = θ β := by
      apply toReal_injective
      rw [← hββ', latticeRealExt_toReal]
      rfl
    subst hβ'eq
    have hβΨ : β ∈ unionRoots χ J := mem_unionRoots_of_mem_unionSimpleRoots hβ
    have hθβ : IsRoot τ (θ β) := isRoot_of_mem_unionRoots (hΨ.mapsTo hβΨ)
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, hcoeF, hx]
    dsimp only [n]
    exact map_canonicalRep_rootReflection_charTwo (frobTwistGL τ L 2 e Q)
      (isRoot_of_mem_unionSimpleRoots hβ) hθβ (hFpin β (isRoot_of_mem_unionRoots hβΨ))
      (by simpa only [map_neg] using hFpin (-β) (isRoot_of_mem_unionRoots (neg_mem_unionRoots hβΨ)))
  obtain ⟨w', hw', hconj, -, hcelliff⟩ :=
    hequiv θℝ F hθℝ hθℝΨ hθℝΔ hFH hFU hFn w hw
  let x : adjointGroup τ L := ⟨s, unionRootSpan_le_adjointGroup hs⟩
  have hxcoe : (x : ModGL τ L) = s := rfl
  have hFx : F x = x := by
    apply Subtype.ext
    rw [hcoeF, hxcoe, hσ]
  have hsw' : s ∈ unionCell L χ J n w' := by
    have h := (hcelliff x).2 (by rwa [hxcoe])
    rwa [hFx, hxcoe] at h
  have hww' : w' = w := by
    by_contra hne
    exact (Set.disjoint_left.1 (hdisj w hw w' hw' (fun h => hne h.symm)) hsw) hsw'
  subst w'
  have hwθ : ∀ α ∈ unionRoots χ J, θ (w • α) = w • θ α := by
    intro α hα
    have h := hconj α hα (θ α) (hΨ.mapsTo hα) (hθℝ_toReal α)
    rw [hθℝ_toReal] at h
    exact toReal_injective h
  have hθref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
      θ (rootReflection γ • α) = rootReflection (θ γ) • θ α := by
    intro γ hγ α hα
    have hγr := isRoot_of_mem_unionRoots hγ
    have hθγ : IsRoot τ (θ γ) := isRoot_of_mem_unionRoots (hΨ.mapsTo hγ)
    rw [rootReflection_smul hγr, rootReflection_smul hθγ]
    have hc : corootPair (θ γ) (θ α) = corootPair γ α := by
      unfold corootPair
      rw [hθ γ α, hθ γ γ]
    simp only [map_sub, map_zsmul, hc]
  have hσnw : frobTwistGL τ L 2 e Q nw = nw := by
    dsimp only [nw]
    exact map_canonicalRep_eq_self_of_commute (frobTwistGL τ L 2 e Q)
      (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) hΨ hθref
      (fun α hα => hFpin α (isRoot_of_mem_unionRoots hα)) hw hwθ
  have hIeq : θ '' unionInversionRoots χ J w = unionInversionRoots χ J w := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      refine ⟨hΨp.mapsTo hβ.1, ?_⟩
      have hθw : θ (w • β) = w • θ β := hwθ β hβ.1.1
      have hneg : -(w • β) ∈ posRoots (unionRoots χ J) :=
        ⟨neg_mem_unionRoots (smul_mem_unionRoots hw hβ.1.1),
          by rw [height_neg]; exact neg_pos.2 hβ.2⟩
      have hpos := hΨp.mapsTo hneg
      rw [map_neg] at hpos
      have hheight : height (θ (w • β)) < 0 := by
        have := hpos.2
        rw [height_neg] at this
        exact neg_pos.mp this
      rwa [← hθw]
    · intro hα
      obtain ⟨β, hβ, hβθ⟩ := hΨp.surjOn hα.1
      refine ⟨β, ⟨hβ, ?_⟩, hβθ⟩
      have hθw : θ (w • β) = w • θ β := hwθ β hβ.1
      have hwβ : w • β ∈ unionRoots χ J := smul_mem_unionRoots hw hβ.1
      have hroot := isRoot_of_mem_unionRoots hwβ
      rcases IsRoot.height_pos_or_neg hroot with hpos | hneg
      · have hmem : w • β ∈ posRoots (unionRoots χ J) := ⟨hwβ, hpos⟩
        have h := hΨp.mapsTo hmem
        have hEq : θ (w • β) = w • α := by rw [hθw, hβθ]
        rw [hEq] at h
        exfalso
        exact (lt_asymm hα.2) h.2
      · exact hneg
  have hmapI : (rootSpan τ L (unionInversionRoots χ J w)).map
      (frobTwistGL τ L 2 e Q) = rootSpan τ L (unionInversionRoots χ J w) := by
    rw [map_frobTwistGL_rootSpan_of_conj 2 e hQconj
      (fun α hα => isRoot_of_mem_unionRoots hα.1.1), hIeq]
  have hFT : ∀ t ∈ unionTorus L χ J,
      frobTwistGL τ L 2 e Q t ∈ unionTorus L χ J := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem (frobTwistGL τ L 2 e Q) ht.1
      rw [show unionRootSpan L χ J = rootSpan τ L (unionRoots χ J) from rfl, hmapΨ] at h
      exact h
    · have h := Subgroup.mem_map_of_mem (frobTwistGL τ L 2 e Q) ht.2
      rw [hmapTorus] at h
      exact h
  have hFUpos : ∀ u ∈ unionUnipotent L χ J,
      frobTwistGL τ L 2 e Q u ∈ unionUnipotent L χ J := by
    intro u hu
    have h := Subgroup.mem_map_of_mem (frobTwistGL τ L 2 e Q) hu
    rw [show unionUnipotent L χ J = rootSpan τ L (posRoots (unionRoots χ J)) from rfl,
      hmapΨp] at h
    exact h
  have hFUI : ∀ u ∈ rootSpan τ L (unionInversionRoots χ J w),
      frobTwistGL τ L 2 e Q u ∈ rootSpan τ L (unionInversionRoots χ J w) := by
    intro u hu
    have h := Subgroup.mem_map_of_mem (frobTwistGL τ L 2 e Q) hu
    rw [hmapI] at h
    exact h
  have hFB : ∀ b ∈ unionBorel L χ J,
      frobTwistGL τ L 2 e Q b ∈ unionBorel L χ J := by
    intro b hb
    rw [← SetLike.mem_coe, coe_unionBorel, Set.mem_mul] at hb ⊢
    obtain ⟨t, ht, u, hu, rfl⟩ := hb
    exact ⟨_, hFT t ht, _, hFUpos u hu, (map_mul _ _ _).symm⟩
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := (hbij w hw nw hliftw).surjOn
    (by rw [hcellEq w hw nw hliftw]; exact hsw)
  have hb' : frobTwistGL τ L 2 e Q b ∈ unionBorel L χ J := hFB b hb
  have hu' : frobTwistGL τ L 2 e Q u ∈ rootSpan τ L (unionInversionRoots χ J w) :=
    hFUI u hu
  have heq' : frobTwistGL τ L 2 e Q b * nw * frobTwistGL τ L 2 e Q u = s := by
    have h := congrArg (frobTwistGL τ L 2 e Q) hbu
    rw [map_mul, map_mul, hσnw, hσ] at h
    exact h
  have hpair : (b, u) = (frobTwistGL τ L 2 e Q b, frobTwistGL τ L 2 e Q u) :=
    ((hbij w hw nw hliftw).injOn ⟨hb', hu'⟩ ⟨hb, hu⟩
      (heq'.trans hbu.symm)).symm
  have hbfix : frobTwistGL τ L 2 e Q b = b := (congrArg Prod.fst hpair).symm
  have hufix : frobTwistGL τ L 2 e Q u = u := (congrArg Prod.snd hpair).symm
  have hbTU : b ∈ (unionTorus L χ J : Set (ModGL τ L)) *
      (unionUnipotent L χ J : Set (ModGL τ L)) := by
    rw [← hB]
    exact hb
  obtain ⟨t, ht, u1, hu1, htu⟩ := Set.mem_mul.1 hbTU
  have htu' : t * u1 = frobTwistGL τ L 2 e Q t * frobTwistGL τ L 2 e Q u1 := by
    rw [htu, ← hbfix, ← map_mul, htu]
  obtain ⟨htfix, hu1fix⟩ := huniq t ht (frobTwistGL τ L 2 e Q t) (hFT t ht) u1 hu1
    (frobTwistGL τ L 2 e Q u1) (hFUpos u1 hu1) htu'
  have htuU : u ∈ unionUnipotent L χ J :=
    rootSpan_mono (fun α hα => hα.1) hu
  refine ⟨w, hw, hwθ, t, ht, htfix.symm, u1, hu1, hu1fix.symm, u, htuU, hufix, ?_⟩
  rw [← hbu, ← htu]

end CFSG.HardMathSupport.C14Idx
