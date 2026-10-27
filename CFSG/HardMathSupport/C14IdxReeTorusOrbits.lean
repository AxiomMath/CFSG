module

public import CFSG.HardMathSupport.C14IdxReeOrbit
public import CFSG.HardMathSupport.C14IdxReeA2Cycle
public import CFSG.HardMathSupport.C14IdxReeOrbitTools
public import CFSG.HardMathSupport.C14IdxReeB2Pair
public import CFSG.RankThree.PartOne.KLR.A1Twist

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
  CFSG.LieType.SeitzGeneration.ExcHighThree
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private theorem rootDiagUnit_coordTuple_orbit_mem
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    {α : Fin ReeTag.F4.tag.rank → ℤ} (hα : α ∈ simpleRoots (kernelRoots χ)) {n : ℕ}
    (hn : 0 < n) (hnα : (θ)^[n] α = α)
    (hmin : ∀ m, 0 < m → m < n → (θ)^[m] α ≠ α)
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a₀ β) :
    rootDiagUnit ReeTag.F4.tag
      (coordTuple ((Finset.range n).image fun i => (θ)^[i] α) c) ∈ Subgroup.closure
      {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
        x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
          ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  let O : Finset (Fin ReeTag.F4.tag.rank → ℤ) :=
    (Finset.range n).image fun i => (θ)^[i] α
  have hstep : ∀ ⦃x⦄, x ∈ simpleRoots (kernelRoots χ) → θ x ∈ simpleRoots (kernelRoots χ) :=
    fun {x} hx => by rw [hθ]; exact hΔ.mapsTo hx
  have hstepMap : Set.MapsTo θ (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)) :=
    fun x hx => hstep hx
  have hOsubΔ : ∀ β ∈ O, β ∈ simpleRoots (kernelRoots χ) :=
    range_image_iterate_subset hstepMap hα n
  have hOroot : ∀ β ∈ O, IsRoot ReeTag.F4.tag β := fun β hβ => simpleRoots_isRoot (hOsubΔ β hβ)
  have hOker : ∀ β ∈ O, β ∈ kernelRoots χ := fun β hβ => simpleRoots_subset (hOsubΔ β hβ)
  have hOinj : ∀ β ∈ O, ∀ γ ∈ O, θ β = θ γ → β = γ := by
    intro β hβ γ hγ h
    apply hΔ.injOn (hOsubΔ β hβ) (hOsubΔ γ hγ)
    change w • ReeTag.F4.dualRoot β = w • ReeTag.F4.dualRoot γ
    rw [← hθ β, ← hθ γ]; exact h
  have hOstable : ∀ β ∈ O, θ β ∈ O := range_image_iterate_stable hn hnα
  have hOcard : O.card = n := range_image_iterate_card hnα hmin
  have hclass := orthogonal_or_b2Pair_or_a2Cycle_ree (M := M) (χ := χ) (w := w) (θ := θ)
    hθ (fun x hx => hstep hx) hα hn hnα hmin
  have hcO : ∀ β ∈ O, c (θ β) = c β ^ rootExp a₀ β := fun β hβ => by
    rw [hθ]; exact hc β (hOsubΔ β hβ)
  rcases hclass with horth | ⟨hn2, hif⟩ | ⟨hn4, hαβ, horth2⟩
  ·
    have hOorth : ∀ β ∈ O, ∀ γ ∈ O, β ≠ γ → iform β γ = 0 := by
      intro β hβ γ hγ hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hβ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
      exact horth i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (fun h => hne (by rw [h]))
    let x : WeylGroup ReeTag.F4.tag := reflectionWordProd O.toList
    have hOrootList : ∀ β ∈ O.toList, IsRoot ReeTag.F4.tag β :=
      fun β hβ => hOroot β (Finset.mem_toList.1 hβ)
    have horthList : O.toList.Pairwise (fun β γ => iform β γ = 0) :=
      (Finset.nodup_toList O).pairwise_of_forall_ne fun β hβ γ hγ hne =>
        hOorth β (Finset.mem_toList.1 hβ) γ (Finset.mem_toList.1 hγ) hne
    have hx2 : x * x = 1 := reflectionWordProd_mul_self hOrootList horthList
    have hxO : ∀ β ∈ O, x • β = -β := fun β hβ =>
      reflectionWordProd_smul_of_mem hOrootList horthList (Finset.mem_toList.2 hβ)
    have hx : x ∈ unionWeylGroup χ Set.univ := by
      have h := reflectionWordProd_mem_unionWeylGroup_of_mem (M := M) (χ := χ) (J := Set.univ)
        (l := O.toList) (fun β hβ => by
          rw [unionRoots_univ_eq_kernelRoots]; exact hOker β (Finset.mem_toList.1 hβ))
      simpa [x] using h
    have hOθ : ∀ β ∈ O, w • ReeTag.F4.dualRoot β ∈ O := fun β hβ => by
      rw [← hθ]; exact hOstable β hβ
    have hconj : w * ReeTag.F4.weylPerm x * w⁻¹ = x := by
      have hweyl : ReeTag.F4.weylPerm x =
          reflectionWordProd (O.toList.map fun β => ReeTag.F4.dualRoot β) :=
        weylPerm_reflectionWordProd hOrootList
      have hmap : w * reflectionWordProd (O.toList.map fun β => ReeTag.F4.dualRoot β) * w⁻¹ =
          reflectionWordProd (O.toList.map θ) := by
        rw [mul_reflectionWordProd_mul_inv w (l := O.toList.map fun β => ReeTag.F4.dualRoot β)
          (fun δ hδ => by
            obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hδ
            exact ReeTag.isRoot_dualRoot (hOroot β (Finset.mem_toList.1 hβ)))]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro β _
        exact (hθ β).symm
      rw [hweyl, hmap]
      exact reflectionWordProd_map_eq_of_mem_fun hOstable hOinj hOroot hOorth
    exact rootDiagUnit_coordTuple_mem_closure_of_reeInvolution (J := Set.univ) hF
      (fun β hβ => by rw [unionRoots_univ_eq_kernelRoots]; exact hOker β hβ)
      hOθ hx hx2 hxO (CFSG.Quasithin.B42F4.canonicalRep_mem_twistedFixed hF hconj) c
      (fun β hβ => by rw [← hθ]; exact hcO β hβ)
  ·
    let β : Fin ReeTag.F4.tag.rank → ℤ := θ α
    have hβΔ : β ∈ simpleRoots (kernelRoots χ) := hstep hα
    have hne : α ≠ β := by
      intro h; exact hmin 1 (by omega) (by omega) (by simpa [β] using h.symm)
    have hθ2 : (θ)^[2] α = α := by rwa [hn2] at hnα
    have hβeq : β = w • ReeTag.F4.dualRoot α := hθ α
    have hαeq : w • ReeTag.F4.dualRoot β = α := by rw [← hθ β]; exact hθ2
    have hdata := reeB2Pair_data (M := M) (χ := χ) (F := F) hF hα hβΔ hβeq hαeq hne hif
    let γ : Fin ReeTag.F4.tag.rank → ℤ := rootReflection β • α
    let x : WeylGroup ReeTag.F4.tag := rootReflection α * rootReflection γ
    have hγker : γ ∈ kernelRoots χ := by simpa [γ] using hdata.1
    have hx : x ∈ unionWeylGroup χ Set.univ := by simpa [x, γ] using hdata.2.1
    have hx2 : x * x = 1 := by simpa [x, γ] using hdata.2.2.1
    have hxα : x • α = -α := by simpa [x, γ] using hdata.2.2.2.1
    have hxβ : x • β = -β := by simpa [x, γ] using hdata.2.2.2.2.1
    have hxσ : canonicalRep (coxeterSystem ReeTag.F4.tag) L x ∈
        twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
      simpa [x, γ] using hdata.2.2.2.2.2.2
    have hO : O = ({α, β} : Finset (Fin ReeTag.F4.tag.rank → ℤ)) := by
      rw [show O = (Finset.range n).image (fun i => (θ)^[i] α) from rfl, hn2]
      ext x
      simp only [Finset.mem_image, Finset.mem_range, β]
      constructor
      · rintro ⟨i, hi, rfl⟩
        interval_cases i <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨0, by omega, by simp⟩
        · exact ⟨1, by omega, by simp⟩
    exact rootDiagUnit_coordTuple_mem_closure_of_reeInvolution (J := Set.univ) hF
      (fun δ hδ => by rw [unionRoots_univ_eq_kernelRoots]; exact hOker δ hδ)
      (fun δ hδ => by rw [← hθ]; exact hOstable δ hδ) hx hx2
      (by
        intro δ hδ
        have hδ' : δ ∈ O := hδ
        rw [hO] at hδ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hδ'
        rcases hδ' with rfl | rfl
        · exact hxα
        · exact hxβ) hxσ c (fun β hβ => by rw [← hθ]; exact hcO β hβ)
  ·
    let β : Fin ReeTag.F4.tag.rank → ℤ := (θ)^[2] α
    have hb : oddDerivPairB ReeTag.F4.tag α β = true := oddDerivPairB_iff.mpr hαβ
    simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
    have hsumroot : IsRoot ReeTag.F4.tag (α + β) := RootOps.isRootB_iff.1 hb.1.1.1.2
    have hne : α ≠ β := by
      intro h
      exact hmin 2 (by omega) (by omega) (by simpa [β] using h.symm)
    have hθ4 : (θ)^[4] α = α := by rw [← hn4]; exact hnα
    have hβΔ : β ∈ simpleRoots (kernelRoots χ) := by
      rw [show β = (θ)^[2] α from rfl]; exact hstepMap.iterate 2 hα
    have hβker : β ∈ kernelRoots χ := simpleRoots_subset hβΔ
    have hαker : α ∈ kernelRoots χ := simpleRoots_subset hα
    have hsumker : α + β ∈ kernelRoots χ := ⟨hsumroot, by
      rw [ofAdd_add, map_mul, hαker.2, hβker.2, one_mul]⟩
    have hOeq : O = (Finset.range 4).image fun i => (θ)^[i] α := by
      rw [show O = (Finset.range n).image (fun i => (θ)^[i] α) from rfl, hn4]
    have hOcard4 : O.card = 4 := by rw [hOcard, hn4]
    have hq : ReeTag.F4.quadForm α = ReeTag.F4.quadForm β := by
      have hθ2 : β = (w * ReeTag.F4.weylPerm w) • α := by
        show θ (θ α) = (w * ReeTag.F4.weylPerm w) • α
        rw [hθ, hθ, ReeTag.dualRoot_smul w (ReeTag.isRoot_dualRoot (simpleRoots_isRoot hα)),
          ReeTag.dualRoot_dualRoot (simpleRoots_isRoot hα), mul_smul]
      rw [hθ2, quadForm_smul]
    have hqsum : iform (α + β) (α + β) = iform α α :=
      a2_quadForm_add_eq hα hβΔ hne hsumroot
        (by
          have h := hq
          rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at h
          exact h)
    have hadd : θ (α + β) = θ α + θ β := by
      simp only [hθ]
      rw [dualRoot_add_of_quadForm_eq (simpleRoots_isRoot hα) (simpleRoots_isRoot hβΔ) hsumroot
        hq (by
          rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform]
          exact hqsum), smul_add]
    have hθneg : ∀ x, IsRoot ReeTag.F4.tag x → θ (-x) = -θ x := fun x hx => by
      simp only [hθ]
      rw [CFSG.RankThree.PartOne.KLR.dualRoot_neg hx, smul_neg]
    have hθαroot : IsRoot ReeTag.F4.tag (θ α) := by
      rw [hθ]; exact (hΨ.mapsTo hαker).1
    have hθ2θ : θ (θ (θ α)) = (w * ReeTag.F4.weylPerm w) • (θ α) := by
      rw [hθ, hθ]
      rw [ReeTag.dualRoot_smul w (ReeTag.isRoot_dualRoot hθαroot),
        ReeTag.dualRoot_dualRoot hθαroot, mul_smul]
    have hqθ : iform (θ α) (θ α) = iform (θ β) (θ β) := by
      have h : θ β = (w * ReeTag.F4.weylPerm w) • (θ α) := by
        show θ (θ (θ α)) = (w * ReeTag.F4.weylPerm w) • (θ α)
        exact hθ2θ
      rw [h, iform_smul]
    have hneθ : θ α ≠ θ β := by
      intro h
      exact hne (by
        apply hΔ.injOn hα hβΔ
        change w • ReeTag.F4.dualRoot α = w • ReeTag.F4.dualRoot β
        rw [← hθ α, ← hθ β]
        exact h)
    have hqθsum : iform (θ α + θ β) (θ α + θ β) = iform (θ α) (θ α) :=
      a2_quadForm_add_eq (hstep hα) (hstep hβΔ) hneθ
        (by rw [← hadd, hθ]; exact (hΨ.mapsTo hsumker).1)
        hqθ
    have hqmul : iform (θ α) (θ α) * iform α α = 8 := by
      have h := (ReeTag.rootDualityCheck_spec (simpleRoots_isRoot hα)).2.2.2.2.1
      rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at h
      have hw : iform (θ α) (θ α) = iform (ReeTag.F4.dualRoot α) (ReeTag.F4.dualRoot α) := by
        rw [hθ α, iform_smul]
      rw [hw]
      simpa [ReeTag.prime] using h
    have hcomm := a2Cycle_commute (L := L) (M := M) (χ := χ) (w := w) (θ := θ) hθ hΨ hα hβΔ
      hsumroot hadd hθneg (by
        have h := hq
        rw [ReeTag.F4.quadForm_eq_iform, ReeTag.F4.quadForm_eq_iform] at h
        exact h)
      hqsum hqθ hqθsum (by rw [mul_comm]; exact hqmul) horth2
    have hmem := rootDiagUnit_coordTuple_mem_closure_of_reeA2Cycle (θ := θ) hF hθ hαβ hθ4
      hcomm hOeq hOcard4 c hcO
    refine Subgroup.closure_mono ?_ hmem
    intro x hx
    refine ⟨?_, hx.2.1, hx.2.2⟩
    have hx' : x ∈ rootSpan ReeTag.F4.tag L (kernelRoots χ) := by
      refine rootSpan_mono ?_ hx.1
      intro γ hγ
      obtain ⟨i, hi, δ, hδ, rfl⟩ := hγ
      interval_cases i
      · exact a2PairRoots_subset_kernelRoots hαker hβker hsumker hδ
      · simpa [Function.iterate_one, hθ] using
          hΨ.mapsTo (a2PairRoots_subset_kernelRoots hαker hβker hsumker hδ)
    simpa only [unionRootSpan, unionRoots_univ_eq_kernelRoots] using hx'
private theorem rootDiagUnit_coordTuple_mem_of_stable_subset
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a₀ β) :
    ∀ A : Finset (Fin ReeTag.F4.tag.rank → ℤ), A ⊆ simpleRoots (kernelRoots χ) →
      (∀ β ∈ A, θ β ∈ A) → rootDiagUnit ReeTag.F4.tag (coordTuple A c) ∈ Subgroup.closure
        {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
          x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
            ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  intro A
  refine Finset.strongInduction (p := fun A => A ⊆ simpleRoots (kernelRoots χ) →
      (∀ β ∈ A, θ β ∈ A) → rootDiagUnit ReeTag.F4.tag (coordTuple A c) ∈ Subgroup.closure
        {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
          x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
            ∃ k : ℕ, x ^ 2 ^ k = 1}) ?_ A
  intro A ih hA hAθ
  by_cases hA0 : A.Nonempty
  · obtain ⟨α, hαA⟩ := hA0
    have hα : α ∈ simpleRoots (kernelRoots χ) := hA hαA
    have hstep : ∀ ⦃x⦄, x ∈ simpleRoots (kernelRoots χ) → θ x ∈ simpleRoots (kernelRoots χ) :=
      fun {x} hx => by rw [hθ]; exact hΔ.mapsTo hx
    have hθinjA : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → θ x = θ y → x = y :=
      fun {x} hx {y} hy h => hΔ.injOn (hA hx) (hA hy) (by
        rw [← hθ x, ← hθ y]; exact h)
    obtain ⟨N, hNpos, hNα⟩ : ∃ N, 0 < N ∧ (θ)^[N] α = α := by
      obtain ⟨d, hd, hdA⟩ := exists_iterate_eq_of_mapsTo A.finite_toSet
        (fun x hx => hAθ x hx) hθinjA
      exact ⟨d, hd, hdA α hαA⟩
    let n : ℕ := Function.minimalPeriod (θ) α
    have hper : Function.IsPeriodicPt θ N α := hNα
    have hn : 0 < n := hper.minimalPeriod_pos hNpos
    have hnα : (θ)^[n] α = α := Function.iterate_minimalPeriod
    have hmin : ∀ m, 0 < m → m < n → (θ)^[m] α ≠ α :=
      fun m hm hlt => Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hm.ne' hlt
    let O : Finset (Fin ReeTag.F4.tag.rank → ℤ) :=
      (Finset.range n).image fun i => (θ)^[i] α
    have hstepMapA : Set.MapsTo θ (A : Set (Fin ReeTag.F4.tag.rank → ℤ))
        (A : Set (Fin ReeTag.F4.tag.rank → ℤ)) := fun x hx => hAθ x hx
    have hOsubA : O ⊆ A := range_image_iterate_subset hstepMapA hαA n
    have hαO : α ∈ O := mem_range_image_iterate (θ := θ) (α := α) hn
    have hO_mem := rootDiagUnit_coordTuple_orbit_mem hF hθ hΨ hΔ hα hn hnα hmin c hc
    have hA'Δ : A \ O ⊆ simpleRoots (kernelRoots χ) := fun x hx =>
      hA (Finset.sdiff_subset hx)
    have hA'θ : ∀ β ∈ A \ O, θ β ∈ A \ O := by
      intro β hβ
      obtain ⟨hβA, hβO⟩ := Finset.mem_sdiff.1 hβ
      refine Finset.mem_sdiff.2 ⟨hAθ β hβA, fun hθO => hβO ?_⟩
      exact mem_range_image_iterate_of_theta_mem hstepMapA
        (fun x hx y hy h => hθinjA hx hy h) hn hnα hαA hβA hθO
    have hsub : A \ O ⊂ A := Finset.sdiff_ssubset hOsubA ⟨α, hαO⟩
    have hA'mem := ih (A \ O) hsub hA'Δ hA'θ
    have hcoord : coordTuple (O ∪ A \ O) c =
        coordTuple O c * coordTuple (A \ O) c := by
      funext i
      simp only [coordTuple, Pi.mul_apply]
      exact Finset.prod_union Finset.disjoint_sdiff
    rw [← Finset.union_sdiff_of_subset hOsubA, hcoord, rootDiagUnit_mul]
    exact (Subgroup.closure _).mul_mem hO_mem hA'mem
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA0
    rw [hAe]
    have hcoord : coordTuple (∅ : Finset (Fin ReeTag.F4.tag.rank → ℤ)) c = 1 := by
      funext i; simp [coordTuple]
    rw [hcoord, rootDiagUnit_one]
    exact (Subgroup.closure _).one_mem

theorem rootDiagUnit_coordTuple_mem_closure_of_reeSimpleRoots
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΔ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α)
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin ReeTag.F4.tag.rank → ℤ)))
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ simpleRoots (kernelRoots χ), c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a₀ β) :
    rootDiagUnit ReeTag.F4.tag (coordTuple (simpleRoots (kernelRoots χ)) c) ∈ Subgroup.closure
      {x : ModGL ReeTag.F4.tag L | x ∈ unionRootSpan L χ Set.univ ∧
        x ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
          ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  exact rootDiagUnit_coordTuple_mem_of_stable_subset hF (fun _ => rfl) hΨ hΔ c hc
    (simpleRoots (kernelRoots χ)) (fun _ h => h) (fun _ h => hΔ.mapsTo h)

end CFSG.HardMathSupport.C14Idx
