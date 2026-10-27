module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthLane
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSuN
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.TwoDHighCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KD4T TauCeti
  CFSG.RankThree.Chevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Noncentral

theorem excOth_sl2_noncomm {K : Type} [Field K] {G : Type*} [Group G] (ρ : SL2 K →* G)
    (hker : ∀ B : SL2 K, ρ B = 1 → (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ¬ Commute (ρ (uSL 1)) (ρ (vSL 1)) := by
  intro h
  have h1 : ρ ⁅uSL (1 : K), vSL 1⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h.eq
  have h2 := hker _ h1
  rw [excOth_comm_uv_entry] at h2
  simp at h2

end Noncentral

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀]
  [IsAlgClosed k] {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

theorem ssOth_commute_orbitMap {O₀ O₁ : Set (Fin τ.rank → ℤ)} (hO₀ : O₀ ∈ D.orbits)
    (hO₁ : O₁ ∈ D.orbits)
    (horth : ∀ i j : ℕ, i < GenFixedRootDatum.orbitCard O₀ → j < GenFixedRootDatum.orbitCard O₁ →
      iform (D.orbitVec O₀ i) (D.orbitVec O₁ j) = 0)
    (A : SL2 (D.orbitField O₀)) (B : SL2 (D.orbitField O₁)) :
    Commute (D.orbitMap O₀ A) (D.orbitMap O₁ B) := by
  rw [GenFixedRootDatum.orbitMap_eq_prod, GenFixedRootDatum.orbitMap_eq_prod]
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have hr0 := D.isRoot_orbitVec hO₀ i
  have hr1 := D.isRoot_orbitVec hO₁ j
  have h0 := horth i j hi' hj'
  obtain ⟨hp, hm⟩ := excOth_not_isRoot_add_sub D.simplyLaced hr0 hr1 h0
  rw [GenFixedRootDatum.orbitFactor_apply, GenFixedRootDatum.orbitFactor_apply]
  exact rootSL2_commute_of_orth hr0 hr1 h0 hp hm _ _

theorem ssOth_orbitGroup_noL2 {O₀ O₁ : Set (Fin τ.rank → ℤ)} (hO₀ : O₀ ∈ D.orbits)
    (hO₁ : O₁ ∈ D.orbits)
    (horth : ∀ i j : ℕ, i < GenFixedRootDatum.orbitCard O₀ → j < GenFixedRootDatum.orbitCard O₁ →
      iform (D.orbitVec O₀ i) (D.orbitVec O₁ j) = 0)
    (h3 : 3 ≤ Nat.card (D.orbitField O₀)) : ExcOthNoL2 D.orbitGroup := by
  intro F _
  refine ⟨fun φ => ?_⟩
  let ρ₀ : SL2 (D.orbitField O₀) →* ↥D.orbitGroup :=
    (D.orbitMapHom hO₀).codRestrict D.orbitGroup (fun A => D.orbitMap_mem_orbitGroup hO₀ A)
  let ρ₁ : SL2 (D.orbitField O₁) →* ↥D.orbitGroup :=
    (D.orbitMapHom hO₁).codRestrict D.orbitGroup (fun A => D.orbitMap_mem_orbitGroup hO₁ A)
  have hker : ∀ {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
      (ρ : SL2 (D.orbitField O) →* ↥D.orbitGroup),
      (∀ A, ((ρ A : ↥D.orbitGroup) : ModGL τ k) = D.orbitMap O A) →
      ∀ B : SL2 (D.orbitField O), ρ B = 1 →
        (B : Matrix (Fin 2) (Fin 2) (D.orbitField O)) 1 0 = 0 := by
    intro O hO ρ hρ B hB
    have h1 : D.orbitMap O B = 1 := by
      rw [← hρ B, hB]
      rfl
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1 with rfl | rfl <;> simp
  have hker₀ := hker hO₀ ρ₀ (fun A => rfl)
  have hker₁ := hker hO₁ ρ₁ (fun A => rfl)
  have hcomm : ∀ (A : SL2 (D.orbitField O₀)) (B : SL2 (D.orbitField O₁)), Commute (ρ₀ A) (ρ₁ B) :=
    fun A B => Subtype.ext (ssOth_commute_orbitMap D hO₀ hO₁ horth A B)
  have hcen : ρ₁ (uSL 1) ∉ Subgroup.center ↥D.orbitGroup := by
    intro hz
    exact excOth_sl2_noncomm ρ₁ hker₁ (Subgroup.mem_center_iff.1 hz (ρ₁ (vSL 1))).symm
  exact excOth_sl2_heis φ ρ₀ h3 hker₀ hcen (fun s => hcomm _ _) (fun t => hcomm _ _)

end Datum

section Cfg

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}

theorem ssOth_exists_cfg
    (hΨ : IsRootComponent Ψ) (hsl : ∀ β ∈ Ψ, iform β β = 2) (h5 : 5 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∃ βa βb βk : Fin τ.rank → ℤ, βa ∈ simpleRoots Ψ ∧ βb ∈ simpleRoots Ψ ∧
      βk ∈ simpleRoots Ψ ∧ βa ≠ βb ∧ iform βa βk = 0 ∧ iform βb βk = 0 ∧ δ βa = βb ∧
        δ βk = βk := by
  classical
  have hsl' : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => hsl β (simpleRoots_subset hβ)
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hinj := injective_of_iform δ hiso
  have hf : IsIsometry Ψ δ :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg δ γ⟩
  obtain ⟨β₀, hβ₀, hδβ₀⟩ := hne
  have hΨne : Ψ.Nonempty := ⟨β₀, simpleRoots_subset hβ₀⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨δ (β : Fin τ.rank → ℤ), hf.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := fun β γ h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσdef
  have hσ : ∀ j, δ (e.symm j) = e.symm (σ j) := fun j => by
    rw [hσdef]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hπe, Equiv.ofBijective_apply, hπ]
  have hσM : ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j := by
    intro i j
    have h1 := he' (e.symm (σ i)) (e.symm (σ j))
    have h2 := he' (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ, ← hσ]
    exact corootPair_isometry hf (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := hσ (e ⟨β₀, hβ₀⟩)
    rw [h1, Equiv.Perm.one_apply, Equiv.symm_apply_apply] at h2
    exact hδβ₀ h2
  have hiform : ∀ x y : Fin t.rank, iform (e.symm x : Fin τ.rank → ℤ) (e.symm y) =
      t.cartanMatrix x y := by
    intro x y
    have h := he' (e.symm x) (e.symm y)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    have h2 := corootPair_mul (simpleRoots_isRoot (e.symm x).2) (e.symm y : Fin τ.rank → ℤ)
    rw [h, hsl' _ (e.symm x).2] at h2
    omega
  have key : ∀ {N : ℕ} {a b k : Fin t.rank}, a ≠ b → dGraphOK t.cartanMatrix a b N = true →
      k ≠ a → k ≠ b → t.cartanMatrix a k = 0 → t.cartanMatrix b k = 0 →
      ∃ βa βb βk : Fin τ.rank → ℤ, βa ∈ simpleRoots Ψ ∧ βb ∈ simpleRoots Ψ ∧
        βk ∈ simpleRoots Ψ ∧ βa ≠ βb ∧ iform βa βk = 0 ∧ iform βb βk = 0 ∧ δ βa = βb ∧
          δ βk = βk := by
    intro N a b k hab hchk hka hkb h2 h3
    obtain ⟨-, -, hsep, -⟩ := dGraphOK_spec hchk
    have hsw := (eq_one_or_eq_swap_of_sepPairB hsep hab hσM).resolve_left hσ1
    refine ⟨e.symm a, e.symm b, e.symm k, (e.symm a).2, (e.symm b).2, (e.symm k).2,
      fun h => hab (e.symm.injective (Subtype.ext h)), ?_, ?_, ?_, ?_⟩
    · rw [hiform]; exact h2
    · rw [hiform]; exact h3
    · rw [hσ, hsw, Equiv.swap_apply_left]
    · rw [hσ, hsw, Equiv.swap_apply_of_ne_of_ne hka hkb]
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · exact absurd (eq_one_of_sepB
      (List.all_eq_true.1 Certificates.certificate13659.1 t hmem) hσM) hσ1
  have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]
  rw [hN, hrank] at hcard
  rw [hrank] at h5
  simp only [countTypes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate13660
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd h5 (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd hcard (by decide)
  · exact absurd h5 (by decide)
  · exact key (a := ⟨3, by decide⟩) (b := ⟨4, by decide⟩) (k := ⟨1, by decide⟩)
      (by decide) h1 (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨4, by decide⟩) (b := ⟨5, by decide⟩) (k := ⟨2, by decide⟩)
      (by decide) h2 (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨5, by decide⟩) (b := ⟨6, by decide⟩) (k := ⟨3, by decide⟩)
      (by decide) h3 (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact key (a := ⟨6, by decide⟩) (b := ⟨7, by decide⟩) (k := ⟨4, by decide⟩)
      (by decide) h4 (by decide) (by decide)
      (by rw [DynkinType.cartanMatrix_D]; decide) (by rw [DynkinType.cartanMatrix_D]; decide)
  · exact absurd hcard (by decide)


end Cfg

section Core


variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem ssOth_twoD_core (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ}
    (he : 1 ≤ e) {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (h5 : 5 ≤ compRank (componentRoots χ i))
    (hcard : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ componentRoots χ i, δ γ ∈ componentRoots χ i)
    (hpos : ∀ γ ∈ posRoots (componentRoots χ i), δ γ ∈ posRoots (componentRoots χ i))
    (hG : IsGraphTwist (componentRoots χ i) δ)
    (hne : ∃ β ∈ simpleRoots (componentRoots χ i), δ β ≠ β) {c : ModGL τ L}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hcG : (adjointGroup τ L).map (MulAut.conj c).toMonoidHom = adjointGroup τ L)
    (hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e c) = rootSubgroup τ L (δ γ))
    (hpin : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e c (rootSL2 τ L β A) =
        rootSL2 τ L (δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A)) :
    ∃ C : Subgroup (ModGL τ L), CFSG.IsQuasisimple C ∧ Group.IsPerfect C ∧
      C ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ⁅rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _))⁆ ≤ C ∧
      ExcOthNoL2 C := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hinj := injective_of_iform δ hiso
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ δ :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg δ γ⟩
  have hΔΔ : ∀ β ∈ simpleRoots Ψ, δ β ∈ simpleRoots Ψ := fun β hβ =>
    hf.apply_mem_simpleRoots hΨ hpos hβ
  have himgΨ : δ '' Ψ = Ψ := by
    refine Set.Subset.antisymm (Set.image_subset_iff.2 hmaps) fun γ hγ => ?_
    exact ⟨δ γ, hmaps γ hγ, hG.invol γ hγ⟩
  have himgΔ : δ '' (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) = simpleRoots Ψ := by
    refine Set.Subset.antisymm (Set.image_subset_iff.2 fun β hβ => hΔΔ β hβ) fun γ hγ => ?_
    exact ⟨δ γ, hΔΔ γ hγ, hG.invol γ (simpleRoots_subset hγ)⟩
  obtain ⟨α₀, hα₀⟩ : (simpleRoots Ψ).Nonempty := by
    obtain ⟨⟨γ, hγ⟩, hγi⟩ := Quotient.exists_rep i
    have hγΨ : γ ∈ Ψ := ⟨hγ, hγi⟩
    obtain ⟨w, -, β, hβ, -⟩ := exists_smul_simpleRoot hΨ hγΨ
    exact ⟨β, hβ⟩
  have hα₀Ψ : α₀ ∈ Ψ := simpleRoots_subset hα₀
  have hk := kernelRoots_spanChar i
  have hus := unionSimpleRoots_spanChar i hα₀Ψ
  have hur := unionRoots_spanChar i
  have hα₀k : α₀ ∈ kernelRoots (spanChar Ψ) := by rw [hk]; exact hα₀Ψ
  obtain ⟨Sfr, hSfr⟩ := ((exceptional_Lang_root_coordinate_surjectivity r L).1 τ e he).1
  let Cc : MulAut (adjointGroup τ L) := ((adjointGroup τ L).equivMapOfInjective
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hcG)
  let F : MulAut (adjointGroup τ L) := Sfr.trans Cc
  have hF : ∀ x : adjointGroup τ L, (F x : ModGL τ L) = frobTwistGL τ L r e c x := by
    intro x
    rw [frobTwistGL_apply]
    change _ = c * Units.map (entrywiseHom (iterateFrobenius L r e)) (x : ModGL τ L) * c⁻¹
    rw [← hSfr x]
    rfl
  set θ := latticeRealExt δ with hθ
  have hθv : ∀ v, θ (toReal v) = toReal (δ v) := fun v => latticeRealExt_toReal δ v
  let D : GenFixedRootDatum τ r L (SpanQuot Ψ) :=
    { simplyLaced := hτ
      e := e
      one_le_e := he
      χ := spanChar Ψ
      θ := θ
      isometry := latticeRealExt_isometry δ hiso
      bijOn_kernelRoots := by
        rw [hk]
        exact bijOn_latticeRealExt hinj himgΨ
      bijOn_simpleRoots := by
        rw [hus]
        exact bijOn_latticeRealExt hinj himgΔ
      orbit_orthogonal := fun α hα β hβ γ hγ hne => by
        rw [hk] at hα
        rw [thetaOrbit_latticeRealExt hG hα] at hβ hγ
        rcases hβ with rfl | hβ <;> rcases hγ with rfl | hγ
        · exact absurd rfl hne
        · rw [Set.mem_singleton_iff] at hγ
          subst hγ
          exact hG.orth β hα (Ne.symm hne)
        · rw [Set.mem_singleton_iff] at hβ
          subst hβ
          rw [iform_comm]
          exact hG.orth γ hα hne
        · rw [Set.mem_singleton_iff] at hβ hγ
          exact absurd (hβ.trans hγ.symm) hne
      orbit_reflection := fun α hα => by
        rw [hk] at hα
        obtain ⟨w, hw, hwα⟩ := hG.reach α hα
        have hsub : {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
            g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))} ⊆
            (fun β => setReflection (thetaOrbit θ β)) ''
              unionSimpleRoots (spanChar Ψ) Set.univ := by
          rintro _ ⟨β, hβ, rfl⟩
          refine ⟨β, by rw [hus]; exact hβ, ?_⟩
          change setReflection (thetaOrbit (latticeRealExt δ) β) = _
          rw [thetaOrbit_latticeRealExt hG (simpleRoots_subset hβ)]
        refine ⟨w, Subgroup.closure_mono hsub hw, w • α, by rw [hus]; exact hwα, ?_⟩
        change (fun γ => w • γ) '' thetaOrbit (latticeRealExt δ) α =
          thetaOrbit (latticeRealExt δ) (w • α)
        rw [thetaOrbit_latticeRealExt hG hα, thetaOrbit_latticeRealExt hG (simpleRoots_subset hwα),
          Set.image_pair, smul_comm_of_mem_closure hG hΨ hiso hmaps hw]
      F := F
      map_torusGroup := map_subgroupOf_adjointGroup hF torusGroup_le_adjointGroup
        (map_frobTwistGL_torusGroup r e hcT)
      map_rootSubgroup := fun α hα α' h => by
        have e' : α' = δ α := toReal_injective (h.symm.trans (hθv α))
        subst e'
        rw [hk] at hα
        exact map_subgroupOf_adjointGroup hF (rootSubgroup_le_adjointGroup α) (hU α hα)
      map_rootSL2 := fun β hβ β' h A x hx => by
        have e' : β' = δ β := toReal_injective (h.symm.trans (hθv β))
        subst e'
        rw [hus] at hβ
        rw [hF, hx]
        exact hpin β hβ A
      J := Set.univ
      isThetaOrbit := ⟨⟦⟨α₀, hα₀k⟩⟧, by
        refine (Set.eq_univ_of_forall fun j => ?_).symm
        refine ⟨0, α₀, ?_, α₀, ?_, by rw [pow_zero, Module.End.one_apply]⟩
        · rw [componentRoots_spanChar i]
          exact hα₀Ψ
        · rw [componentRoots_spanChar i]
          exact hα₀Ψ⟩ }
  have hDroots : D.roots = Ψ := hur
  have hDsimple : D.simpleRootsJ = (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) := by
    change unionSimpleRoots (spanChar Ψ) Set.univ ∩ D.roots = _
    rw [hus, hDroots]
    exact Set.inter_eq_left.2 fun β hβ => simpleRoots_subset hβ
  have hDspan : D.rootSpanJ = rootSpan τ L Ψ := by
    change unionRootSpan L (spanChar Ψ) Set.univ = _
    rw [unionRootSpan, hur]
  have hroot : ∀ γ : Fin τ.rank → ℤ, GenFixedRootDatum.orbitRoot ({γ} : Set _) = γ := fun γ =>
    Set.mem_singleton_iff.1 (lexLeast_mem (Set.finite_singleton γ) (Set.singleton_nonempty γ))
  have horb : ∀ O ∈ D.orbits, ∃ β ∈ simpleRoots Ψ, O = {β, δ β} := by
    rintro O ⟨β, hβ, rfl⟩
    rw [hDsimple] at hβ
    exact ⟨β, hβ, thetaOrbit_latticeRealExt hG (simpleRoots_subset hβ)⟩
  have hq2 : 2 ≤ D.q := by
    change 2 ≤ r ^ e
    exact le_trans (Fact.out : r.Prime).two_le (Nat.le_self_pow (by omega) r)
  have hperf : Group.IsPerfect D.orbitGroup := by
    refine D.isPerfect_orbitGroup_of_forall fun O hO c => ?_
    obtain ⟨β, hβ, hOβ⟩ := horb O hO
    subst hOβ
    by_cases hfix : δ β = β
    · have h1O : GenFixedRootDatum.orbitCard ({β, δ β} : Set (Fin τ.rank → ℤ)) = 1 := by
        rw [hfix, Set.pair_eq_singleton]
        exact Set.ncard_singleton β
      have hrO : GenFixedRootDatum.orbitRoot ({β, δ β} : Set (Fin τ.rank → ℤ)) = β := by
        rw [hfix, Set.pair_eq_singleton]
        exact hroot β
      obtain ⟨β', hβ', hfix', hadj⟩ := hG.adj β hβ hfix
      have hP : thetaOrbit D.θ β' ∈ D.orbits := ⟨β', by rw [hDsimple]; exact hβ', rfl⟩
      have hPeq : thetaOrbit D.θ β' = {β'} := by
        change thetaOrbit (latticeRealExt δ) β' = _
        rw [thetaOrbit_latticeRealExt hG (simpleRoots_subset hβ'), hfix', Set.pair_eq_singleton]
      have h1P : GenFixedRootDatum.orbitCard (thetaOrbit D.θ β') = 1 := by
        rw [hPeq]
        exact Set.ncard_singleton β'
      have hrP : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ β') = β' := by
        rw [hPeq]
        exact hroot β'
      refine orbitXY_mem_commutator_of_adjacent_root D hP hO h1P h1O ?_ c
      rw [hrP, hrO, iform_comm]
      exact hadj
    · have h2 : GenFixedRootDatum.orbitCard ({β, δ β} : Set (Fin τ.rank → ℤ)) = 2 :=
        Set.ncard_pair (Ne.symm hfix)
      have h3 : 3 < Nat.card (D.orbitField {β, δ β}) := by
        rw [D.card_orbitField hO, h2]
        nlinarith
      exact D.gens_mem_commutator_of_three_lt hO h3 c
  have hO₀ : thetaOrbit D.θ α₀ ∈ D.orbits := ⟨α₀, by rw [hDsimple]; exact hα₀, rfl⟩
  have hqs := D.isQuasisimple_orbitGroup_of_isPerfect hO₀ hperf
  refine ⟨D.orbitGroup, hqs, hperf, fun g hg => ?_, ?_, ?_⟩
  · have hgC := D.orbitGroup_le_adjointGroup hg
    refine ⟨?_, hgC, ?_⟩
    · have := D.orbitGroup_le_rootSpanJ hg
      rwa [hDspan] at this
    · change frobTwistGL τ L r e c g = g
      have h := congrArg Subtype.val (F_eq_self_of_mem_orbitGroup D hg)
      rw [hF] at h
      exact h
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmem : ∀ z ∈ rootSpan τ L Ψ ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        ∃ z' : adjointGroup τ L, z' ∈ D.fixedGroup ∧ (z' : ModGL τ L) = z := by
      intro z hz
      refine ⟨⟨z, hz.2.1⟩, D.mem_fixedGroup.2 ⟨by rw [hDspan]; exact hz.1, ?_⟩, rfl⟩
      apply Subtype.ext
      rw [hF]
      exact hz.2.2
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    obtain ⟨y', hy', rfl⟩ := hmem y hy
    have h := D.commutator_fixedGroup_le (Subgroup.commutator_mem_commutator hx' hy')
    have h' := D.coe_mem_orbitGroup_of_mem_orbitGroupC h
    have e : ((⁅x', y'⁆ : adjointGroup τ L) : ModGL τ L) =
        ⁅(x' : ModGL τ L), (y' : ModGL τ L)⁆ :=
      map_commutatorElement (adjointGroup τ L).subtype x' y'
    rwa [e] at h'
  ·
    obtain ⟨βa, βb, βk, hβa, hβb, hβk, hab, hak, hbk, hδa, hδk⟩ :=
      ssOth_exists_cfg hΨ (fun β hβ => excOth_iform_self hτ (hΨ.isRoot β hβ)) h5 hcard δ hiso
        hmaps hpos hne
    have hOa : thetaOrbit D.θ βa ∈ D.orbits := ⟨βa, by rw [hDsimple]; exact hβa, rfl⟩
    have hOk : thetaOrbit D.θ βk ∈ D.orbits := ⟨βk, by rw [hDsimple]; exact hβk, rfl⟩
    have hOaeq : thetaOrbit D.θ βa = {βa, βb} := by
      change thetaOrbit (latticeRealExt δ) βa = _
      rw [thetaOrbit_latticeRealExt hG (simpleRoots_subset hβa), hδa]
    have hOkeq : thetaOrbit D.θ βk = {βk} := by
      change thetaOrbit (latticeRealExt δ) βk = _
      rw [thetaOrbit_latticeRealExt hG (simpleRoots_subset hβk), hδk, Set.pair_eq_singleton]
    have h2 : GenFixedRootDatum.orbitCard (thetaOrbit D.θ βa) = 2 := by
      rw [GenFixedRootDatum.orbitCard, hOaeq]
      exact Set.ncard_pair hab
    have horth : ∀ i j : ℕ, i < GenFixedRootDatum.orbitCard (thetaOrbit D.θ βa) →
        j < GenFixedRootDatum.orbitCard (thetaOrbit D.θ βk) →
        iform (D.orbitVec (thetaOrbit D.θ βa) i) (D.orbitVec (thetaOrbit D.θ βk) j) = 0 := by
      intro i j _ _
      have h1 := (Set.ext_iff.1 hOaeq _).1 (D.orbitVec_mem hOa i)
      have h2' := (Set.ext_iff.1 hOkeq _).1 (D.orbitVec_mem hOk j)
      rw [Set.mem_singleton_iff.1 h2']
      rcases h1 with h1 | h1
      · rw [h1]
        exact hak
      · rw [Set.mem_singleton_iff.1 h1]
        exact hbk
    have h3 : 3 ≤ Nat.card (D.orbitField (thetaOrbit D.θ βa)) := by
      rw [D.card_orbitField hOa, h2]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ D.q ^ 2 := Nat.pow_le_pow_left hq2 2
    exact ssOth_orbitGroup_noL2 D hOa hOk horth h3


end Core

section High


open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ssOth_twoD_high {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hcard : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1)) :
    ExcOthNoL2 (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have := hchar
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ), torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L :=
    fun T => sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  obtain ⟨v, hv, hmaps, hpos, hG⟩ := S.exists_isGraphTwistT hT i hkind h5
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry (componentRoots (rootCharHom a) i) (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg _ γ⟩
  have hΔ : ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i),
      S.rhoTwist v β ∈ simpleRoots (componentRoots (rootCharHom a) i) := fun β hβ =>
    hf.apply_mem_simpleRoots hΨ hpos hβ
  obtain ⟨y, hyZ, hyM, hyv, hpin⟩ := S.exists_twoD_pin hq i hv hΔ
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hyC : y ∈ adjointGroup τ L := hSC _ hyZ
  have hFc : ∀ g, frobTwistGL τ L r e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ L).map (MulAut.conj (y * Q)).toMonoidHom = adjointGroup τ L := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ L ⟨y, hyM⟩ = v := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e (y * Q)) =
        rootSubgroup τ L (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ L r e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i), ∀ A : SL2 L,
      frobTwistGL τ L r e (y * Q) (rootSL2 τ L β A) =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A) :=
    fun β hβ A => by rw [hFc]; exact hpin β hβ A
  have hne := ssexc_twoD_moves_simple_root S hT i hkind h5 hv hmaps
  obtain ⟨C, hCqs, hCperf, hCle, hcomm, hNoC⟩ := ssOth_twoD_core hτ
    (by omega : 1 ≤ e) i h5 hcard (S.rhoTwist v) hiso hmaps hpos hG hne hcT hcG hU hpin'
  have hyZ' : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
  obtain ⟨z, hzZ, hz⟩ := S.exists_lang_twoDT he hQT hstep hT hyZ'
  have hzC : z ∈ adjointGroup τ L := hSC _ hzZ
  have hzN := mem_normalizer_rootSpan_of_mem_Z hzZ i
  set φ : ModGL τ L →* ModGL τ L := (MulAut.conj z⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj z⁻¹).injective
  have hφapp : ∀ g, φ g = z⁻¹ * g * z := fun g => by
    rw [hφ]
    simp
  set M' : Subgroup (ModGL τ L) :=
    adjointGroup τ L ⊓ (frobTwistGL τ L r e (y * Q)).eqLocus (MonoidHom.id _) with hM'
  have hstepz : ∀ g, frobTwistGL τ L r e (y * Q) (z⁻¹ * g * z) = z⁻¹ * S.D.step g * z := by
    intro g
    rw [hFc, map_mul, map_mul, map_inv, hz]
    group
  have hMap : S.D.model.map φ = M' := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxC, hxF⟩, rfl⟩
      have hxs : S.D.step x = x := hxF
      rw [hφapp]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hzC) hxC) hzC, ?_⟩
      change frobTwistGL τ L r e (y * Q) (z⁻¹ * x * z) = z⁻¹ * x * z
      rw [hstepz, hxs]
    · rintro ⟨hgC, hgF⟩
      have hgF' : frobTwistGL τ L r e (y * Q) g = g := hgF
      refine ⟨z * g * z⁻¹, Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzC hgC) (inv_mem hzC), ?_⟩, ?_⟩
      · change S.D.step (z * g * z⁻¹) = z * g * z⁻¹
        have h1 := hstepz (z * g * z⁻¹)
        have e2 : z⁻¹ * (z * g * z⁻¹) * z = g := by group
        rw [e2, hgF'] at h1
        calc S.D.step (z * g * z⁻¹) = z * (z⁻¹ * S.D.step (z * g * z⁻¹) * z) * z⁻¹ := by group
          _ = z * g * z⁻¹ := by rw [← h1]
      · rw [hφapp]
        group
  have hrr : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
    S.rationalRoots_eq_of_five_leT hT i h5
  have hspan : (rootSpan τ L (componentRoots (rootCharHom a) i)).map φ =
      rootSpan τ L (componentRoots (rootCharHom a) i) :=
    CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (inv_mem hzN)
  have hRmap : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ =
      ⁅rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ ⁅M', M'⁆,
        rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ ⁅M', M'⁆⁆ := by
    rw [rationalComponent, rationalSpan, hrr, Subgroup.map_commutator,
      Subgroup.map_inf_eq _ _ _ hφinj, hspan]
    change ⁅_ ⊓ (⁅S.D.model, S.D.model⁆).map φ, _ ⊓ (⁅S.D.model, S.D.model⁆).map φ⁆ = _
    rw [Subgroup.map_commutator, hMap]
  have hRC : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ = C := by
    rw [hRmap]
    have hCC : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hCperf
    have hle : rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ ⁅M', M'⁆ ≤
        rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ M' :=
      inf_le_inf_left _ (Subgroup.commutator_le_self M')
    refine le_antisymm (le_trans (Subgroup.commutator_mono hle hle) hcomm) ?_
    have hCM : C ≤ M' := hCle.trans inf_le_right
    have hCle' : C ≤ rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ ⁅M', M'⁆ := by
      refine le_inf (hCle.trans inf_le_left) ?_
      rw [← hCC]
      exact Subgroup.commutator_mono hCM hCM
    calc C = ⁅C, C⁆ := hCC.symm
      _ ≤ _ := Subgroup.commutator_mono hCle' hCle'
  have e : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃* ↥C :=
    ((rationalComponent S.ρ S.Γ (rootCharHom a) i).equivMapOfInjective φ hφinj).trans
      (MulEquiv.subgroupCongr hRC)
  exact ExcOthNoL2.of_equiv e hNoC


end High

section Kind


theorem excTLKind_twoD {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ExcTLKind .twoD τ := by
  have _ := hτ
  intro L _ _ p₀ S a hT ha3 h1 i hk _ q _ hq
  classical
  have hL3 : (3 : L) ≠ 0 := by
    intro h3
    apply h1
    have ha1 : ∀ j, a j = 1 := by
      intro j
      have h' : ((a j : L)) ^ 3 = 1 := by
        have := congrArg Units.val (ha3 j)
        simpa using this
      have h0 : ((a j : L) - 1) ^ 3 = 0 := by
        linear_combination h' + (-(a j : L) ^ 2 + (a j : L)) * h3
      exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0))
    have : a = 1 := funext ha1
    rw [this, rootDiagUnit_one]
  have hTp : rootDiagUnit τ a ^ 3 = 1 := excOth_rootDiagUnit_pow_eq_one ha3
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · have hτ5 : 5 ≤ τ.rank := h5.trans (compRank_le_rank _)
    have hNo := ssOth_twoD_high S (simplyLaced_of_five_le_rank hτ5) hT i hk h5 hcard
    obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
    exact (hNo F).false e'
  · have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, h4']
    have hNo := ssOth_d4class S Nat.prime_three hL3 hT hTp h1 i h4' hc hnin hr
    obtain ⟨F, _, _, _, ⟨e'⟩⟩ := hq
    exact (hNo F).false e'

end Kind

end CFSG.HardMathSupport.Dickson.Sec6.I1431
