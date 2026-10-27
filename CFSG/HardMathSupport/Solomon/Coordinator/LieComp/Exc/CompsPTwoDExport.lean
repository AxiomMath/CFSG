module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDLabel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace CompsPTwoDExport


section Datum

variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_datum_pinned (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {e : ℕ} (he : 1 ≤ e)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ componentRoots χ i, δ γ ∈ componentRoots χ i)
    (hpos : ∀ γ ∈ posRoots (componentRoots χ i), δ γ ∈ posRoots (componentRoots χ i))
    (hG : IsGraphTwist (componentRoots χ i) δ) {c : ModGL τ L}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hcG : (adjointGroup τ L).map (MulAut.conj c).toMonoidHom = adjointGroup τ L)
    (hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e c) = rootSubgroup τ L (δ γ))
    (hpin : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e c (rootSL2 τ L β A) =
        rootSL2 τ L (δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A)) :
    ∃ D : GenFixedRootDatum τ r L (SpanQuot (componentRoots χ i)),
      D.e = e ∧ D.θ = latticeRealExt δ ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) ∧
      CFSG.IsQuasisimple D.orbitGroup ∧ Group.IsPerfect D.orbitGroup ∧
      D.orbitGroup ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ⁅rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _))⁆ ≤
        D.orbitGroup ∧
      ∀ x : adjointGroup τ L, (D.F x : ModGL τ L) = frobTwistGL τ L r e c x := by
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
  refine ⟨D, rfl, rfl, hDsimple, hqs, hperf, fun g hg => ?_, ?_, hF⟩
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

theorem exists_twoD_datum (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ componentRoots χ i, δ γ ∈ componentRoots χ i)
    (hpos : ∀ γ ∈ posRoots (componentRoots χ i), δ γ ∈ posRoots (componentRoots χ i))
    (hG : IsGraphTwist (componentRoots χ i) δ) {c : ModGL τ L}
    (hcT : c ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hcG : (adjointGroup τ L).map (MulAut.conj c).toMonoidHom = adjointGroup τ L)
    (hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e c) = rootSubgroup τ L (δ γ))
    (hpin : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e c (rootSL2 τ L β A) =
        rootSL2 τ L (δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A)) :
    ∃ D : GenFixedRootDatum τ r L (SpanQuot (componentRoots χ i)),
      D.e = e ∧ D.θ = latticeRealExt δ ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) ∧
      CFSG.IsQuasisimple D.orbitGroup ∧ Group.IsPerfect D.orbitGroup ∧
      D.orbitGroup ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ⁅rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _))⁆ ≤ D.orbitGroup := by
  obtain ⟨D, heD, hθD, hsimple, hqs, hperf, hle, hcomm, -⟩ :=
    exists_twoD_datum_pinned hτ he i δ hiso hmaps hpos hG hcT hcG hU hpin
  exact ⟨D, heD, hθD, hsimple, hqs, hperf, hle, hcomm⟩

end Datum

section Graph

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem exists_graphTwist_labelled
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ v ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      (∀ γ ∈ componentRoots (rootCharHom a) i,
        S.rhoTwist v γ ∈ componentRoots (rootCharHom a) i) ∧
      (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
        S.rhoTwist v γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
      IsGraphTwist (componentRoots (rootCharHom a) i) (S.rhoTwist v) ∧
      ∃ (m : ℕ) (_ : 5 ≤ m) (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m),
        CompsPTwoDLabel.IsForkLabelling (componentRoots (rootCharHom a) i) (S.rhoTwist v) ε := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨hni, hcard⟩ := S.twoD_factsT hT i hkind h5
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ := S.image_componentRoots_eq_of_five_leT hT i h5
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  have hρsΨ : ∀ γ ∈ Ψ, S.ρ.symm γ ∈ Ψ := fun γ hγ => by
    rw [← hst] at hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    rwa [Equiv.symm_apply_apply]
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ S.ρ.symm := by
    refine ⟨⟨hρsΨ, S.ρ.symm.injective.injOn, fun γ hγ => ⟨S.ρ γ, hρΨ γ hγ,
      S.ρ.symm_apply_apply γ⟩⟩, fun γ _ δ _ => ?_, fun γ _ => ?_⟩
    · have h := iform_rho S (S.ρ.symm γ) (S.ρ.symm δ)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    · apply S.ρ.injective
      rw [Equiv.apply_symm_apply, S.frob.neg_eq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hg := hf.comp_smul hΨ hu
  have hv : u⁻¹ ∈ componentWeylGroup Ψ := inv_mem hu
  have hδg : ∀ γ, S.rhoTwist u⁻¹ (S.ρ.symm (u • γ)) = γ := fun γ => by
    rw [S.rhoTwist_apply, Equiv.apply_symm_apply, inv_smul_smul]
  have hmaps : ∀ γ ∈ Ψ, S.rhoTwist u⁻¹ γ ∈ Ψ := fun γ hγ =>
    smul_mem_of_mem_componentWeylGroup hΨ hv _ (hρΨ γ hγ)
  have hposδ : ∀ γ ∈ posRoots Ψ, S.rhoTwist u⁻¹ γ ∈ posRoots Ψ := by
    intro γ hγ
    obtain ⟨b, hb, rfl⟩ := hg.exists_posRoots hΨ hpos hγ
    rw [hδg]
    exact hb
  have hiso := S.iform_rhoTwist u⁻¹
  have hinj := injective_of_iform _ hiso
  have hfδ : IsIsometry Ψ (S.rhoTwist u⁻¹) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ _ => hiso γ δ,
      fun γ _ => map_neg _ γ⟩
  have hne : ∃ β ∈ simpleRoots Ψ, S.rhoTwist u⁻¹ β ≠ β := by
    by_contra h
    push Not at h
    apply hni
    refine ⟨u, componentWeylGroup_le Ψ hu, fun γ hγ => ?_⟩
    have h1 := hfδ.eq_self_of_simpleRoots hΨ h hγ
    rw [S.rhoTwist_apply] at h1
    calc S.ρ γ = u • (u⁻¹ • S.ρ γ) := by rw [smul_inv_smul]
      _ = u • γ := by rw [h1]
  have hτ := simplyLaced_of_five_le_rank (le_trans h5 (compRank_le Ψ))
  have hsl : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  obtain ⟨m, hm, ε, hε⟩ := CompsPTwoDLabel.exists_labelling_twoD hΨ hsl h5 hcard _ hiso hmaps
    hposδ hne
  exact ⟨u⁻¹, hv, hmaps, hposδ,
    isGraphTwist_of_twoD hΨ hsl h5 hcard _ hiso hmaps hposδ hne, m, hm, ε, hε⟩


end Graph

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem exists_twoD_export_of_graph
    {r e : ℕ} [Fact r.Prime] [CharP L r]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hq : S.D.q = r ^ e) (he : 1 ≤ e)
    (hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (v : WeylGroup τ) (hv : v ∈ componentWeylGroup (componentRoots (rootCharHom a) i))
    (hmaps : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.rhoTwist v γ ∈ componentRoots (rootCharHom a) i)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      S.rhoTwist v γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hG : IsGraphTwist (componentRoots (rootCharHom a) i) (S.rhoTwist v)) :
    ∃ (z : ModGL τ L) (D : GenFixedRootDatum τ r L (SpanQuot (componentRoots (rootCharHom a) i))),
      D.e = e ∧ D.θ = latticeRealExt (S.rhoTwist v) ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj z⁻¹).toMonoidHom =
        D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots (rootCharHom a) i) :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ∧
      ∀ x : adjointGroup τ L,
        S.D.step (z * (x : ModGL τ L) * z⁻¹) = z * (D.F x : ModGL τ L) * z⁻¹ := by
  classical
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ), torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L :=
    fun T => sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
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
  obtain ⟨D, hDe, hDθ, hDs, hCqs, hCperf, hCle, hcomm, hDF⟩ :=
    exists_twoD_datum_pinned hτ (by omega : 1 ≤ e) i
    (S.rhoTwist v) hiso hmaps hpos hG hcT hcG hU hpin'
  set C : Subgroup (ModGL τ L) := D.orbitGroup with hCdef
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
  have hrr : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    have hmem : ∀ γ ∈ componentRoots (rootCharHom a) i,
        S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ =>
      hst.subset (Set.mem_image_of_mem _ hγ)
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
          rw [Function.iterate_succ_apply]
          exact ih _ (hmem δ hδ)
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
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
  refine ⟨z, D, hDe, hDθ, hRC, hDs, hzZ, ?_⟩
  intro x
  rw [hDF, hFc, map_mul, map_mul, map_inv, hz]
  group

theorem exists_twoD_export_pinned
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (r e m : ℕ) (_ : Fact r.Prime) (_ : CharP L r) (_ : 5 ≤ m) (z : ModGL τ L)
      (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m)
      (D : GenFixedRootDatum τ r L (SpanQuot (componentRoots (rootCharHom a) i))),
      S.D.q = r ^ e ∧ 1 ≤ e ∧ D.e = e ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj z⁻¹).toMonoidHom =
        D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots (rootCharHom a) i) :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      (∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) ∧
      (∀ j : Fin m, j.val + 2 < m →
        D.θ (toReal (ε.symm j : Fin τ.rank → ℤ)) = toReal (ε.symm j : Fin τ.rank → ℤ)) ∧
      (∀ a' b' : Fin m, a'.val + 2 = m → b'.val + 1 = m →
        D.θ (toReal (ε.symm a' : Fin τ.rank → ℤ)) = toReal (ε.symm b' : Fin τ.rank → ℤ) ∧
          D.θ (toReal (ε.symm b' : Fin τ.rank → ℤ)) = toReal (ε.symm a' : Fin τ.rank → ℤ)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ∧
      ∀ x : adjointGroup τ L,
        S.D.step (z * (x : ModGL τ L) * z⁻¹) = z * (D.F x : ModGL τ L) * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨v, hv, hmaps, hpos, hG, m, hm, ε, hε⟩ :=
    exists_graphTwist_labelled S hT i hkind h5
  obtain ⟨z, D, hDe, hDθ, hRC, hDs, hzZ, hF⟩ := exists_twoD_export_of_graph S hτ hT i hq he
    (S.image_componentRoots_eq_of_five_leT hT i h5) v hv hmaps hpos hG
  refine ⟨r, e, m, ⟨hr⟩, hchar, hm, z, ε, D, hq, he, hDe, hRC, hDs, hε.1,
    fun j hj => ?_, fun a' b' ha' hb' => ?_, hzZ, hF⟩
  · rw [hDθ, latticeRealExt_toReal, hε.2.1 j hj]
  · obtain ⟨h1, h2⟩ := hε.2.2 a' b' ha' hb'
    rw [hDθ, latticeRealExt_toReal, latticeRealExt_toReal, h1, h2]
    exact ⟨rfl, rfl⟩

theorem exists_twoD_export
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (r e m : ℕ) (_ : Fact r.Prime) (_ : CharP L r) (_ : 5 ≤ m) (z : ModGL τ L)
      (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m)
      (D : GenFixedRootDatum τ r L (SpanQuot (componentRoots (rootCharHom a) i))),
      S.D.q = r ^ e ∧ 1 ≤ e ∧ D.e = e ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj z⁻¹).toMonoidHom =
        D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots (rootCharHom a) i) :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      (∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD m (ε β) (ε γ)) ∧
      (∀ j : Fin m, j.val + 2 < m →
        D.θ (toReal (ε.symm j : Fin τ.rank → ℤ)) = toReal (ε.symm j : Fin τ.rank → ℤ)) ∧
      (∀ a' b' : Fin m, a'.val + 2 = m → b'.val + 1 = m →
        D.θ (toReal (ε.symm a' : Fin τ.rank → ℤ)) = toReal (ε.symm b' : Fin τ.rank → ℤ) ∧
          D.θ (toReal (ε.symm b' : Fin τ.rank → ℤ)) = toReal (ε.symm a' : Fin τ.rank → ℤ)) := by
  obtain ⟨r, e, m, hr, hchar, hm, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap, -, -⟩ :=
    exists_twoD_export_pinned S hτ hT i hkind h5
  exact ⟨r, e, m, hr, hchar, hm, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩


end Main

end CompsPTwoDExport

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
