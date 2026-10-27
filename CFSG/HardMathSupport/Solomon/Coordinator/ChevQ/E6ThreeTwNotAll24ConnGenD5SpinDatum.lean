module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDExport
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Datum

variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_datum_fixed (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ}
    (he : 1 ≤ e)
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
      D.e = e ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) ∧
      Group.IsPerfect D.orbitGroup ∧
      D.torusJ = rootSpan τ L (componentRoots χ i) ⊓ torusGroup τ L ∧
      D.fixedGroup.map (adjointGroup τ L).subtype =
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) := by
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
  have hDtor : D.torusJ = rootSpan τ L Ψ ⊓ torusGroup τ L := by
    change unionTorus L (spanChar Ψ) Set.univ = _
    rw [unionTorus, unionRootSpan, hur]
  refine ⟨D, rfl, hDsimple, hperf, hDtor, ?_⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxS, hxF⟩ := D.mem_fixedGroup.1 hx
    refine ⟨by rwa [hDspan] at hxS, x.2, ?_⟩
    change frobTwistGL τ L r e c (x : ModGL τ L) = x
    have h := congrArg Subtype.val hxF
    rw [hF] at h
    exact h
  · rintro ⟨hgS, hgC, hgF⟩
    have hgF' : frobTwistGL τ L r e c g = g := hgF
    refine ⟨⟨g, hgC⟩, D.mem_fixedGroup.2 ⟨by rw [hDspan]; exact hgS, ?_⟩, rfl⟩
    apply Subtype.ext
    rw [hF]
    exact hgF'

end Datum

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
