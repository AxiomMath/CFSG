module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighPerfect
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement

set_option linter.unusedSectionVars false


section SpanChar

variable {τ : Tag}

abbrev SpanQuot (Ψ : Set (Fin τ.rank → ℤ)) : Type :=
  Multiplicative (Fin τ.rank → ℤ) ⧸ Subgroup.closure (Multiplicative.ofAdd '' Ψ)

@[expose] def spanChar (Ψ : Set (Fin τ.rank → ℤ)) :
    Multiplicative (Fin τ.rank → ℤ) →* SpanQuot Ψ :=
  QuotientGroup.mk' _

variable {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem iform_zero_right' (x : Fin τ.rank → ℤ) : iform x 0 = 0 := by
  have h := iform_smul_right 0 x 0
  rwa [zero_smul, zero_mul] at h

theorem kernelRoots_spanChar (i : KernelComponent χ) :
    kernelRoots (spanChar (componentRoots χ i)) = componentRoots χ i := by
  set Ψ := componentRoots χ i with hΨ
  ext γ
  constructor
  · rintro ⟨hγr, hγ1⟩
    have hmem : Multiplicative.ofAdd γ ∈ Subgroup.closure (Multiplicative.ofAdd '' Ψ) :=
      (QuotientGroup.eq_one_iff _).1 hγ1
    have hχ : Subgroup.closure (Multiplicative.ofAdd '' Ψ) ≤ χ.ker := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨β, ⟨hβk, -⟩, rfl⟩
      exact hβk.2
    have hγk : γ ∈ kernelRoots χ := ⟨hγr, hχ hmem⟩
    by_contra hγΨ
    have horth : ∀ β ∈ Ψ, iform γ β = 0 := by
      rintro β ⟨hβk, hβi⟩
      refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨β, hβk⟩) fun h => hγΨ ?_
      exact ⟨hγk, h.trans hβi⟩
    have hcl : ∀ m ∈ Subgroup.closure (Multiplicative.ofAdd '' Ψ),
        iform γ (Multiplicative.toAdd m) = 0 := by
      intro m hm
      induction hm using Subgroup.closure_induction with
      | mem m hm =>
        obtain ⟨β, hβ, rfl⟩ := hm
        exact horth β hβ
      | one => exact iform_zero_right' γ
      | mul m n _ _ hm hn => rw [toAdd_mul, iform_add_right, hm, hn, add_zero]
      | inv m _ hm =>
        rw [toAdd_inv, ← neg_one_smul ℤ (Multiplicative.toAdd m), iform_smul_right, hm,
          mul_zero]
    have h0 := hcl _ hmem
    have hpos := iform_self_pos_of_isRoot hγr
    simp only [toAdd_ofAdd] at h0
    omega
  · intro hγ
    exact ⟨hγ.1.1, (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_closure ⟨γ, hγ, rfl⟩)⟩

theorem componentRoots_spanChar (i : KernelComponent χ)
    (j : KernelComponent (spanChar (componentRoots χ i))) :
    componentRoots (spanChar (componentRoots χ i)) j = componentRoots χ i := by
  have hk := kernelRoots_spanChar i
  obtain ⟨α, rfl⟩ := Quotient.exists_rep j
  have hSΨ : componentRoots (spanChar (componentRoots χ i)) ⟦α⟧ ⊆ componentRoots χ i :=
    fun γ hγ => by
      rw [← hk]
      exact hγ.1
  have hαS : (α : Fin τ.rank → ℤ) ∈ componentRoots (spanChar (componentRoots χ i)) ⟦α⟧ :=
    ⟨α.2, rfl⟩
  have horth : ∀ γ ∈ componentRoots (spanChar (componentRoots χ i)) ⟦α⟧,
      ∀ β ∈ componentRoots χ i, β ∉ componentRoots (spanChar (componentRoots χ i)) ⟦α⟧ →
        iform γ β = 0 := by
    rintro γ ⟨hγk, hγj⟩ β hβ hβS
    have hβk : β ∈ kernelRoots (spanChar (componentRoots χ i)) := by rw [hk]; exact hβ
    refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨β, hβk⟩) fun h => hβS ?_
    exact ⟨hβk, h.symm.trans hγj⟩
  rcases (isRootComponent_componentRoots i).irreducible _ hSΨ horth with h | h
  · rw [h] at hαS
    exact absurd hαS (Set.notMem_empty _)
  · exact h

theorem unionRoots_spanChar (i : KernelComponent χ) :
    unionRoots (spanChar (componentRoots χ i)) Set.univ = componentRoots χ i := by
  ext γ
  constructor
  · rintro ⟨hγ, -⟩
    rwa [kernelRoots_spanChar i] at hγ
  · intro hγ
    have hγ' : γ ∈ kernelRoots (spanChar (componentRoots χ i)) := by
      rw [kernelRoots_spanChar i]
      exact hγ
    exact ⟨hγ', Set.mem_univ _⟩

theorem unionSimpleRoots_spanChar (i : KernelComponent χ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) :
    unionSimpleRoots (spanChar (componentRoots χ i)) Set.univ =
      (simpleRoots (componentRoots χ i) : Set (Fin τ.rank → ℤ)) := by
  have hα' : α ∈ kernelRoots (spanChar (componentRoots χ i)) := by
    rw [kernelRoots_spanChar i]
    exact hα
  ext β
  constructor
  · rintro ⟨j, -, hβ⟩
    rwa [componentRoots_spanChar i j] at hβ
  · intro hβ
    refine ⟨⟦⟨α, hα'⟩⟧, Set.mem_univ _, ?_⟩
    rw [componentRoots_spanChar i]
    exact hβ

end SpanChar

section Orbits

variable {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)}

theorem thetaOrbit_latticeRealExt (hG : IsGraphTwist Ψ δ) {α : Fin τ.rank → ℤ} (hα : α ∈ Ψ) :
    thetaOrbit (latticeRealExt δ) α = {α, δ α} := by
  have hit : ∀ m : ℕ, (δ : (Fin τ.rank → ℤ) → _)^[m] α ∈ ({α, δ α} : Set (Fin τ.rank → ℤ)) := by
    intro m
    induction m with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]
        exact Or.inr rfl
      · rw [Set.mem_singleton_iff] at h
        rw [h, hG.invol α hα]
        exact Or.inl rfl
  ext β
  constructor
  · rintro ⟨m, hm⟩
    rw [latticeRealExt_pow_toReal] at hm
    rw [← toReal_injective hm]
    exact hit m
  · rintro (rfl | rfl)
    · exact self_mem_thetaOrbit _ _
    · exact ⟨1, by rw [pow_one, latticeRealExt_toReal]⟩

theorem map_rootReflection_smul (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδγ : IsRoot τ (δ γ)) (x : Fin τ.rank → ℤ) :
    δ (rootReflection γ • x) = rootReflection (δ γ) • δ x := by
  rw [rootReflection_smul hγ, rootReflection_smul hδγ, map_sub, map_zsmul, corootPair,
    corootPair, hiso, hiso]

theorem smul_comm_of_mem_closure (hG : IsGraphTwist Ψ δ) (hΨ : IsRootComponent Ψ)
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y) (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ)
    {w : WeylGroup τ} (hw : w ∈ Subgroup.closure {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
      g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))}) (x : Fin τ.rank → ℤ) :
    w • δ x = δ (w • x) := by
  induction hw using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨β, hβ, rfl⟩ := hg
    have hβΨ := simpleRoots_subset hβ
    have hβr := hΨ.isRoot β hβΨ
    have hδβ := hΨ.isRoot _ (hmaps β hβΨ)
    by_cases hfix : δ β = β
    · rw [hfix, Set.pair_eq_singleton, setReflection_singleton]
      have h := map_rootReflection_smul hiso hβr hδβ x
      rw [hfix] at h
      exact h.symm
    · rw [setReflection_pair hβr hδβ (Ne.symm hfix) (hG.orth β hβΨ hfix), mul_smul, mul_smul]
      have h1 := map_rootReflection_smul hiso hβr hδβ x
      have h2 := map_rootReflection_smul hiso hδβ (by rw [hG.invol β hβΨ]; exact hβr)
        (rootReflection β • x)
      rw [hG.invol β hβΨ] at h2
      rw [← h1, ← h2]
      have hc := commute_rootReflection_of_iform_eq_zero hβr hδβ (hG.orth β hβΨ hfix)
      rw [← mul_smul, ← mul_smul, hc.eq]
  | one => simp
  | mul a b _ _ ha hb => rw [mul_smul, mul_smul, hb, ha]
  | inv a _ ha =>
    have h := ha (a⁻¹ • x)
    rw [smul_inv_smul] at h
    rw [← h, inv_smul_smul]

end Orbits

section Datum

variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_core (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
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
    ∃ C : Subgroup (ModGL τ L), CFSG.IsQuasisimple C ∧ Group.IsPerfect C ∧
      C ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ⁅rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _))⁆ ≤ C := by
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
  refine ⟨D.orbitGroup, hqs, hperf, fun g hg => ?_, ?_⟩
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

end Datum

end CFSG.HardMathSupport.Timmesfeld.LangTorus
