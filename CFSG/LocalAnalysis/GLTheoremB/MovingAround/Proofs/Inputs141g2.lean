module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141g
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g

open CFSG.LocalAnalysis.GLTheoremB.MovingAround

section Datum

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement Pointwise


variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_core_two (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
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
        rootSL2 τ L (δ β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A))
    (hodd : ∀ t ∈ torusGroup τ L, ∃ N : ℕ, Odd N ∧ t ^ N = 1) :
    ∃ C : Subgroup (ModGL τ L), CFSG.IsQuasisimple C ∧
      C ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ∀ x ∈ rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        ∃ N : ℕ, Odd N ∧ x ^ N ∈ C := by
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
  have hmem : ∀ z ∈ rootSpan τ L Ψ ⊓
      (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
      ∃ z' : adjointGroup τ L, z' ∈ D.fixedGroup ∧ (z' : ModGL τ L) = z := by
    intro z hz
    refine ⟨⟨z, hz.2.1⟩, D.mem_fixedGroup.2 ⟨by rw [hDspan]; exact hz.1, ?_⟩, rfl⟩
    apply Subtype.ext
    rw [hF]
    exact hz.2.2
  refine ⟨D.orbitGroup, hqs, fun g hg => ?_, fun x hx => ?_⟩
  · have hgC := D.orbitGroup_le_adjointGroup hg
    refine ⟨?_, hgC, ?_⟩
    · have := D.orbitGroup_le_rootSpanJ hg
      rwa [hDspan] at this
    · change frobTwistGL τ L r e c g = g
      have h := congrArg Subtype.val (F_eq_self_of_mem_orbitGroup D hg)
      rw [hF] at h
      exact h
  ·
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    have hdec : x' ∈ (D.fixedTorus : Set (adjointGroup τ L)) *
        (D.orbitGroupC : Set (adjointGroup τ L)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact hx'
    obtain ⟨t, ht, c', hc', htc⟩ := hdec
    obtain ⟨N, hN, htN⟩ := hodd (t : ModGL τ L)
      (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ht).1)
    have htN1 : t ^ N = 1 := Subtype.ext (by simpa using htN)
    have htnorm : t ∈ Subgroup.normalizer (D.orbitGroupC : Set (adjointGroup τ L)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => D.conj_mem_orbitGroupC_of_mem_fixedTorus ht hy, fun hy => ?_⟩
      have h1 := D.conj_mem_orbitGroupC_of_mem_fixedTorus (inv_mem ht) hy
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e] at h1
    have htc' : t * c' = x' := htc
    have h1 := Inputs141e.mul_pow_mem_of_mem_normalizer htnorm hc' N
    rw [htN1, inv_one, one_mul, htc'] at h1
    refine ⟨N, hN, ?_⟩
    have h2 := D.coe_mem_orbitGroup_of_mem_orbitGroupC h1
    simpa using h2

end Datum

section TwoDHigh

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement


theorem ratTwo_shape_twoDHigh
    {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ⁅Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (Inputs141f.ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have := hchar
  have hoddT : ∀ t ∈ torusGroup τ (AlgebraicClosure K), ∃ N : ℕ, Odd N ∧ t ^ N = 1 := by
    intro t ht
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨N, hN, hlN⟩ := Inputs141e.exists_odd_pow_eq_one hK2 l
    exact ⟨N, hN,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hlN⟩
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ), torusGroup τ (AlgebraicClosure K) ⊔
      rootSpan τ (AlgebraicClosure K) T ≤ adjointGroup τ (AlgebraicClosure K) :=
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
  have hyC : y ∈ adjointGroup τ (AlgebraicClosure K) := hSC _ hyZ
  have hFc : ∀ g, frobTwistGL τ (AlgebraicClosure K) r e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer
      (torusGroup τ (AlgebraicClosure K) : Set (ModGL τ (AlgebraicClosure K))) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ (AlgebraicClosure K)).map (MulAut.conj (y * Q)).toMonoidHom =
      adjointGroup τ (AlgebraicClosure K) := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ (AlgebraicClosure K) ⟨y, hyM⟩ = v := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (rootSubgroup τ (AlgebraicClosure K) γ).map (frobTwistGL τ (AlgebraicClosure K) r e (y * Q)) =
        rootSubgroup τ (AlgebraicClosure K) (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ (AlgebraicClosure K) r e (y * Q) =
        (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots (componentRoots (rootCharHom a) i), ∀ A : SL2 (AlgebraicClosure K),
      frobTwistGL τ (AlgebraicClosure K) r e (y * Q) (rootSL2 τ (AlgebraicClosure K) β A) =
        rootSL2 τ (AlgebraicClosure K) (S.rhoTwist v β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius (AlgebraicClosure K) r e) A) :=
    fun β hβ A => by rw [hFc]; exact hpin β hβ A
  obtain ⟨C, hCqs, hCle, hCodd⟩ := exists_twoD_core_two hτ (by omega : 1 ≤ e) i
    (S.rhoTwist v) hiso hmaps hpos hG hcT hcG hU hpin' hoddT
  have hyZ' : y ∈ torusGroup τ (AlgebraicClosure K) ⊔
      rootSpan τ (AlgebraicClosure K) (kernelRoots (rootCharHom a)) :=
    (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
  obtain ⟨z, hzZ, hz⟩ := S.exists_lang_twoDT he hQT hstep hT hyZ'
  have hzC : z ∈ adjointGroup τ (AlgebraicClosure K) := hSC _ hzZ
  have hzN := mem_normalizer_rootSpan_of_mem_Z hzZ i
  have hstepz : ∀ g, frobTwistGL τ (AlgebraicClosure K) r e (y * Q) (z⁻¹ * g * z) =
      z⁻¹ * S.D.step g * z := by
    intro g
    rw [hFc, map_mul, map_mul, map_inv, hz]
    group
  have hs1 := S.componentOrbitLength_eq_one_of_five_leT hT i h5
  have hCM : ∀ c ∈ C, z * c * z⁻¹ ∈ S.D.model := by
    intro c hc
    have hcM := (hCle hc).2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzC (Subgroup.mem_inf.1 hcM).1)
      (Subgroup.inv_mem _ hzC), ?_⟩
    have h1 := hstepz (z * c * z⁻¹)
    have e2 : z⁻¹ * (z * c * z⁻¹) * z = c := by group
    rw [e2] at h1
    have hcF : frobTwistGL τ (AlgebraicClosure K) r e (y * Q) c = c := (Subgroup.mem_inf.1 hcM).2
    rw [hcF] at h1
    change S.D.step (z * c * z⁻¹) = z * c * z⁻¹
    calc S.D.step (z * c * z⁻¹) = z * (z⁻¹ * S.D.step (z * c * z⁻¹) * z) * z⁻¹ := by group
      _ = z * c * z⁻¹ := by rw [← h1]
  haveI : Finite S.D.model := S.finite
  haveI : Finite ↥C := Finite.of_injective (fun c : C => (⟨z * c * z⁻¹, hCM c c.2⟩ : S.D.model))
    (fun c d hcd => by
      have h1 := congrArg Subtype.val hcd
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1)))
  let θ : C →* ModGL τ (AlgebraicClosure K) := (MulAut.conj z).toMonoidHom.comp C.subtype
  have hθ : ∀ c : C, θ c = z * c * z⁻¹ := fun c => rfl
  refine ratTwo_shape_of_hom S hK2 hp hp2 hT i θ (fun c => ?_) (fun c => ?_) (fun g hg hgF => ?_)
    (Or.inl hCqs)
  · rw [hθ]
    exact (Subgroup.mem_normalizer_iff.1 hzN _).1 (hCle c.2).1
  · rw [hs1, hθ]
    exact (hCM c c.2).2
  · rw [hs1] at hgF
    have hgF' : S.D.step g = g := hgF
    have hx : z⁻¹ * g * z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ⊓
        (adjointGroup τ (AlgebraicClosure K) ⊓
          (frobTwistGL τ (AlgebraicClosure K) r e (y * Q)).eqLocus (MonoidHom.id _)) := by
      have hxS : z⁻¹ * g * z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hzN) g).1 hg
        rwa [inv_inv] at h1
      refine ⟨hxS, rootSpan_le_adjointGroup _ _ hxS, ?_⟩
      change frobTwistGL τ (AlgebraicClosure K) r e (y * Q) (z⁻¹ * g * z) = z⁻¹ * g * z
      rw [hstepz, hgF']
    obtain ⟨N, hN, hxN⟩ := hCodd _ hx
    refine ⟨N, hN, ⟨⟨_, hxN⟩, ?_⟩⟩
    rw [hθ]
    show z * (z⁻¹ * g * z) ^ N * z⁻¹ = g ^ N
    rw [← conj_pow]
    congr 1
    group

end TwoDHigh

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem tag_simplyLaced_of_five_le_rank {τ : Tag} (h : 5 ≤ τ.rank) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  cases τ with
  | G2 => exact absurd h (by decide)
  | F4 => exact absurd h (by decide)
  | D4 => exact Or.inl rfl
  | E6 => exact Or.inr (Or.inl rfl)
  | E7 => exact Or.inr (Or.inr (Or.inl rfl))
  | E8 => exact Or.inr (Or.inr (Or.inr rfl))

theorem langOuterTwo_holds :
    Inputs141f.LangOuterTwo := by
  intro τ K _ _ hK2 p₀ S p hp hp5 a hT hap h1 i hkind
  have hp2 : p ≠ 2 := by omega
  have hTp : rootDiagUnit τ a ^ p = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact absurd hk hkind
  | suN =>
    obtain ⟨h2, hn⟩ := suN_rank_ncard hk
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
    exact ratTwo_shape_suN S hK2 hp hp5 hT i hk hν hψ hκ hnorm hΨ
  | twoD =>
    obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hτ := tag_simplyLaced_of_five_le_rank
        (h5.trans (compRank_le_rank (componentRoots (rootCharHom a) i)))
      exact ratTwo_shape_twoDHigh S hK2 hp hp2 hτ hT i hk h5
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, hr]
      obtain ⟨hρ, hfin, hqs⟩ := layer_d4class S hp hpL hT hTp h1 i hr hc hnin
      exact ratTwo_shape_of_layer S hK2 hp hp2 hT i hρ hfin hqs
  | exc =>
    obtain ⟨hnin, hA | ⟨hr, hc, -⟩⟩ := exc_kind hk
    · obtain ⟨hρ, hfin, hqs⟩ := layer_e6class S hp hpL hT hTp h1 i hA.1 hA.2
      exact ratTwo_shape_of_layer S hK2 hp hp2 hT i hρ hfin hqs
    · obtain ⟨hρ, hfin, hqs⟩ := layer_d4class S hp hpL hT hTp h1 i hr hc hnin
      exact ratTwo_shape_of_layer S hK2 hp hp2 hT i hρ hfin hqs

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g

end
