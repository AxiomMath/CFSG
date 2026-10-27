module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

set_option linter.unusedSectionVars false

private def ElemPerfJ (ℓ : ℕ) (C : Type) [Group C] : Prop :=
  ∀ c : C, (∃ n : ℕ, c ^ ℓ ^ n = 1) → ∃ P : Subgroup C, ⁅P, P⁆ = P ∧ c ∈ P

private theorem elemPerfJ_of_mulEquiv {ℓ : ℕ} {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (h : ElemPerfJ ℓ C') : ElemPerfJ ℓ C := by
  intro c ⟨n, hn⟩
  obtain ⟨P, hP, hcP⟩ := h (e c) ⟨n, by rw [← map_pow, hn, map_one]⟩
  exact ⟨P.map e.symm.toMonoidHom, by rw [← Subgroup.map_commutator, hP], ⟨e c, hcP, by simp⟩⟩

private theorem qPerf_of_elemPerfJ {ℓ : ℕ} {S : Type} [Group S] {β : MulAut S}
    (h : ElemPerfJ ℓ ↥(fixSubgroup β)) : Inputs256f.QPerf ℓ β := by
  intro s hs ⟨n, hn⟩
  obtain ⟨P, hP, hsP⟩ := h ⟨s, mem_fixSubgroup.2 hs⟩ ⟨n, Subtype.ext (by simp [hn])⟩
  exact ⟨P.map (fixSubgroup β).subtype, Subgroup.map_subtype_le P,
    by rw [← Subgroup.map_commutator, hP], ⟨_, hsP, rfl⟩⟩

private theorem elemPerfJ_of_conj_eq {q : ℕ} {Y : Type} [Group Y] (y : Y) {φ ψ : MulAut Y}
    (h : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ) (hψ : ElemPerfJ q ↥(fixSubgroup ψ)) :
    ElemPerfJ q ↥(fixSubgroup φ) := by
  rw [← h] at hψ
  exact elemPerfJ_of_mulEquiv
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv (MulAut.conj y) φ) hψ

private theorem elemPerfJ_inv_iff {q : ℕ} {Y : Type} [Group Y] (φ : MulAut Y) :
    ElemPerfJ q ↥(fixSubgroup φ⁻¹) ↔ ElemPerfJ q ↥(fixSubgroup φ) :=
  ⟨fun h => elemPerfJ_of_mulEquiv (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq φ)).symm h,
    fun h => elemPerfJ_of_mulEquiv (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq φ)) h⟩

section SL3

open scoped MatrixGroups

private theorem sl3_hom_charElemJ {F : Type} [Field F] [Finite F] {C : Type} [Group C] [Finite C]
    (ρ : SL(3, F) →* C) (hρ : ∃ g, ρ g ≠ 1) (hcard : Nat.card C = Nat.card SL(3, F))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) :
    ρ.ker ≤ Subgroup.center SL(3, F) ∧ Nat.Coprime (Nat.card ρ.ker) ℓ ∧
      ⁅ρ.range, ρ.range⁆ = ρ.range ∧ ∀ (c : C) (n : ℕ), c ^ ℓ ^ n = 1 → c ∈ ρ.range := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hquasi' : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hquasi : CFSG.Open.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hquasi'
  have hker : ρ.ker ≤ Subgroup.center SL(3, F) := by
    obtain ⟨g, hg⟩ := hρ
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi ρ.ker with
      h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top g : g ∈ ρ.ker) hg
  have hkercard : Nat.card ρ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hker).trans CFSG.DesarguesianPlanes.card_center_SL3_le
  have hrange : Nat.card ρ.range * Nat.card ρ.ker = Nat.card (SL(3, F)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  have hidx : ρ.range.index * Nat.card ρ.range = Nat.card C := ρ.range.index_mul_card
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have h1 : ρ.range.index * Nat.card ρ.range ≤ 3 * Nat.card ρ.range := by
    rw [hidx, hcard, ← hrange]
    nlinarith
  have hidx3 : ρ.range.index ≤ 3 := Nat.le_of_mul_le_mul_right h1 hpos
  have hidx0 : ρ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  haveI hperf : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  obtain ⟨hN, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.normal_and_solvable_of_perfect_index_le_four hperf
      (by omega) hidx0
  have hcop : ∀ m : ℕ, 0 < m → m ≤ 3 → Nat.Coprime m ℓ := fun m hm0 hm3 =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun h => by
      have := Nat.le_of_dvd hm0 h
      omega)
  refine ⟨hker, hcop _ Nat.card_pos hkercard, Subgroup.isPerfect_iff.1 hperf, fun c n hc => ?_⟩
  exact mem_of_charPow_of_coprime_pow_mem hc (hcop _ (Nat.pos_of_ne_zero hidx0) hidx3)
    (Subgroup.pow_index_mem ρ.range c)

end SL3



section TwoDHigh

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.RankThree.Lattice
open scoped commutatorElement

section Core

open scoped Pointwise

variable {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]

theorem exists_twoD_core_charElem (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
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
    (htor : ∀ t ∈ torusGroup τ L, ∃ N : ℕ, Nat.Coprime N r ∧ t ^ N = 1) :
    ∃ C : Subgroup (ModGL τ L), ⁅C, C⁆ = C ∧
      C ≤ rootSpan τ L (componentRoots χ i) ⊓
        (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots χ i) ⊓
          (adjointGroup τ L ⊓ (frobTwistGL τ L r e c).eqLocus (MonoidHom.id _)),
        (∃ n : ℕ, g ^ r ^ n = 1) → g ∈ C := by
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
  refine ⟨D.orbitGroup, Subgroup.isPerfect_iff.1 hperf, fun g hg => ?_, ?_⟩
  · have hgC := D.orbitGroup_le_adjointGroup hg
    refine ⟨?_, hgC, ?_⟩
    · have := D.orbitGroup_le_rootSpanJ hg
      rwa [hDspan] at this
    · change frobTwistGL τ L r e c g = g
      have h := congrArg Subtype.val (F_eq_self_of_mem_orbitGroup D hg)
      rw [hF] at h
      exact h
  ·
    intro g hg ⟨n, hn⟩
    have hg' : (⟨g, hg.2.1⟩ : adjointGroup τ L) ∈ D.fixedGroup := by
      refine D.mem_fixedGroup.2 ⟨by rw [hDspan]; exact hg.1, ?_⟩
      apply Subtype.ext
      rw [hF]
      exact hg.2.2
    have hdec : (⟨g, hg.2.1⟩ : adjointGroup τ L) ∈ (D.fixedTorus : Set (adjointGroup τ L)) *
        (D.orbitGroupC : Set (adjointGroup τ L)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact hg'
    obtain ⟨t, ht, x, hx, htx⟩ := hdec
    have htx' : t * x = ⟨g, hg.2.1⟩ := htx
    have htN : t ∈ Subgroup.normalizer (D.orbitGroupC : Set (adjointGroup τ L)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => D.conj_mem_orbitGroupC_of_mem_fixedTorus ht hy, fun hy => ?_⟩
      have h1 := D.conj_mem_orbitGroupC_of_mem_fixedTorus (inv_mem ht) hy
      have e1 : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e1] at h1
    obtain ⟨N, hN, htN'⟩ := htor (t : ModGL τ L) (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ht).1)
    have htN1 : t ^ N = 1 := Subtype.ext (by simpa using htN')
    have hgn : (t * x) ^ r ^ n = 1 := by
      rw [htx']
      exact Subtype.ext (by simpa using hn)
    have hmem := mem_of_charElem_of_mul htN htN1 hN hx hgn
    rw [htx'] at hmem
    exact D.coe_mem_orbitGroup_of_mem_orbitGroupC hmem

end Core

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem exists_perfect_orbit_twoD_high (hLℓ : ringChar L = ℓ)
    (htorL : ∀ t ∈ torusGroup τ L, ∃ N : ℕ, Nat.Coprime N ℓ ∧ t ^ N = 1)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ P : Subgroup (ModGL τ L),
      P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model ∧
      ⁅P, P⁆ = P ∧
      ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
        (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have := hchar
  have hrℓ : r = ℓ := by
    rw [← hLℓ]
    exact (ringChar.eq L r).symm
  have htor : ∀ t ∈ torusGroup τ L, ∃ N : ℕ, Nat.Coprime N r ∧ t ^ N = 1 := by
    rw [hrℓ]
    exact htorL
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
  obtain ⟨C, hCperf, hCle, hCq⟩ := exists_twoD_core_charElem hτ (by omega : 1 ≤ e) i
    (S.rhoTwist v) hiso hmaps hpos hG hcT hcG hU hpin' htor
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
  have hPapp : ∀ x, (MulAut.conj z).toMonoidHom x = z * x * z⁻¹ := fun x => rfl
  refine ⟨C.map (MulAut.conj z).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hPapp, hrr]
    have hxS : x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := (hCle hx).1
    have hxM : x ∈ M' := (hCle hx).2
    refine ⟨(Subgroup.mem_normalizer_iff.1 hzN x).1 hxS, ?_⟩
    rw [← hMap] at hxM
    obtain ⟨y, hy, hyx⟩ := hxM
    rw [hφapp] at hyx
    rw [← hyx]
    have e1 : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
    rw [e1]
    exact hy
  · rw [← Subgroup.map_commutator, hCperf]
  · intro g hgA hgM hgn
    rw [hrr] at hgA
    have hφg : φ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ M' := by
      refine ⟨?_, ?_⟩
      · rw [← hspan]
        exact ⟨g, hgA, rfl⟩
      · rw [← hMap]
        exact ⟨g, hgM, rfl⟩
    obtain ⟨n, hn⟩ := hgn
    have hφgn : φ g ^ r ^ n = 1 := by rw [← map_pow, hrℓ, hn, map_one]
    refine ⟨φ g, hCq _ hφg ⟨n, hφgn⟩, ?_⟩
    rw [hPapp, hφapp]
    group

end TwoDHigh

section Layers

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep D4TrialityLayer
  d4Nodes)

open scoped Matrix

theorem orbitCharElemPerfect_of_layer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {ℓ₀ : ℕ} {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  have horbit : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (hρ δ hδ)
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  refine ⟨rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model, le_rfl, ?_,
    fun g hgA hgM _ => ⟨hgA, hgM⟩⟩
  rw [horbit]
  exact Inputs256f.commutator_self_of_perfect (Group.isPerfect_def.1 hqs.1)

section Standard

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem orbitCharElemPerfect_of_d4_outer [E6Sub τ] {ℓ₀ : ℕ} (hsearch : D4BaseSearch τ)
    (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2
  exact orbitCharElemPerfect_of_layer S i hρ hlayer

theorem orbitCharElemPerfect_of_d4 [E6Sub τ] {ℓ₀ : ℕ} (hsearch : D4BaseSearch τ)
    (hL : D4TrialityLayer τ) (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  rw [componentOrbitLength_eq_one hfin hρ, mul_one] at h2
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : π * π ≠ 1 := by
    intro hππ
    apply h2
    have hu' : w₀ * u * w₀⁻¹ ∈ parabolicWeylGroup τ (d4Nodes τ) := by
      have hle : (parabolicWeylGroup τ (d4Nodes τ)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup τ (d4Nodes τ) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, ?_⟩
        change simple τ (π j) = w₀ * simple τ j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨u, hu, rfl⟩
    refine ⟨v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹,
      hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu hu'), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    have hγr : IsRoot τ (v • α) := hγ.1.1
    have hw2 : w₀ • w₀ • α = α := by
      have hα' : w₀ • α ∈ parabolicRoots τ (d4Nodes τ) := by
        rw [hlin0 α hα]
        refine ⟨?_, fun k hk => ?_⟩
        · rw [← hlin0 α hα]
          exact IsRoot.smul hα.1 w₀
        · have hk' : π.symm k ∉ d4Nodes τ := fun h => hk (by
            have h' := hπ.mem_d4Set (show π.symm k ∈ d4Set τ from h)
            rw [Equiv.apply_symm_apply] at h'
            exact h')
          exact hα.2 _ hk'
      rw [hlin0 _ hα', hlin0 α hα, ← permLattice_mul, hππ]
      rfl
    rw [Function.iterate_succ_apply, Function.iterate_one, hρw _ hγr,
      hρw _ ((isRoot_smul_iff w).2 hγr)]
    calc w • w • v • α = v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
          simp only [mul_smul, smul_inv_smul]
      _ = v • (u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
      _ = v • (u • (w₀ * u * w₀⁻¹) • w₀ • w₀ • α) := by simp only [mul_smul, inv_smul_smul]
      _ = (v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹) • v • α := by
          rw [hw2]
          simp only [mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ.eq_cycle hπ1 hπ2 with rfl | rfl
    · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2
  exact orbitCharElemPerfect_of_layer S i hρ hlayer

end Standard

theorem orbitCharElemPerfect_of_d4_twE6_of_layer {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p) {ℓ₀ : ℕ}
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
      u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      IsD4LeafPerm π → π ≠ 1 → (¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) →
      πJ * πJ ≠ 1 := by
    intro hnin2 h2
    apply hnin2
    have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
        exact (e6WeylTwist_simple j).symm
      exact hle ⟨u, hu, rfl⟩
    have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨e6WeylTwist u, hδu, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
    refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
        (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
      intro x hx
      rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
        inv_smul_smul]
    set β := u • permLattice πJ α with hβ
    have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
      rw [hβ, ← hθ' α hα]
      exact hθmem α hα
    have e1 : S.ρ (v • α) = v • β := by
      rw [hβ, ← hθ' α hα, smul_inv_smul]
    have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
      rw [← hθ' β hβJ, smul_inv_smul]
    have e3 : permLattice πJ (permLattice πJ α) = α := by
      rw [← permLattice_mul, h2]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer := hlay ℓ f hf _ hn'M u hu πJ hπJleaf hπ1 hπ2 hact
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
      ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    have e : Q ≃* Q.map (MulAut.conj nv).toMonoidHom :=
      Q.equivMapOfInjective _ (MulAut.conj nv).injective
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer
  exact orbitCharElemPerfect_of_layer S i hρ hqs

theorem orbitCharElemPerfect_of_d4_twE6 (hE6 : E6FixDNAll) {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p) {ℓ₀ : ℕ}
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    OrbitCharElemPerfect S ℓ₀ a i :=
  orbitCharElemPerfect_of_d4_twE6_of_layer S hS i v hΨ hρ hnin
    fun ℓ f _ _ hf n hn u hu π hleaf hπ1 _ hact => by
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2

theorem orbitCharElemPerfect_twE6_triality {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {ℓ₀ : ℕ}
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hnin2 : ¬ twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  refine orbitCharElemPerfect_of_d4_twE6_of_layer S hS i v hΨ hρ hnin
    (fun ℓ f _ _ hf n hn u hu π hleaf hπ1 hπ2 hact => ?_)
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  rcases hleaf.eq_cycle hπ1 (hπ2 hnin2) with hc | hc
  · rw [hc] at hact
    exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2
  · rw [hc] at hact
    exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2

theorem orbitCharElemPerfect_e6T {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type}
    [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {ℓ₀ : ℕ} {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have h6 : 6 ≤ τ.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    rcases hτ.isE7E8 with rfl | rfl
    · refine S.rho_mem_componentRootsT haT i v hΨ (N := 0) (fun s hs => ?_)
        ⟨({Pi.single 0 1} : Finset (Fin Tag.E7.rank → ℤ)), fun α hα => ?_, by simp⟩
      · have := card_le_of_orth_e6 h6 [] (fun l hl h => absurd h (orth_e6_E7 l hl)) s hs
        simpa using this
      · rw [Finset.mem_singleton.1 hα]
        exact single_mem_parabolicRoots_e6 _ (by decide)
    · refine S.rho_mem_componentRootsT haT i v hΨ (N := 6) (fun s hs => ?_)
        ⟨({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
          Pi.single 5 1, Pi.single 0 1 + Pi.single 2 1} : Finset (Fin Tag.E8.rank → ℤ)),
          fun α hα => ?_, by decide⟩
      · exact (card_le_of_orth_e6 h6 _ orth_e6_E8 s hs).trans (by decide)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide), fun j hj => ?_⟩
          have key : ∀ j : Fin 8, ¬ (j.val ≤ 5) →
              ((Pi.single 0 1 + Pi.single 2 1 : Fin 8 → ℤ)) j = 0 := by decide
          exact key j hj
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  have hw' := hw
  rw [hΨ] at hw'
  obtain ⟨-, hqs⟩ := rootSpan_inf_model_quasisimple hτ' S hn v hw'
  exact orbitCharElemPerfect_of_layer S i hρ (by rw [hΨ]; exact hqs)

theorem orbitCharElemPerfect_rank_four (hE6 : E6FixDNAll) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) {ℓ₀ : ℕ} (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact orbitCharElemPerfect_of_d4_outer d4Base_E6 d4TrialityLayer_E6
        (d4SwapLayer_E6 hE6) S hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v
        hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      exact orbitCharElemPerfect_of_d4_twE6 hE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact orbitCharElemPerfect_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact orbitCharElemPerfect_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6) S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin

theorem orbitCharElemPerfect_exc {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) {ℓ₀ : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .exc) :
    OrbitCharElemPerfect S ℓ₀ a i := by
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    obtain ⟨-, hA | ⟨hr, -, -⟩⟩ := exc_kind hk
    · rw [hA.1] at hle
      exact absurd hle (by decide)
    · rw [hr] at hle
      exact absurd hle (by decide)
  | F4 =>
    obtain ⟨-, hA | ⟨hr, hc, -⟩⟩ := exc_kind hk
    · have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
      rw [hA.1] at hle
      exact absurd hle (by decide)
    · obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
      obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
      exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 =>
    obtain ⟨-, hA | ⟨-, hc, -⟩⟩ := exc_kind hk
    · have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
      rw [hA.1] at hle
      exact absurd hle (by decide)
    · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
    · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hA.2]; rfl)) ha1
    · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
        (by decide)
        (fun y hy => far_d4_E6 y fun z hz => by
          have h := hy z hz
          rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
        ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) haT hTp i hr hc
      have hfin : (componentRoots (rootCharHom a) i).Finite :=
        (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
      have hs := componentOrbitLength_eq_one hfin hρ
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
      rcases hP with rfl | ⟨t, ht, rfl⟩
      · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
          ext1 g
          rw [hΦ, one_mul, inv_one, mul_one]
        exact orbitCharElemPerfect_of_d4 d4Base_E6 d4TrialityLayer_E6 S hFr hΦ' hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hnin2
      · rw [hs, Function.iterate_one] at hnin
        rw [hs, mul_one] at hnin2
        exact orbitCharElemPerfect_twE6_triality S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin hnin2
  | E7 =>
    obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
    · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
        (by decide) hTp i hA.1 hA.2
      exact orbitCharElemPerfect_e6T S haT i v hv
    · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
        (by decide)
        (fun y hy => far_d4_E7 y fun z hz => by
          have h := hy z hz
          rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
        ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) haT hTp i hr hc
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
      obtain ⟨w, hn⟩ := S.D.n_weyl
      exact orbitCharElemPerfect_of_d4 d4Base_E7
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2
  | E8 =>
    obtain ⟨hnin, hA | ⟨hr, hc, hnin2⟩⟩ := exc_kind hk
    · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
        (by decide) hTp i hA.1 hA.2
      exact orbitCharElemPerfect_e6T S haT i v hv
    · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
        (by decide)
        (fun y hy => far_d4_E8 y fun z hz => by
          have h := hy z hz
          rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
        ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) haT hTp i hr hc
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
      obtain ⟨w, hn⟩ := S.D.n_weyl
      exact orbitCharElemPerfect_of_d4 d4Base_E8
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2

end Layers

section Outer

open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem langOuterCharElem_holds : LangOuterCharElem := by
  intro τ K _ _ h5 p₀ S p hp a hT hap h1 i hkind
  classical
  have hℓ : (ringChar K).Prime := by
    haveI : Fintype K := Fintype.ofFinite K
    exact (FiniteField.card K (ringChar K)).choose_spec.1
  have hLℓ : ringChar (AlgebraicClosure K) = ringChar K :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure K
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hkind with hk | hk
  · obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
    by_cases h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hr := le_trans h5' (compRank_le_rank (componentRoots (rootCharHom a) i))
      have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        cases τ <;> simp_all [Tag.rank]
      refine exists_perfect_orbit_twoD_high S hLℓ (fun t ht => ?_) hτ hT i hk h5'
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      obtain ⟨N, hN, hlN⟩ := exists_coprime_pow_eq_one_algClosure hℓ rfl l
      exact ⟨N, hN, rootDiagUnit_pow_eq_one_of_forall hlN⟩
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
        rw [hcard, hr]
      exact orbitCharElemPerfect_rank_four e6FixDNAll_proved S hp hpL hT hTp h1 i hr hc hnin
  · exact orbitCharElemPerfect_exc S hp hpL hT hTp h1 i hk

end Outer

theorem excRationalLieTypesP_charQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcRationalLieTypesP p :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.excRationalLieTypesP_of_residuals hp hp2
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.excRationalLieTypesOuterDP_proved hp)
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.excRationalLieTypesF4P_of_small hp hp2
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.excRationalLieTypesF4SmallP_holds hp hp2))

theorem qGenExcInndiag_of_outer (hout : LangOuterCharElem) : Inputs256f.QGenExcInndiag := by
  intro τ hτ K _ _ h5 p hp hp2 hpK α b j hj hα hp1 hh1
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have hqK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hpK' : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hpK ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have h4 : 4 ≤ Nat.card K := by
    rw [hqK]
    calc 4 ≤ ringChar K := by omega
      _ = ringChar K ^ 1 := (pow_one _).symm
      _ ≤ ringChar K ^ (f : ℕ) := Nat.pow_le_pow_right hℓ.pos f.pos
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h | h
    · subst h
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (by omega)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h])
  have hh : rootDiagUnit τ b * j ∈ CFSG.StandardType.RecipeExcLang.inndiagGroup τ K := ⟨b, j, hj, rfl⟩
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK' (Or.inr h4) hmon hperf α (rootDiagUnit τ b * j)
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hα hp1 hh1
  exact qGen_of_langSetup_charElem S hout hp (excRationalLieTypesP_charQ hp hp2) rfl hℓ h5 hpK ι hinj hrange α
    hconj hT hap h1 (langSetup_hTame S hT hap h1)

theorem qGenTwE6Inndiag_of_outer (hout : LangOuterCharElem) : Inputs256f.QGenTwE6Inndiag := by
  intro ℓ f hℓ h5 hf K _ _ hK σ hσ p hp hp2 hpℓ h hp1 hh1
  classical
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀ hmon
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hKℓ : ringChar K = ℓ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 2) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  exact qGen_of_langSetup_charElem S hout hp (excRationalLieTypesP_charQ hp hp2) hKℓ hℓ h5 hpℓ ι hinj hrange _
    hconj hT hap h1 (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ) (fun h => absurd h (by decide)) hT hap h1)

theorem qGen_triD4_inner_of_outer (hout : LangOuterCharElem) {ℓ f : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (Fr : K ≃+* K)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)) (hφ : orderOf φ = p)
    (hin : φ ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)).range) :
    Inputs256e.QGen ℓ φ := by
  classical
  obtain ⟨x, rfl⟩ := hin
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hxp : x ^ p = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, ← hφ, pow_orderOf_eq_one, map_one])
  have hx1 : x ≠ 1 := fun h' => by
    rw [h', map_one, orderOf_one] at hφ
    exact hp.one_lt.ne' hφ.symm
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ hf hK Fr hFr hp hpℓ hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hKℓ : ringChar K = ℓ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 3) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  exact qGen_of_langSetup_charElem S hout hp (excRationalLieTypesP_charQ hp hp2) hKℓ hℓ h5 hpℓ ι hinj hrange _
    hconj hT hap h1 (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ) (fun h => absurd h (by decide)) hT hap h1)

section Unitary

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.SP
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 renaming fixSub → fixSubO
open scoped MatrixGroups

private theorem unitary_core_elemPerfJ {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (hq5 : 5 ≤ p ^ f) {K : Type} [Field K] [Finite K] [CharP K p] {σ ε : K ≃+* K}
    (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3) (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) {b : Kˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    ElemPerfJ p ↥(foldFix ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ : MulAut
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓
      foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3 : (3 ^ f) % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    omega
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set q := p ^ f with hqdef
  set q₄ := q ^ 4 with hq₄def
  have hq2 : 2 ≤ q := by omega
  have hq4two : 2 ≤ q₄ := by
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmod : q₄ % 3 = 1 := by rw [hq₄def, Nat.pow_mod, hq]
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hb3' : (b : K) ^ 3 = 1 := by
    have := congrArg Units.val hb3
    simpa using this
  have hbσ : Units.map σ.toRingHom.toMonoidHom b = b := by
    apply Units.ext
    show σ (b : K) = b
    rw [hσ]
    obtain ⟨k, hk⟩ : ∃ k, q₄ = 3 * k + 1 := ⟨q₄ / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hb3', one_pow, one_mul]
  have hεb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹ := by
    apply Units.ext
    show ε (b : K) = ((b⁻¹ : Kˣ) : K)
    rw [hε]
    have h9 : (q ^ 9) % 3 = 2 := by rw [Nat.pow_mod, hq]
    obtain ⟨k, hk⟩ : ∃ k, q ^ 9 = 3 * k + 2 := ⟨q ^ 9 / 3, by omega⟩
    have hb2 : (b : K) ^ 2 = ((b⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hb3'
    rw [hk, pow_add, pow_mul, hb3', one_pow, one_mul, hb2]
  have hA : A2Std σ b q₄ := ⟨hq4two, hK, hσ, hmod, hodd, hbσ, hb3, hb1⟩
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := by
    intro c
    simp only [hε]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    have hN : Nat.card K = q₄ ^ 3 := hK
    have hpowN : ∀ n : ℕ, c ^ (Nat.card K ^ n) = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_mul, ih]
        haveI : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
    have : q ^ 9 * (q ^ 9 * (q ^ 9 * q ^ 9)) = Nat.card K ^ 3 := by
      rw [hN, hq₄def]
      ring
    rw [this]
    exact hpowN 3
  obtain ⟨μ, hμ, hμε⟩ := exists_mu_unitary (p := p) (f := f) hf hA.toCore rfl hε hεb hε4
  set φ₄ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφ₄
  have hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ₄ y : ModGL TwistTag.D4.tag K) = a2Conj σ b (y : ModGL TwistTag.D4.tag K) :=
    a2_hφ_of_class (σ := σ) (d := b) hs
  obtain ⟨ρ, hnt, hcard, h1, h2, h3, h4, h5, h6⟩ :=
    exists_hom_fixSub_mu hA.toCore φ₄ hφ μ hμ
  obtain ⟨hker, hcopk, -, hmemρ⟩ := sl3_hom_charElemJ ρ hnt hcard hp hp5
  have hcompat := tau_rho_compat hA.toCore φ₄ ρ hμε h1 h2 h3 h4 h5 h6
  have hFcard : Nat.card (fixSubfield σ) = q₄ :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hA.two_le hA.card hA.frob
  haveI hFchar : CharP (fixSubfield σ) p :=
    ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective p).2 inferInstance
  let σQ : fixSubfield σ ≃+* fixSubfield σ := fixSubfieldRestrict ε σ
  have hσQ : ∀ c : fixSubfield σ, σQ c = c ^ (p ^ f) :=
    eps_restrict_frob (Q := p ^ f) rfl hσ hε
  obtain ⟨F₂, hF₂, ⟨e⟩⟩ := stdUnitary_equiv_fin (ℓ := p) (f := f) (ν := 3) hp
    (L := ↥(fixSubfield σ)) hf σQ hσQ le_rfl (by rw [hFcard])
  haveI hF₂char : CharP ↥F₂ p := (F₂.subtype.charP_iff F₂.subtype_injective p).2 inferInstance
  let θ : SL(3, fixSubfield σ) ≃* SL(3, fixSubfield σ) := stdUnitaryEquiv (ν := 3) σQ
  let S : Subgroup SL(3, fixSubfield σ) := fixSubgroup θ
  have hSmem : ∀ x, x ∈ S ↔ θ x = x := fun x => mem_fixSubgroup
  have hFD : LieFactorData p ↥(StatedSU 3 (p ^ f) ↥F₂) :=
    lieFactorData_statedSU_three hp hF₂ hq5
  have hSperf : Group.IsPerfect ↥S := ⟨(hFD.of_mulEquiv e).perfect⟩
  let ρY : SL(3, fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixSubO φ₄).subtype.comp ρ
  let τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := unTau σ ε
  have hτρ : ∀ x, τ.toMonoidHom (ρY x) = ρY (θ.toMonoidHom x) := fun x => hcompat x
  have hrange_le : ρY.range ≤ fixSubO φ₄ := by
    rintro _ ⟨x, rfl⟩
    exact (ρ x).2
  have hC' : ∀ g, g ∈ foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ↔
      g ∈ fixSubO φ₄ ∧ τ.toMonoidHom g = g := by
    intro g
    rw [Subgroup.mem_inf, mem_foldFix, mem_foldFix]
    rfl
  have hSC : S.map ρY ≤ foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro _ ⟨w, hw, rfl⟩
    refine (hC' _).2 ⟨hrange_le ⟨w, rfl⟩, ?_⟩
    rw [hτρ]
    exact congrArg ρY ((hSmem w).1 hw)
  have hSmap : ⁅S.map ρY, S.map ρY⁆ = S.map ρY := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hSperf]
  intro c ⟨n, hn⟩
  obtain ⟨hcφ, hcτ⟩ := (hC' c).1 c.2
  have hcn' : (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ p ^ n = 1 := by
    have := congrArg Subtype.val hn
    rwa [SubgroupClass.coe_pow] at this
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(fixSubO φ₄), (c₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = c :=
    ⟨⟨c, hcφ⟩, rfl⟩
  have hc₀n : c₀ ^ p ^ n = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hc₀]; exact hcn')
  obtain ⟨x, hx⟩ := hmemρ c₀ n hc₀n
  set N := Nat.card ρ.ker with hNdef
  have hxk : x ^ p ^ n ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    exact hc₀n
  have hxN : (x ^ p ^ n) ^ N = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard ρ.ker hxk)
  have hcopo : Nat.Coprime N (orderOf c₀) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hc₀n) (Nat.Coprime.pow_right n hcopk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopo
  set x' := (x ^ N) ^ m with hx'
  have hρx' : ρ x' = c₀ := by rw [hx', map_pow, map_pow, hx, hm]
  have hx'p : x' ^ p ^ n = 1 := by
    have e1 : x' ^ p ^ n = ((x ^ p ^ n) ^ N) ^ m := by
      rw [hx']
      simp only [← pow_mul]
      congr 1
      ring
    rw [e1, hxN, one_pow]
  have hρYx' : ρY x' = (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    show ((ρ x' : ↥(fixSubO φ₄)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = _
    rw [hρx', hc₀]
  have hθx : ρY (θ.toMonoidHom x') = ρY x' := by
    rw [← hτρ, hρYx']
    exact hcτ
  set z := θ.toMonoidHom x' * x'⁻¹ with hz
  have hzk : z ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have : ρY z = 1 := by rw [hz, map_mul, map_inv, hθx, mul_inv_cancel]
    exact this
  have hzN : z ^ N = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard ρ.ker hzk)
  have hzc : Commute z x' := (Subgroup.mem_center_iff.1 (hker hzk) x').symm
  have hzp : z ^ p ^ n = 1 := by
    have e1 : θ.toMonoidHom x' = z * x' := by rw [hz, inv_mul_cancel_right]
    have : (θ.toMonoidHom x') ^ p ^ n = 1 := by rw [← map_pow, hx'p, map_one]
    rwa [e1, hzc.mul_pow, hx'p, mul_one] at this
  have hz1 : z = 1 := eq_one_of_charPow_of_coprime hzp hcopk hzN
  have hx'S : x' ∈ S := (hSmem x').2 (mul_inv_eq_one.1 hz1)
  refine ⟨(S.map ρY).subgroupOf _, commutator_subgroupOf_eq_of_perfect hSC hSmap, ?_⟩
  rw [Subgroup.mem_subgroupOf]
  exact ⟨x', hx'S, hρYx'⟩

private theorem elemPerfJ_a2Minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : D4MinusToral p f hp K σ s) :
    ElemPerfJ p ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, _, _, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  have hq5 : 5 ≤ p ^ f :=
    hp5.trans (Nat.le_self_pow (by omega) p)
  have hcore := unitary_core_elemPerfJ (p := p) hp2 hf hq hq5 hK₄ hσ₄ hε hb3 hb1 hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  exact elemPerfJ_of_mulEquiv (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)).symm
    (elemPerfJ_of_mulEquiv e hcore)

end Unitary

section Plus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
open scoped MatrixGroups

private theorem elemPerfJ_a2Plus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {d : Kˣ} (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    ElemPerfJ p ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) := by
  have hA : A2Std σ d (p ^ f) := a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  obtain ⟨ρ, hρ, hcard, -⟩ :=
    exists_hom_fixSub hA.toCore (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) hφ
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  obtain ⟨-, -, hperf, hmem⟩ := sl3_hom_charElemJ ρ hρ hcard hp hp5
  refine elemPerfJ_of_mulEquiv (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)).symm ?_
  intro c ⟨n, hn⟩
  exact ⟨ρ.range, hperf, hmem c n hn⟩

end Plus

section G2

open CFSG.LieType.Chevalley

private theorem elemPerfJ_triD4_G2 {ℓ f : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ElemPerfJ ℓ ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
    (by omega) hf (Or.inr h5) hK σ hσ
  haveI : CharP K ℓ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.charP_of_card_pow_three hℓ hf hK
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hk : 3 ≤ Nat.card (fixSubfield σ) := by
    obtain ⟨q', hq'p, hq'c⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_primePower_card_subfield
        (ringChar.eq K ℓ) (fixSubfield σ)
    rw [hq'c, TauCeti.PrimePower.card_def, hq'p]
    exact (by omega : 3 ≤ ℓ).trans (Nat.le_self_pow q'.exponent_pos.ne' ℓ)
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup .G2
    (fixSubfield σ) (fun _ => hk)
  have htop : ⁅(⊤ : Subgroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))), ⊤⁆ =
      (⊤ : Subgroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))) := by
    have h1 : ⁅(⊤ : Subgroup ↥(adjointGroup Tag.G2 (fixSubfield σ))), ⊤⁆ =
        (⊤ : Subgroup ↥(adjointGroup Tag.G2 (fixSubfield σ))) := hperf.commutator_eq_top
    have h2 : (⊤ : Subgroup ↥(adjointGroup Tag.G2 (fixSubfield σ))).map e.symm.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.symm.surjective
    rw [← h2, ← Subgroup.map_commutator, h1]
  intro c _
  exact ⟨⊤, htop, Subgroup.mem_top c⟩

end G2

section Reduce

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

private theorem elemPerfJ_cocycle_q1 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    ElemPerfJ p ↥(fixSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
  have hRot := rotLang_holds
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hG2 : ElemPerfJ p ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    elemPerfJ_triD4_G2 hp5 hf hK σ hσ
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine elemPerfJ_of_conj_eq y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine elemPerfJ_of_conj_eq y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      exact hG2
    · exact elemPerfJ_a2Plus hp hp2 hp3 hf hq hK hσ hd hd3 hd1 hsd
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral hRot hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    refine elemPerfJ_of_conj_eq y₀ hconj ?_
    exact elemPerfJ_a2Plus hp hp2 hp3 hf hq hK hσ hd hd3 hd1 hsd

private theorem elemPerfJ_outer_three_odd_one {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    ElemPerfJ ℓ ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K₃ hK₃ Fr hFr φ hφord hφ
  · rw [hφ']
    exact elemPerfJ_cocycle_q1 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
  · have h := elemPerfJ_cocycle_q1 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
    rw [← hφ'] at h
    exact (elemPerfJ_inv_iff φ).1 h

private theorem elemPerfJ_outer_three_odd_two {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    ElemPerfJ ℓ ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hψ3 := d4_fieldActor_pow_three K₃ hK₃ Fr hFr
  have hG2 := elemPerfJ_triD4_G2 hℓ5 hf hK₃ Fr hFr
  have hTor : ∀ s, D4MinusToral ℓ f hp K₃ Fr s →
      ElemPerfJ ℓ ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) Fr Fr)) :=
    fun s hs => elemPerfJ_a2Minus hp hp2 hp3 hf hq hK₃ hFr hs
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K₃ hK₃ Fr hFr φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact elemPerfJ_of_conj_eq y hy hG2
    · exact elemPerfJ_of_conj_eq y hy ((elemPerfJ_inv_iff _).2 hG2)
  · rcases hys with hys | hys
    · exact elemPerfJ_of_conj_eq y hys (hTor s hs)
    · exact elemPerfJ_of_conj_eq y hys ((elemPerfJ_inv_iff _).2 (hTor s hs))
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr n hn hN
    have hPL := elemPerfJ_of_conj_eq y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact elemPerfJ_of_conj_eq y hyn hPL
    · exact elemPerfJ_of_conj_eq y hyn ((elemPerfJ_inv_iff _).2 hPL)

end Reduce

theorem qGen_triD4_outer_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (Fr : K ≃+* K)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom))
    (hφ : orderOf φ = 3)
    (hout : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)).range) :
    Inputs256e.QGen ℓ φ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hφ3 : φ ^ 3 = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hexp := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.trialityOuterExport_of
    (HardMathSupport.Solomon.Coordinator.LieComp.trialityOddA2Comps_of_toral
        HardMathSupport.Solomon.Coordinator.LieComp.TriA2.a2PlusComps_holds
        HardMathSupport.Solomon.Coordinator.LieComp.TriA2.a2MinusComps_holds) ℓ f (by omega) hf K hK Fr hFr φ
    hφ3 hout
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)) (by omega)
  have hqp : Inputs256f.QPerf ℓ φ := by
    rcases (show (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 by omega) with hq | hq
    · exact qPerf_of_elemPerfJ (elemPerfJ_outer_three_odd_one h5 hf hq hK Fr hFr φ hφ3 hout)
    · exact qPerf_of_elemPerfJ (elemPerfJ_outer_three_odd_two h5 hf hq hK Fr hFr φ hφ3 hout)
  exact Inputs256f.qGen_of_qPerf hexp.toComps hqp

theorem qGenTriD4Rest_of_outer (hout : LangOuterCharElem) : Inputs256f.QGenTriD4Rest := by
  intro ℓ f hℓ h5 hf K _ _ hK Fr hFr p hp hp2 hpℓ φ hφ hcase
  by_cases hin : φ ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)).range
  · exact qGen_triD4_inner_of_outer hout hℓ h5 hf hK Fr hFr hp hp2 hpℓ φ hφ hin
  · rcases hcase with h | ⟨rfl, -⟩
    · exact absurd h hin
    · exact qGen_triD4_outer_three hℓ h5 hf hK Fr hFr φ hφ hin

theorem qGenExc_of_outer (hout : LangOuterCharElem) : Inputs256e.QGenExc :=
  Inputs256f.qGenExc_of_inndiag (qGenExcInndiag_of_outer hout) (qGenTwE6Inndiag_of_outer hout)
    (qGenTriD4Rest_of_outer hout)

theorem qGenExcInndiag_holds : Inputs256f.QGenExcInndiag :=
  qGenExcInndiag_of_outer langOuterCharElem_holds

theorem qGenTwE6Inndiag_holds : Inputs256f.QGenTwE6Inndiag :=
  qGenTwE6Inndiag_of_outer langOuterCharElem_holds

theorem qGenTriD4Rest_holds : Inputs256f.QGenTriD4Rest :=
  qGenTriD4Rest_of_outer langOuterCharElem_holds

theorem qGenExc_holds : Inputs256e.QGenExc :=
  qGenExc_of_outer langOuterCharElem_holds

theorem seitzThm4Rest4_of_uniSeitz (hU : Inputs2311c.UniSeitzPlanes Inputs2311f.OddCpfRest3)
    (h3 : Inputs256e.Input14_2StructThree) : SeitzRest2.SeitzThm4Rest4 :=
  ⟨hU, qGenExcInndiag_holds, qGenTwE6Inndiag_holds, qGenTriD4Rest_holds, h3⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

end
