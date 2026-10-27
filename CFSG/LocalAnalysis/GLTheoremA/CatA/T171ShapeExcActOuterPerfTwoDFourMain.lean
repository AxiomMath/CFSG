module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourStableStab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice
open scoped Pointwise commutatorElement


theorem twoDExcFixedPointsDatumRankFour_of_graph (hG : RankFourGraphTwist)
    (hE8 : RankFourTwoDE8Stable) : TwoDExcFixedPointsDatumRankFour := by
  intro τ L _ _ _ p S a hT i hkind h4
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r = 2 := CharP.eq L hchar ‹CharP L 2›
  subst hr2
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    image_componentRoots_eq_of_twoD_rank_four hE8 S hT i hkind h4
  have hs1 : componentOrbitLength S.ρ Ψ = 1 :=
    componentOrbitLength_eq_one ((finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ)
      fun γ hγ => hst.subset (Set.mem_image_of_mem _ hγ)
  have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    tag_simplyLaced_of_twistKind_twoD_rank_four S hT i hkind h4
  have hsl : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  obtain ⟨v, hv, hmaps, hpos, hGtwist⟩ := hG S hT i hkind h4 hst hsl
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : IsIsometry Ψ (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg _ γ⟩
  have hΔ : ∀ β ∈ simpleRoots Ψ, S.rhoTwist v β ∈ simpleRoots Ψ := fun β hβ =>
    hf.apply_mem_simpleRoots hΨ hpos hβ
  obtain ⟨y, hyZ, hyM, hyv, hpin⟩ := S.exists_twoD_pin hq i hv hΔ
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hSC : ∀ T : Set (Fin τ.rank → ℤ),
      torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L := fun T =>
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hyC : y ∈ adjointGroup τ L := hSC Ψ hyZ
  have hFc : ∀ g, frobTwistGL τ L 2 e (y * Q) g = y * S.D.step g * y⁻¹ := by
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
  have hU : ∀ γ ∈ Ψ, (rootSubgroup τ L γ).map (frobTwistGL τ L 2 e (y * Q)) =
      rootSubgroup τ L (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ L 2 e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots Ψ, ∀ A : SL2 L,
      frobTwistGL τ L 2 e (y * Q) (rootSL2 τ L β A) =
        rootSL2 τ L (S.rhoTwist v β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 e) A) :=
    fun β hβ A => by rw [hFc]; exact hpin β hβ A
  obtain ⟨D, -, hDroots, hDsimple, hDperf, hDtor, hDfixed⟩ :=
    exists_twoD_datum_fixed_roots hτ he i (S.rhoTwist v) hiso hmaps hpos hGtwist hcT hcG hU hpin'
  have hyZ' : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
  obtain ⟨z, hzZ, hz⟩ := S.exists_lang_twoDT he hQT hstep hT hyZ'
  have hzC : z ∈ adjointGroup τ L := hSC _ hzZ
  have hzN : z ∈ Subgroup.normalizer (rootSpan τ L Ψ) := mem_normalizer_rootSpan_of_mem_Z hzZ i
  have hconj := map_fixedPointSubgroup_conj_eq_of_pin (Ψ := Ψ) (F := S.D.step)
    (F' := frobTwistGL τ L 2 e (y * Q)) hFc hz hzN hzC
  obtain ⟨h4', hcard⟩ := shape_of_twistKind_twoD hkind
  have hiso := outer_isIsometry_rho S (s := 1) (by rw [Function.iterate_one]; exact hst)
  have hni : ¬ twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
    rw [← hs1]
    exact not_twistInner_of_twistKind_twoD_exc (Or.inl hkind)
  have hdet : (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 :=
    det_cartan_eq_four_of_nonInner hΨ _ hiso.bijOn hiso.iform_eq hiso.neg hni h4' hcard
  have hcenter : Subgroup.center (rootSpan τ L Ψ) = ⊥ :=
    center_eq_bot_of_twistKind_twoD S hT i hkind
  have hiter : iterHom S.D.step 1 = S.D.step :=
    MonoidHom.ext fun g => by rw [iterHom_eq_iterate, Function.iterate_one]
  refine ⟨D, simpleRoots Ψ, z, hDperf, ?_, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hDsimple]
  · intro γ hγ
    rw [hDroots] at hγ
    exact exists_coords hΨ hγ
  · rw [hDroots]
    exact hcenter
  · rw [hDroots]
    exact hDtor
  · rw [hs1, hiter, hconj, hDfixed]

theorem twoDExcFixedPointsDatum_of_graph (hG : RankFourGraphTwist)
    (hE8 : RankFourTwoDE8Stable) : TwoDExcFixedPointsDatum :=
  twoDExcFixedPointsDatum_of_rankFour (twoDExcFixedPointsDatumRankFour_of_graph hG hE8)

theorem twoDExcFixedPointsPerfect_holds_of_graph (hG : RankFourGraphTwist)
    (hE8 : RankFourTwoDE8Stable) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
  twoDExcFixedPointsPerfect_holds_of_rankFour
    (twoDExcFixedPointsDatumRankFour_of_graph hG hE8) S hT i hkind

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
