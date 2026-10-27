module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDatum

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem isQuasisimple_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e h

section Setup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem LangSetup.exists_step_frobTwist_adjoint {r e : ℕ} [Fact r.Prime] [CharP L r]
    (he : S.D.q = r ^ e) :
    ∃ Q : ModGL τ L, Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      (adjointGroup τ L).map (MulAut.conj Q).toMonoidHom = adjointGroup τ L ∧
      ∀ g, S.D.step g = frobTwistGL τ L r e Q g := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hFrE : Fr = iterateFrobenius L r e :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, he]
  have hPfix : P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      (adjointGroup τ L).map (MulAut.conj P).toMonoidHom = adjointGroup τ L := by
    rcases hP with rfl | ⟨t, h, rfl⟩
    · refine ⟨one_mem _, ?_⟩
      have h1 : (MulAut.conj (1 : ModGL τ L)).toMonoidHom = MonoidHom.id _ := by
        ext g
        simp
      rw [h1, Subgroup.map_id]
    · subst h
      refine ⟨diagramMap_mem_normalizer t, ?_⟩
      change (adjointGroup t.tag L).map (MulAut.conj (diagramMap t L)).toMonoidHom = _
      rw [conj_diagramMap_eq_twistHom]
      exact map_twistHom_adjointGroup t L (RingHom.id L) Function.surjective_id
  have hnC : S.D.n ∈ adjointGroup τ L := by
    rw [hn]
    exact canonicalRep_mem_adjointGroup _ L w
  refine ⟨S.D.n * P, mul_mem ?_ hPfix.1, ?_, fun g => ?_⟩
  · rw [hn]
    exact canonicalRep_mem_normalizer w
  · have e1 : (MulAut.conj (S.D.n * P)).toMonoidHom =
        (MulAut.conj S.D.n).toMonoidHom.comp (MulAut.conj P).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hPfix.2]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hnC)
  · rw [frobTwistGL_apply]
    show S.D.n * S.D.Φ g * S.D.n⁻¹ = _
    rw [hΦ g, hFrE]
    change S.D.n * (P * entrywiseFrobGL τ L r e g * P⁻¹) * S.D.n⁻¹ = _
    group

theorem LangSetup.exists_lang_twoDT {r e : ℕ} [Fact r.Prime] [CharP L r] (_he0 : 0 < e)
    {Q : ModGL τ L} (_hQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (_hstep : ∀ g, S.D.step g = frobTwistGL τ L r e Q g) (hT : rootDiagUnit τ a ∈ S.D.torus)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)), S.D.step z = z * y := by
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S one_pos
    (fun γ hγ => by rw [Function.iterate_one]; exact outer_rho_mem_kernelRoots S hT hγ) hy
  exact ⟨z, hzZ, by rw [← hz, iterHom_eq_iterate, Function.iterate_one]⟩

theorem LangSetup.exists_lang_twoD {r e : ℕ} [Fact r.Prime] [CharP L r] (he0 : 0 < e)
    {Q : ModGL τ L} (hQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hstep : ∀ g, S.D.step g = frobTwistGL τ L r e Q g) (hE : rootDiagUnit τ a ∈ S.E)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)), S.D.step z = z * y :=
  S.exists_lang_twoDT he0 hQ hstep (S.E_le hE).1 hy

theorem mem_normalizer_rootSpan_of_mem_Z {z : ModGL τ L}
    (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (j : KernelComponent (rootCharHom a)) :
    z ∈ Subgroup.normalizer
      (rootSpan τ L (componentRoots (rootCharHom a) j) : Set (ModGL τ L)) :=
  Subgroup.mem_normalizer_iff.2 (mem_componentRootSpan_iff_conj_of_mem hz j)

end Setup

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem LangSetup.isQuasisimple_rationalComponent_twoDT
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  obtain ⟨C, hCqs, hCperf, hCle, hcomm⟩ := exists_twoD_core hτ (by omega : 1 ≤ e) i
    (S.rhoTwist v) hiso hmaps hpos hG hcT hcG hU hpin'
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
  have e' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≃* C :=
    ((rationalComponent S.ρ S.Γ (rootCharHom a) i).equivMapOfInjective φ hφinj).trans
      (MulEquiv.subgroupCongr hRC)
  exact isQuasisimple_of_mulEquiv' e'.symm hCqs

theorem LangSetup.isQuasisimple_rationalComponent_twoD
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hE : rootDiagUnit τ a ∈ S.E) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  S.isQuasisimple_rationalComponent_twoDT hτ (S.E_le hE).1 i hkind h5

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
