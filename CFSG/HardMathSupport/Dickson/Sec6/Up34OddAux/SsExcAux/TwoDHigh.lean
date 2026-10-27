module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.TwoDHighCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem ssexc_twoD_high_pSubgroup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) {l : ℕ} (hl : l.Prime) [CharP L l]
    (hl5 : 5 ≤ l) :
    ∃ V : Subgroup ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), IsPGroup l V ∧
      8 ≤ Nat.card V := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have := hchar
  have hrl : r = l := CharP.eq L hchar ‹CharP L l›
  have hr5 : 5 ≤ r := hrl ▸ hl5
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
  obtain ⟨C, hCqs, hCperf, hCle, hcomm, V₀, hV₀C, hV₀exp, hV₀card⟩ := ssexc_twoD_core hτ hr5
    (by omega : 1 ≤ e) i (S.rhoTwist v) hiso hmaps hpos hG hne hcT hcG hU hpin'
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
  let Vc : Subgroup (ModGL τ L) := V₀.map (MulAut.conj z).toMonoidHom
  have hVc : Vc ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∈ (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ := hRC ▸ hV₀C hx
    obtain ⟨y, hy, hyx⟩ := hxC
    have hzy : (MulAut.conj z).toMonoidHom x = y := by
      rw [← hyx, hφapp]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hzy]
    exact hy
  refine ⟨Vc.subgroupOf (rationalComponent S.ρ S.Γ (rootCharHom a) i), ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
    have hxl : x ^ l = 1 := hrl ▸ hV₀exp x hx
    have h1 : ((g : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL τ L) ^ l = 1 := by
      rw [← hxg, ← map_pow, hxl, map_one]
    exact Subtype.ext (Subtype.ext (by simpa using h1))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVc).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj z).injective]
    exact hV₀card

end CFSG.HardMathSupport.Dickson.Sec6
