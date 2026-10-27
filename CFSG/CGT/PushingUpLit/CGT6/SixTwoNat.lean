module

public import CFSG.CGT.PushingUpLit.CGT6.Props
public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def blockUEquiv (X : Subgroup G) : ↥(shortU ↥X) ≃* ↥(blockU X) :=
  (Subgroup.equivMapOfInjective (shortU ↥X) X.subtype X.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_shortU_subtype X))

theorem blockUEquiv_coe (X : Subgroup G) (u : ↥(shortU ↥X)) :
    ((blockUEquiv X u : ↥(blockU X)) : G) = (((u : ↥X)) : G) := rfl

theorem normalizer_le_normalizer_blockU (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (blockU X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_blockU hg hu, fun hu => ?_⟩
  have := conj_mem_blockU (inv_mem hg) hu
  simpa [mul_assoc] using this

theorem blockU_le_commutator {X : Subgroup G} (hperf : ⁅X, X⁆ = X) :
    blockU X ≤ ⁅X, blockU X⁆ := by
  have hperfX : commutator ↥X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hperf
  have hpn : (pCore 2 ↥X).Normal := inferInstance
  have hUn : (shortU ↥X).Normal := by
    unfold shortU
    infer_instance
  have hNn : (⁅(⊤ : Subgroup ↥X), shortU ↥X⁆).Normal := Subgroup.commutator_normal _ _
  have e1 : ⁅pCore 2 ↥X, (⊤ : Subgroup ↥X)⁆ = shortU ↥X := rfl
  have e2 : ⁅(⊤ : Subgroup ↥X), pCore 2 ↥X⁆ = shortU ↥X := by
    rw [Subgroup.commutator_comm]
    rfl
  have e3 : ⁅shortU ↥X, (⊤ : Subgroup ↥X)⁆ = ⁅(⊤ : Subgroup ↥X), shortU ↥X⁆ :=
    Subgroup.commutator_comm _ _
  have h1 : ⁅⁅(⊤ : Subgroup ↥X), pCore 2 ↥X⁆, (⊤ : Subgroup ↥X)⁆ ≤
      ⁅(⊤ : Subgroup ↥X), shortU ↥X⁆ := by
    rw [e2, e3]
  have h2 : ⁅⁅pCore 2 ↥X, (⊤ : Subgroup ↥X)⁆, (⊤ : Subgroup ↥X)⁆ ≤
      ⁅(⊤ : Subgroup ↥X), shortU ↥X⁆ := by
    rw [e1, e3]
  have h3 := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal h1 h2
  rw [← commutator_def, hperfX, e2] at h3
  have h4 := Subgroup.map_mono (f := X.subtype) h3
  rw [Subgroup.map_commutator, map_shortU_subtype, Subgroup.map_top, Subgroup.range_subtype] at h4
  exact h4


section ToAlt

variable {X : Subgroup G}

@[expose] noncomputable def toAlt {m : ℕ} (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin m)) :
    ↥X →* alternatingGroup (Fin m) :=
  (φ : (↥X ⧸ pCore 2 ↥X) →* _).comp (QuotientGroup.mk' (pCore 2 ↥X))

theorem toAlt_apply {m : ℕ} (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin m)) (g : ↥X) :
    toAlt φ g = φ (QuotientGroup.mk g) := rfl

theorem toAlt_surjective {m : ℕ} (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin m)) :
    Function.Surjective (toAlt φ) :=
  φ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem toAlt_eq_one_iff {m : ℕ} (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin m)) (g : ↥X) :
    toAlt φ g = 1 ↔ g ∈ pCore 2 ↥X := by
  rw [toAlt_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem toAlt_eq_iff {m : ℕ} (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin m)) (g g' : ↥X) :
    toAlt φ g = toAlt φ g' ↔ g⁻¹ * g' ∈ pCore 2 ↥X := by
  rw [← toAlt_eq_one_iff φ, map_mul, map_inv, inv_mul_eq_one]

end ToAlt

section Alt

variable [Finite G] {X : Subgroup G}

theorem inf_centralizer_blockU_eq {a : ℕ}
    {φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hX : IsShortGroup ↥X) (h3 : 3 ≤ 2 * a + 1) (hnat : IsNaturalAltModuleWith ↥X a φ) :
    X ⊓ Subgroup.centralizer (blockU X : Set G) = oTwoIn X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨ψ, hsum, hsurj, hψk, hψe⟩ := hnat
    set x' : ↥X := ⟨x, hxX⟩ with hx'
    set σ : Equiv.Perm (Fin (2 * a + 1)) :=
      ((φ (QuotientGroup.mk x' : ↥X ⧸ pCore 2 ↥X) : alternatingGroup (Fin (2 * a + 1))) :
        Equiv.Perm (Fin (2 * a + 1))) with hσ
    have hcomm : ∀ u : ↥(shortU ↥X), x' * (u : ↥X) = (u : ↥X) * x' := by
      intro u
      apply Subtype.ext
      have huU : ((u : ↥X) : G) ∈ blockU X := by
        rw [← map_shortU_subtype]
        exact ⟨u, u.2, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hxC _ huU).symm
    have hfix : ∀ v : ↥(coreMod (2 * a + 1)),
        permAct (2 * a + 1) σ (v : PermMod (2 * a + 1)) = (v : PermMod (2 * a + 1)) := by
      intro v
      obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (v : PermMod (2 * a + 1))) v.2
      have e : x' * (u : ↥X) * x'⁻¹ = (u : ↥X) := by
        rw [hcomm u]
        group
      have hu' : x' * (u : ↥X) * x'⁻¹ ∈ shortU ↥X := by
        rw [e]
        exact u.2
      have key := hψe x' u u.2 hu'
      have e2 : (⟨x' * (u : ↥X) * x'⁻¹, hu'⟩ : ↥(shortU ↥X)) = u := Subtype.ext e
      rw [e2] at key
      have hu2 : ψ u = (v : PermMod (2 * a + 1)) := by
        rw [hu]
        rfl
      rw [hu2] at key
      exact key.symm
    have hone : coreAct (2 * a + 1) σ = 1 := by
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [coreAct_coe]
      exact hfix v
    have hσ1 : σ = 1 := coreAct_injective h3 (hone.trans (map_one (coreAct (2 * a + 1))).symm)
    have hφ1 : φ (QuotientGroup.mk x') = 1 := Subtype.ext hσ1
    have hq : QuotientGroup.mk x' = (1 : ↥X ⧸ pCore 2 ↥X) := (MulEquiv.map_eq_one_iff φ).mp hφ1
    have hxp : x' ∈ pCore 2 ↥X := (QuotientGroup.eq_one_iff x').mp hq
    exact ⟨x', hxp, rfl⟩
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨oTwoIn_le X hr, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact blockU_comm_of_short hX u hu r hr


theorem exists_altNatData {a : ℕ}
    {φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hX : IsShortGroup ↥X) (hperf : ⁅X, X⁆ = X) (h3 : 3 ≤ 2 * a + 1)
    (hnat : IsNaturalAltModuleWith ↥X a φ) (hU2 : CFSG.Open.IsElemAbelian 2 (blockU X)) :
    ∃ D : @AltNatData ↥(blockU X) (commGroupOfElemAbelian hU2) (autOn X (blockU X))
        (2 * a + 1),
      ∀ g : ↥X, @AltNatData.θ _ (commGroupOfElemAbelian hU2) _ _ D
        (actOnRange (blockU X) X (le_normalizer_blockU X) g) = φ (QuotientGroup.mk g) := by
  classical
  let _ : CommGroup ↥(blockU X) := commGroupOfElemAbelian hU2
  have hXU : X ≤ Subgroup.normalizer (blockU X : Set G) := le_normalizer_blockU X
  have hC := inf_centralizer_blockU_eq hX h3 hnat
  obtain ⟨ψ, hsum, hsurj, hψk, hψe⟩ := hnat
  let eU := blockUEquiv X
  let ρ := actOnRange (blockU X) X hXU
  have hρs : Function.Surjective ρ := actOnRange_surjective (blockU X) X hXU
  let φ' : ↥X →* alternatingGroup (Fin (2 * a + 1)) :=
    (φ : (↥X ⧸ pCore 2 ↥X) →* _).comp (QuotientGroup.mk' (pCore 2 ↥X))
  have hφ's : Function.Surjective φ' := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφ'k : φ'.ker = pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ pCore 2 ↥X
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hkerEq : ρ.ker = φ'.ker := by
    rw [ker_actOnRange, hC, hφ'k]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective (pCore 2 ↥X)
  let θ : ↥(autOn X (blockU X)) ≃* alternatingGroup (Fin (2 * a + 1)) :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's))
  have hθ : ∀ g : ↥X, θ (ρ g) = φ' g := fun g => by
    show (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's)
      ((QuotientGroup.quotientMulEquivOfEq hkerEq)
        ((QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (ρ g))) = φ' g
    have : (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (ρ g) =
        (QuotientGroup.mk g : ↥X ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  let β : ↥(blockU X) →* ↥(coreMod (2 * a + 1)) :=
    (ψ.comp eU.symm.toMonoidHom).codRestrict (coreMod (2 * a + 1)) fun w => by
      rw [mem_coreMod]
      exact hsum _
  have hβcoe : ∀ w : ↥(blockU X), ((β w : ↥(coreMod (2 * a + 1))) : PermMod (2 * a + 1)) =
      ψ (eU.symm w) := fun w => rfl
  have hcoe : ∀ w : ↥(blockU X), (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) = (w : G) := by
    intro w
    have := blockUEquiv_coe X (eU.symm w)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hβs : Function.Surjective β := by
    intro v
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (v : PermMod (2 * a + 1))) v.2
    refine ⟨eU u, Subtype.ext ?_⟩
    rw [hβcoe, MulEquiv.symm_apply_apply, hu]
    rfl
  have hkerfix : ∀ w : ↥(blockU X), β w = 1 → w ∈ fixV (autOn X (blockU X)) := by
    intro w hw
    have h1 : ψ (eU.symm w) = 1 := congrArg Subtype.val hw
    have h2 : eU.symm w ∈ ψ.ker := h1
    rw [hψk, Subgroup.mem_subgroupOf] at h2
    have h3' : ((eU.symm w : ↥(shortU ↥X)) : ↥X) ∈ Subgroup.center ↥X := (Subgroup.mem_inf.mp h2).2
    intro g hg
    obtain ⟨y, hy⟩ := hρs ⟨g, hg⟩
    have hyg : (g : MulAut ↥(blockU X)) = actOn (blockU X) X hXU y := (congrArg Subtype.val hy).symm
    rw [hyg]
    apply Subtype.ext
    rw [actOn_apply_coe]
    have hc := Subgroup.mem_center_iff.mp h3' y
    have hcG : (y : G) * (w : G) = (w : G) * (y : G) := by
      rw [← hcoe w]
      exact congrArg Subtype.val hc
    rw [hcG]
    group
  have hequi : ∀ (e : ↥(autOn X (blockU X))) (w : ↥(blockU X)),
      β ((e : MulAut ↥(blockU X)) w) = coreAct (2 * a + 1)
        ((θ e : alternatingGroup (Fin (2 * a + 1))) : Equiv.Perm (Fin (2 * a + 1))) (β w) := by
    intro e w
    obtain ⟨y, rfl⟩ := hρs e
    rw [hθ y]
    set u : ↥(shortU ↥X) := eU.symm w with hu
    have hu1 : ((u : ↥X) : G) = (w : G) := hcoe w
    have hu' : y * (u : ↥X) * y⁻¹ ∈ shortU ↥X := by
      rw [← Subgroup.mem_map_iff_mem X.subtype_injective, map_shortU_subtype]
      show (y : G) * ((u : ↥X) : G) * (y : G)⁻¹ ∈ blockU X
      rw [hu1]
      exact conj_mem_blockU (Subgroup.le_normalizer y.2) w.2
    have hsub : eU.symm ((ρ y : MulAut ↥(blockU X)) w) = ⟨y * (u : ↥X) * y⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((ρ y : MulAut ↥(blockU X)) w : G) = (y : G) * ((u : ↥X) : G) * (y : G)⁻¹
      rw [hu1]
      exact actOn_apply_coe hXU y w
    have key := hψe y u u.2 hu'
    apply Subtype.ext
    rw [hβcoe, hsub, key, coreAct_coe, hβcoe]
    rfl
  have hcomm : commV (autOn X (blockU X)) = ⊤ := by
    have h1 : commV (autOn X (blockU X)) = commOn hU2 X := rfl
    rw [h1, commOn_eq hU2 hXU, Subgroup.subgroupOf_eq_top]
    exact blockU_le_commutator hperf
  exact ⟨
    { θ := θ
      β := β
      surj := hβs
      ker_fix := hkerfix
      equivar := hequi
      comm_top := hcomm }, hθ⟩


theorem isNatAlt_blockU {a : ℕ}
    {φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hX : IsShortGroup ↥X) (h3 : 3 ≤ 2 * a + 1) (hnat : IsNaturalAltModuleWith ↥X a φ) :
    IsNatAlt X (blockU X) (2 * a + 1) := by
  classical
  have hC := inf_centralizer_blockU_eq hX h3 hnat
  obtain ⟨ψ, hsum, hsurj, hψk, hψe⟩ := hnat
  let eU := blockUEquiv X
  let β : ↥(blockU X) →* ↥(coreMod (2 * a + 1)) :=
    (ψ.comp eU.symm.toMonoidHom).codRestrict (coreMod (2 * a + 1)) fun w => by
      rw [mem_coreMod]
      exact hsum _
  have hβcoe : ∀ w : ↥(blockU X), ((β w : ↥(coreMod (2 * a + 1))) : PermMod (2 * a + 1)) =
      ψ (eU.symm w) := fun w => rfl
  have hcoe : ∀ w : ↥(blockU X), (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) = (w : G) := by
    intro w
    have := blockUEquiv_coe X (eU.symm w)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hβs : Function.Surjective β := by
    intro v
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (v : PermMod (2 * a + 1))) v.2
    refine ⟨eU u, Subtype.ext ?_⟩
    rw [hβcoe, MulEquiv.symm_apply_apply, hu]
    rfl
  refine ⟨toAlt φ, β, toAlt_surjective φ, ?_, hβs, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, toAlt_eq_one_iff, Subgroup.mem_subgroupOf, hC]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      rwa [← this]
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : β w = 1 ↔ ψ (eU.symm w) = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, ← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      have hs' : (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) ∈ blockZ X := by
        rw [← map_shortC_subtype]
        exact Subgroup.mem_map_of_mem _ hs
      rw [hcoe w] at hs'
      exact hs'
    · intro hw
      have : (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) ∈ blockZ X := by rw [hcoe w]; exact hw
      rw [← map_shortC_subtype] at this
      obtain ⟨c, hc, hcx⟩ := this
      have : c = ((eU.symm w : ↥(shortU ↥X)) : ↥X) := Subtype.ext hcx
      rwa [← this]
  · intro e w hw
    set u : ↥(shortU ↥X) := eU.symm w with hu
    have hu1 : ((u : ↥X) : G) = (w : G) := hcoe w
    have hu' : e * (u : ↥X) * e⁻¹ ∈ shortU ↥X := by
      rw [← Subgroup.mem_map_iff_mem X.subtype_injective, map_shortU_subtype]
      show (e : G) * ((u : ↥X) : G) * (e : G)⁻¹ ∈ blockU X
      rw [hu1]
      exact hw
    have hsub : eU.symm ⟨(e : G) * w * (e : G)⁻¹, hw⟩ = ⟨e * (u : ↥X) * e⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show (e : G) * (w : G) * (e : G)⁻¹ = (e : G) * ((u : ↥X) : G) * (e : G)⁻¹
      rw [hu1]
    have key := hψe e u u.2 hu'
    apply Subtype.ext
    rw [hβcoe, hsub, key, coreAct_coe, hβcoe]
    rfl

end Alt

end CFSG.CGT.PushingUpLit.CGT6
