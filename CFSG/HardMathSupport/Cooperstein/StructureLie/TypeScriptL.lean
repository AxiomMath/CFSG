module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.Nodes
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLRep
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLShape
import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM blockV IsOrthogonalTwo)
open CFSG.Open (pCoreOf)
open Matrix
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] {L : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def HasModuleRep (L : Subgroup G) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) W) : Prop :=
  ∃ cls : blockU L →* Multiplicative W, Function.Surjective cls ∧
    cls.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : ↥L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (cls v) =
        (ρ ℓ : W →ₗ[ZMod 2] W) (Multiplicative.toAdd (cls u))

noncomputable def coordGL {ι : Type} [Fintype ι] [DecidableEq ι] (φ : W ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    LinearMap.GeneralLinearGroup (ZMod 2) W ≃* GL ι (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).trans Matrix.GeneralLinearGroup.toLin.symm

theorem coordGL_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (φ : W ≃ₗ[ZMod 2] (ι → ZMod 2))
    (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (w : W) :
    ((coordGL φ g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φ w =
      φ ((g : W →ₗ[ZMod 2] W) w) := by
  have h1 : ((coordGL φ g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φ w =
      (Matrix.GeneralLinearGroup.toLin (coordGL φ g) : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
        (φ w) := by
    rw [Matrix.GeneralLinearGroup.coe_toLin]
    rfl
  rw [h1]
  have h2 : Matrix.GeneralLinearGroup.toLin (coordGL φ g) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv φ g := by
    simp [coordGL]
  rw [h2]
  simp [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]

theorem eq_of_mulVec_eq {ι : Type} [Fintype ι] [DecidableEq ι] (φ : W ≃ₗ[ZMod 2] (ι → ZMod 2))
    {A B : Matrix ι ι (ZMod 2)} (h : ∀ w : W, A *ᵥ φ w = B *ᵥ φ w) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have := h (φ.symm v)
  simpa using this

theorem exists_typeData_of_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : Subgroup (GL ι (ZMod 2)))
    {ρ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) W} (hρ : HasModuleRep L ρ)
    (hker : ρ.ker = CFSG.pCore 2 ↥L) (φ : W ≃ₗ[ZMod 2] (ι → ZMod 2))
    (h1 : ∀ g ∈ ρ.range, ∃ A ∈ Ω,
      ∀ w : W, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : W →ₗ[ZMod 2] W) w))
    (h2 : ∀ A ∈ Ω, ∃ g ∈ ρ.range,
      ∀ w : W, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : W →ₗ[ZMod 2] W) w)) :
    ∃ α : ↥L →* ↥Ω, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ∃ β : blockU L →* Multiplicative (ι → ZMod 2), Function.Surjective β ∧
        β.ker = (blockZ L).subgroupOf (blockU L) ∧
        ∀ (ℓ : ↥L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
          Multiplicative.toAdd (β v) =
            ((α ℓ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
  obtain ⟨cls, hsurj, hclsker, hact⟩ := hρ
  have hmem : ∀ ℓ : ↥L, (coordGL φ).toMonoidHom (ρ ℓ) ∈ Ω := fun ℓ => by
    obtain ⟨A, hA, hAw⟩ := h1 (ρ ℓ) ⟨ℓ, rfl⟩
    have : A = coordGL φ (ρ ℓ) := Units.ext (eq_of_mulVec_eq φ fun w => by
      rw [hAw w, coordGL_mulVec])
    rw [this] at hA
    exact hA
  let α : ↥L →* ↥Ω := ((coordGL φ).toMonoidHom.comp ρ).codRestrict Ω hmem
  have hα : ∀ ℓ : ↥L, ((α ℓ : GL ι (ZMod 2))) = coordGL φ (ρ ℓ) := fun ℓ => rfl
  have hαsurj : Function.Surjective α := by
    rintro ⟨A, hA⟩
    obtain ⟨g, ⟨ℓ, rfl⟩, hgw⟩ := h2 A hA
    refine ⟨ℓ, Subtype.ext ?_⟩
    rw [hα]
    exact Units.ext (eq_of_mulVec_eq φ fun w => by rw [hgw w, coordGL_mulVec]) |>.symm
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext ℓ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, hα]
    simp only [OneMemClass.coe_one]
    exact ⟨fun h => (coordGL φ).injective (h.trans (map_one _).symm),
      fun h => by rw [h, map_one]⟩
  let ψ : Multiplicative W →* Multiplicative (ι → ZMod 2) :=
    AddMonoidHom.toMultiplicative (φ.toLinearMap.toAddMonoidHom)
  have hψ : ∀ x, Multiplicative.toAdd (ψ x) = φ (Multiplicative.toAdd x) := fun x => rfl
  have hψinj : Function.Injective ψ := fun a b hab => by
    have := congrArg Multiplicative.toAdd hab
    rw [hψ, hψ] at this
    exact Multiplicative.toAdd.injective (φ.injective this)
  have hψsurj : Function.Surjective ψ := fun y =>
    ⟨Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd y)), by
      apply Multiplicative.toAdd.injective
      rw [hψ]
      simp⟩
  refine ⟨α, hαsurj, hαker, ψ.comp cls, hψsurj.comp hsurj, ?_, ?_⟩
  · rw [← hclsker]
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hψinj (h.trans (map_one ψ).symm), fun h => by rw [h, map_one]⟩
  · intro ℓ u v huv
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hψ, hψ, hact ℓ u v huv, hα,
      coordGL_mulVec]

theorem isAltNaturalType_of_model {ρ : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) W}
    (hρ : HasModuleRep L ρ) (hker : ρ.ker = CFSG.pCore 2 ↥L) {m : ℕ}
    (h : IsAltModel ρ.range m) : IsAltNaturalType L m := by
  obtain ⟨cls, hsurj, hclsker, hact⟩ := hρ
  obtain ⟨φ, θ, hφθ⟩ := h
  let α : ↥L →* alternatingGroup (Fin m) := θ.toMonoidHom.comp ρ.rangeRestrict
  have hαsurj : Function.Surjective α :=
    θ.surjective.comp ρ.rangeRestrict_surjective
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext ℓ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hℓ
      have : ρ.rangeRestrict ℓ = 1 := θ.injective (hℓ.trans (map_one θ).symm)
      exact congrArg Subtype.val this
    · intro hℓ
      have : ρ.rangeRestrict ℓ = 1 := Subtype.ext hℓ
      change θ (ρ.rangeRestrict ℓ) = 1
      rw [this, map_one]
  let ψ : Multiplicative W →* Multiplicative (altHeart m) :=
    AddMonoidHom.toMultiplicative φ.toAddMonoidHom
  have hψ : ∀ x, Multiplicative.toAdd (ψ x) = φ (Multiplicative.toAdd x) := fun x => rfl
  have hψinj : Function.Injective ψ := fun a b hab => by
    have := congrArg Multiplicative.toAdd hab
    rw [hψ, hψ] at this
    exact Multiplicative.toAdd.injective (φ.injective this)
  have hψsurj : Function.Surjective ψ := fun y =>
    ⟨Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd y)), by
      apply Multiplicative.toAdd.injective
      rw [hψ]
      simp⟩
  refine ⟨α, hαsurj, hαker, ψ.comp cls, hψsurj.comp hsurj, ?_, ?_⟩
  · rw [← hclsker]
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hψinj (h.trans (map_one ψ).symm), fun h => by rw [h, map_one]⟩
  · intro ℓ u v huv x hx
    rw [MonoidHom.comp_apply, hψ] at hx
    rw [MonoidHom.comp_apply, hψ, hact ℓ u v huv]
    exact hφθ (ρ.rangeRestrict ℓ) _ x hx

end Glue

section Main

variable {G : Type} [Group G] [Finite G]

open Subgroup in
theorem isTypeScriptL_of_transvectionData {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (ht : TransvectionData S L) (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L)
    (hZ : Subgroup.center ↥(barM X L) = ⊥) : IsTypeScriptL L := by
  obtain ⟨s, hsS, hgen, hsn, hZs⟩ := ht
  have hset := TransvIrr.setting_of hX hA hL hsS hgen hsn hZs
  have hSL := CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨W, _, _, _, _, cls, ρ, hadd, hsurj, hclsker, hact, hirr, htr, hgenρ, hM, hperf, hL1,
      hs, hC⟩ :=
    TransvIrr.exists_rep_data_of_setting hset hV2 hsn
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hX hA hL hTM hMT hCT hx hxn)
  have hUeq := blockU_eq_commutator_blockV hSL hL.perfect hset hQV
  have hZeq := blockZ_eq_of_blockU_eq (S := S) hUeq
  let ρL : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2) W := ρ.comp (Subgroup.inclusion hset.le)
  let e : blockU L ≃* ↥⁅blockV S L, L⁆ := MulEquiv.subgroupCongr hUeq
  let clsHom : ↥⁅blockV S L, L⁆ →* Multiplicative W :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (cls u)) fun a b => hadd a b
  have hρL : HasModuleRep L ρL := by
    refine ⟨clsHom.comp e.toMonoidHom, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd y)
      exact ⟨e.symm u, by
        change Multiplicative.ofAdd (cls (e (e.symm u))) = y
        rw [e.apply_symm_apply, hu]
        rfl⟩
    · ext u
      have h1 := hclsker (e u)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hZeq]
      change Multiplicative.ofAdd (cls (e u)) = 1 ↔ _
      rw [ofAdd_eq_one]
      exact h1
    · intro ℓ u v huv
      exact (hact (Subgroup.inclusion hset.le ℓ) (e u) (e v) huv).symm
  have hq := hL.component.2.2
  have hpk : CFSG.pCore 2 ↥L ≤ ρL.ker := by
    intro q hq'
    rw [MonoidHom.mem_ker]
    refine Units.ext (LinearMap.ext fun w => ?_)
    obtain ⟨u, rfl⟩ := hsurj w
    have hqQ : (q : G) ∈ pCoreOf 2 (L ⊔ S) :=
      pCoreOf_le_pCoreOf_sup hSL (mem_pCoreOf_of_mem_pCore hq')
    have hc := commute_of_mem_pCoreOf_blockV hqQ (hset.U_le_V u.2)
    have huq : (u : G) = ((Subgroup.inclusion hset.le q : ↥(L ⊔ S)) : G) * (u : G) *
        ((Subgroup.inclusion hset.le q : ↥(L ⊔ S)) : G)⁻¹ := by
      show (u : G) = (q : G) * u * (q : G)⁻¹
      rw [hc]
      group
    exact hact (Subgroup.inclusion hset.le q) u u huq
  have hne : ρL.ker ≠ ⊤ := by
    intro htop
    apply hL1
    intro x hx
    have h1 : (⟨(x : G), hx⟩ : ↥L) ∈ ρL.ker := by rw [htop]; exact Subgroup.mem_top _
    have e1 : Subgroup.inclusion hset.le ⟨(x : G), hx⟩ = x := Subtype.ext rfl
    rw [MonoidHom.mem_ker] at h1 ⊢
    rw [← e1]
    exact h1
  have hk : ρL.ker = CFSG.pCore 2 ↥L :=
    ker_eq_pCore_of_quasisimple hL.le hq hZ ρL hpk hne
  have : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr hset.normL
  have hmodel := models_of_transvection_rep ρ (L.subgroupOf (L ⊔ S)) ⟨s, hset.mem⟩ hirr htr
    hgenρ hM hperf hL1 hs
  have hrange : ρL.range = (L.subgroupOf (L ⊔ S)).map ρ := by
    ext y
    constructor
    · rintro ⟨ℓ, rfl⟩
      exact ⟨Subgroup.inclusion hset.le ℓ, Subgroup.mem_subgroupOf.mpr ℓ.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  rw [← hrange] at hmodel
  rcases hmodel with ⟨m, φ, h1, h2⟩ | ⟨m, φ, h1, h2⟩ | ⟨m, hm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨m, exists_typeData_of_model (omegaPlusTwo m) hρL hk φ h1 h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, exists_typeData_of_model (omegaMinusTwo m) hρL hk φ h1 h2⟩)))
  · exact Or.inr (Or.inl ⟨m, isAltNaturalType_of_model hρL hk hm⟩)

end Main

end CFSG.HardMathSupport.Cooperstein.StructureLie
