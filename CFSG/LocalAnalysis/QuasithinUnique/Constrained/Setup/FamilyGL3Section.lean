module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Normalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.ComponentClassification Matrix
open scoped commutatorElement

section Transport

variable {E W : Type*} [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def linConj (Φ : E ≃ₗ[ZMod 2] W) : (E ≃ₗ[ZMod 2] E) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun f := Φ.symm.trans (f.trans Φ)
  invFun f := Φ.trans (f.trans Φ.symm)
  left_inv f := LinearEquiv.ext fun x => by simp
  right_inv f := LinearEquiv.ext fun x => by simp
  map_mul' f g := LinearEquiv.ext fun x => by simp

theorem GoodRep.conj {ρ : H32 →* (E ≃ₗ[ZMod 2] E)} (hρ : GoodRep ρ) (Φ : E ≃ₗ[ZMod 2] W) :
    GoodRep ((linConj Φ).toMonoidHom.comp ρ) where
  faithful := (linConj Φ).injective.comp hρ.faithful
  centralizer φ h := by
    have h1 : (linConj Φ).symm φ = 1 := by
      apply hρ.centralizer
      intro g
      apply (linConj Φ).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h g
    have h2 := congrArg (linConj Φ) h1
    rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem false_of_modIso [Finite W] {ρH : H32 →* (E ≃ₗ[ZMod 2] E)} (hρ : GoodRep ρH)
    {ρS : GL32 →* (W ≃ₗ[ZMod 2] W)} (hiso : ModIso (ρH.comp sIncl) ρS)
    {Ā : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hn : ∀ a ∈ Ā, ∀ g : GL32, ∃ g' : GL32, a * ρS g * a⁻¹ = ρS g')
    (h0 : Ā ≠ ⊥) (hcomm : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a) (hsq : ∀ a ∈ Ā, a ^ 2 = 1)
    (hoff : Nat.card W ≤
      Nat.card Ā * Nat.card (fixedSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) Ā)) : False := by
  obtain ⟨Φ, hΦ⟩ := hiso
  have hρW := hρ.conj Φ
  have hS : ∀ g : GL32, ((linConj Φ).toMonoidHom.comp ρH) (sIncl g) = ρS g := by
    intro g
    refine LinearEquiv.ext fun w => ?_
    show Φ (ρH (sIncl g) (Φ.symm w)) = ρS g w
    have h1 := hΦ g (Φ.symm w)
    simp only [MonoidHom.comp_apply] at h1
    rw [h1, LinearEquiv.apply_symm_apply]
  have hn' : ∀ a ∈ Ā, ∀ g : GL32, ∃ g' : GL32,
      a * ((linConj Φ).toMonoidHom.comp ρH) (sIncl g) * a⁻¹ =
        ((linConj Φ).toMonoidHom.comp ρH) (sIncl g') := by
    intro a ha g
    obtain ⟨g', hg'⟩ := hn a ha g
    exact ⟨g', by rw [hS, hS]; exact hg'⟩
  have := hρW.excludes hn' h0 hcomm hsq
  omega

end Transport

section Sections

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}

@[expose] noncomputable def secRep (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) :
    GL32 →* ((↥I ⧸ Layer.fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ Layer.fixIn L I)) :=
  (Layer.actOn L A I hAn hI L le_sup_left).comp e.toMonoidHom

theorem secRep_range (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) :
    (secRep e hAn hI).range = Lift.Lbar L A I hAn hI := by
  unfold secRep Lift.Lbar
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective]
  exact (MonoidHom.range_eq_map _).symm

theorem secRep_isIrr (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (hirr : Layer.IsIrrQuot (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L I) :
    IsIrrRep (secRep e hAn hI) := by
  obtain ⟨hnt, hirr'⟩ := Lift.lbar_irreducible hAn hI hirr
  refine ⟨hnt, fun g => map_zero _, fun N hN => hirr' N fun x hx u hu => ?_⟩
  rw [← secRep_range e hAn hI] at hx
  obtain ⟨g, rfl⟩ := hx
  exact hN g u hu

theorem secRep_normalizes (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    {a : (↥I ⧸ Layer.fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ Layer.fixIn L I)}
    (ha : a ∈ Lift.Abar L A I hAn hI) (g : GL32) :
    ∃ g' : GL32, a * secRep e hAn hI g * a⁻¹ = secRep e hAn hI g' := by
  have hmem := Lift.abar_le_normalizer_lbar hAn hI ha
  have hg : secRep e hAn hI g ∈ Lift.Lbar L A I hAn hI := by
    rw [← secRep_range e hAn hI]
    exact ⟨g, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hmem (secRep e hAn hI g)).1 hg
  rw [← secRep_range e hAn hI] at h1
  obtain ⟨g', hg'⟩ := h1
  exact ⟨g', hg'.symm⟩

theorem false_of_section_Q [Finite V] (e : GL32 ≃* ↥L) (hcs : Layer.ComponentSection L A I)
    (hiso : ModIso repA
      (secRep e hcs.A_norm (Layer.isInvariant_sup_subgroup hcs.inv_L hcs.inv_A))) :
    False := by
  have hLA := Layer.isInvariant_sup_subgroup hcs.inv_L hcs.inv_A
  have : Finite ↥I := inferInstance
  have : Finite (↥I ⧸ Layer.fixIn L I) := inferInstance
  refine false_of_modIso (ρH := repQ) goodRep_repQ (Ā := Lift.Abar L A I hcs.A_norm hLA)
    (by rw [repQ_comp_sIncl]; exact hiso) (fun a ha g => secRep_normalizes e hcs.A_norm hLA ha g)
    hcs.Abar_ne
    (fun a ha b hb => Layer.Actor.comm_of_isElementaryAbelian_two hcs.Abar_elem a ha b hb)
    (fun a ha => Layer.Actor.sq_of_isElementaryAbelian_two hcs.Abar_elem a ha) ?_
  exact hcs.Abar_off

end Sections

section SectionOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {X : Submodule (ZMod 2) V}

local notation "ρ₀" => MonoidHom.id (V ≃ₗ[ZMod 2] V)

omit [Finite V] in
theorem section_Lbar_ne
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hLA : Offender.IsInvariant ρ₀ (L ⊔ A) X) (hXc : Offender.commSub ρ₀ L X = X)
    (hXnt : ¬ X ≤ Offender.fixSub ρ₀ L) :
    (Layer.actOn L A X hAn hLA L le_sup_left).range ≠ ⊥ := by
  intro h
  have h1 : Layer.actOn L A X hAn hLA L le_sup_left = 1 := MonoidHom.range_eq_bot_iff.1 h
  apply hXnt
  calc X = Offender.commSub ρ₀ L X := hXc.symm
    _ ≤ Offender.fixSub ρ₀ L := by
      rw [Layer.commSub_le_iff]
      intro l hl u hu
      have h2 : Layer.actW L A X hAn hLA ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by
        have := congrArg (fun φ => φ ⟨l, hl⟩) h1
        exact this
      exact Layer.disp_mem_fix_of_actW_eq_one hAn hLA h2 u hu

omit [Finite V] in
theorem section_Abar_ne
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hLA : Offender.IsInvariant ρ₀ (L ⊔ A) X) (hLperf : ⁅L, A⁆ = L)
    (hLbar_ne : (Layer.actOn L A X hAn hLA L le_sup_left).range ≠ ⊥) :
    (Layer.actOn L A X hAn hLA A le_sup_right).range ≠ ⊥ := by
  intro h
  have h1 : Layer.actOn L A X hAn hLA A le_sup_right = 1 := MonoidHom.range_eq_bot_iff.1 h
  apply hLbar_ne
  rw [MonoidHom.range_eq_bot_iff]
  have hLle' : ⁅L, A⁆ ≤ (Layer.actW L A X hAn hLA).ker.map (L ⊔ A).subtype := by
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h2 : Layer.actW L A X hAn hLA ⟨a, Subgroup.mem_sup_right ha⟩ = 1 := by
      have := congrArg (fun φ => φ ⟨a, ha⟩) h1
      exact this
    have hmem : ⁅(⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L ⊔ A)), ⟨a, Subgroup.mem_sup_right ha⟩⁆ ∈
        (Layer.actW L A X hAn hLA).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, h2, commutatorElement_one_right]
    exact ⟨_, hmem, rfl⟩
  have hLle : L ≤ (Layer.actW L A X hAn hLA).ker.map (L ⊔ A).subtype :=
    (le_of_eq hLperf.symm).trans hLle'
  refine MonoidHom.ext fun ⟨l, hl⟩ => ?_
  obtain ⟨y, hy, hyl⟩ := hLle hl
  have : y = ⟨l, Subgroup.mem_sup_left hl⟩ := Subtype.ext hyl
  rw [this] at hy
  exact MonoidHom.mem_ker.1 hy

theorem section_offender
    (hno : Offender.NoPQuotient 2 ↥L) (hch : Offender.CentralPChief 2 ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hmax : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ A →
      Offender.weight ρ₀ B ≤ Offender.weight ρ₀ A)
    (hXL : Offender.IsInvariant ρ₀ L X) (hXA : Offender.IsInvariant ρ₀ A X)
    (hLA : Offender.IsInvariant ρ₀ (L ⊔ A) X) (hXc : Offender.commSub ρ₀ L X = X) :
    (∀ x : ↥(L ⊔ A), Layer.actW L A X hAn hLA x = 1 →
      Layer.resSub ρ₀ (L ⊔ A) X hLA x = 1) ∧
    Nat.card (↥X ⧸ Layer.fixIn L X) ≤
      Offender.weight (MonoidHom.id ((↥X ⧸ Layer.fixIn L X) ≃ₗ[ZMod 2] _))
        (Layer.actOn L A X hAn hLA A le_sup_right).range := by
  have hX : L ⊔ A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)) :=
    sup_le Subgroup.le_normalizer hAn
  have hinj : ∀ x : ↥(L ⊔ A), Layer.actW L A X hAn hLA x = 1 →
      Layer.resSub ρ₀ (L ⊔ A) X hLA x = 1 := by
    intro x hx
    have key := Layer.detect_of_trivial_mod ρ₀ L (L ⊔ A) hX hno hch X hXL hLA hXc x.2
      (Layer.disp_mem_fix_of_actW_eq_one hAn hLA hx)
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [Layer.resSub_apply]
    exact key w w.2
  refine ⟨hinj, ?_⟩
  let AX := (Layer.resSub ρ₀ A X hXA).range
  have h1 : Nat.card ↥X ≤ Offender.weight (MonoidHom.id (↥X ≃ₗ[ZMod 2] ↥X)) AX :=
    Layer.natCard_le_weight_res ρ₀ A X hXA hmax
  let ρ' : ↥AX →* (↥X ≃ₗ[ZMod 2] ↥X) := (MonoidHom.id (↥X ≃ₗ[ZMod 2] ↥X)).comp AX.subtype
  have hρ'w : Offender.weight ρ' ⊤ = Offender.weight (MonoidHom.id (↥X ≃ₗ[ZMod 2] ↥X)) AX := by
    show Offender.weight ((MonoidHom.id (↥X ≃ₗ[ZMod 2] ↥X)).comp AX.subtype) ⊤ = _
    rw [Layer.weight_comp_subtype, Layer.map_subtype_top]
  have hZ' : ∀ x : ↥AX, ∀ z ∈ Layer.fixIn L X, ρ' x z ∈ Layer.fixIn L X := by
    rintro ⟨_, a, rfl⟩ z hz
    exact Layer.fixIn_invariant hAn hXA a z hz
  have h2 := Layer.natCard_quotient_le_weight ρ' (Layer.fixIn L X) hZ' (by rw [hρ'w]; exact h1)
  let π := Layer.quotHom ρ' (Layer.fixIn L X) hZ'
  let s : ↥A →* ↥AX := (Layer.resSub ρ₀ A X hXA).rangeRestrict
  have hs : Function.Surjective s := MonoidHom.rangeRestrict_surjective _
  have hcomp : π.comp s = Layer.actOn L A X hAn hLA A le_sup_right := by
    refine MonoidHom.ext fun a => LinearEquiv.ext fun w => ?_
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [MonoidHom.comp_apply, Layer.quotHom_mk, Layer.actOn_A_mk hAn hXL hXA a u]
    rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨a, rfl⟩ := hs y
    have h3 : Layer.actW L A X hAn hLA ⟨a, Subgroup.mem_sup_right a.2⟩ = 1 := by
      have h4 : (π.comp s) a = 1 := hy
      rw [hcomp] at h4
      exact h4
    have h5 := hinj _ h3
    rw [Layer.resSub_sup_A hXL hXA] at h5
    exact Subtype.ext h5
  have hrange : π.range = (Layer.actOn L A X hAn hLA A le_sup_right).range := by
    rw [← hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs]
    exact MonoidHom.range_eq_map π
  calc Nat.card (↥X ⧸ Layer.fixIn L X) ≤ Offender.weight π ⊤ := h2
    _ = Offender.weight (MonoidHom.id ((↥X ⧸ Layer.fixIn L X) ≃ₗ[ZMod 2] _)) π.range :=
      (Layer.weight_range_of_injective π hπinj).symm
    _ = _ := by rw [hrange]

end SectionOffender

section Pair

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I J X : Submodule (ZMod 2) V}

local notation "ρ₀" => MonoidHom.id (V ≃ₗ[ZMod 2] V)

@[expose] noncomputable def secIncl (hIX : I ≤ X) :
    (↥I ⧸ Layer.fixIn L I) →ₗ[ZMod 2] (↥X ⧸ Layer.fixIn L X) :=
  Submodule.mapQ (Layer.fixIn L I) (Layer.fixIn L X) (Submodule.inclusion hIX)
    (fun _ hw l hl => hw l hl)

theorem secIncl_mk (hIX : I ≤ X) (u : ↥I) :
    secIncl (L := L) hIX (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (Submodule.inclusion hIX u) := rfl

theorem secIncl_injective (hIX : I ≤ X) : Function.Injective (secIncl (L := L) hIX) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [secIncl_mk, Submodule.Quotient.mk_eq_zero] at hw
  rw [Submodule.Quotient.mk_eq_zero]
  intro l hl
  exact hw l hl

theorem secIncl_equivariant (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant ρ₀ (L ⊔ A) I) (hX : Offender.IsInvariant ρ₀ (L ⊔ A) X)
    (hIX : I ≤ X) (g : GL32) (w : ↥I ⧸ Layer.fixIn L I) :
    secRep e hAn hX g (secIncl hIX w) = secIncl hIX (secRep e hAn hI g w) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  unfold secRep
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, secIncl_mk, Lift.actOn_L_mk hAn hX,
    Lift.actOn_L_mk hAn hI, secIncl_mk]
  congr 1

theorem modIso_repPS_of_pair (e : GL32 ≃* ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant ρ₀ (L ⊔ A) I) (hJ : Offender.IsInvariant ρ₀ (L ⊔ A) J)
    (hX : Offender.IsInvariant ρ₀ (L ⊔ A) (I ⊔ J))
    (hIty : ModIso repV (secRep e hAn hI)) (hJty : ModIso repDual (secRep e hAn hJ)) :
    ModIso repPS (secRep e hAn hX) := by
  obtain ⟨Φi, hΦi0⟩ := hIty
  obtain ⟨Φj, hΦj0⟩ := hJty
  have hΦi : ∀ g v, Φi (repV g v) = secRep e hAn hI g (Φi v) := hΦi0
  have hΦj : ∀ g v, Φj (repDual g v) = secRep e hAn hJ g (Φj v) := hΦj0
  have hirrI : IsIrrRep (secRep e hAn hI) :=
    IsIrrAct.of_actIso ⟨Φi, hΦi0⟩ isIrr_repV
  have hirrJ : IsIrrRep (secRep e hAn hJ) :=
    IsIrrAct.of_actIso ⟨Φj, hΦj0⟩ isIrr_repDual
  let ι : (↥I ⧸ Layer.fixIn L I) →ₗ[ZMod 2] (↥(I ⊔ J) ⧸ Layer.fixIn L (I ⊔ J)) :=
    secIncl (le_sup_left : I ≤ I ⊔ J)
  let ι' : (↥J ⧸ Layer.fixIn L J) →ₗ[ZMod 2] (↥(I ⊔ J) ⧸ Layer.fixIn L (I ⊔ J)) :=
    secIncl (le_sup_right : J ≤ I ⊔ J)
  have hι : Function.Injective ι := secIncl_injective _
  have hι' : Function.Injective ι' := secIncl_injective _
  have eqι : ∀ g w, secRep e hAn hX g (ι w) = ι (secRep e hAn hI g w) :=
    secIncl_equivariant e hAn hI hX _
  have eqι' : ∀ g w, secRep e hAn hX g (ι' w) = ι' (secRep e hAn hJ g w) :=
    secIncl_equivariant e hAn hJ hX _
  let Ψ : P6 →ₗ[ZMod 2] (↥(I ⊔ J) ⧸ Layer.fixIn L (I ⊔ J)) :=
    (ι ∘ₗ (Φi : _ →ₗ[ZMod 2] _)).coprod (ι' ∘ₗ (Φj : _ →ₗ[ZMod 2] _))
  have hΨ : ∀ p : P6, Ψ p = ι (Φi p.1) + ι' (Φj p.2) := fun p => rfl
  have eqΨ : ∀ g p, Ψ (repPS g p) = secRep e hAn hX g (Ψ p) := by
    intro g p
    rw [hΨ, hΨ, map_add, eqι, eqι', repPS_apply]
    show ι (Φi (repV g p.1)) + ι' (Φj (repDual g p.2)) = _
    rw [hΦi, hΦj]
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hu
    have h0 : ι (Φi u) + ι' (Φj w) = 0 := hu
    have h1 : ι (Φi u) = ι' (Φj w) := by
      calc ι (Φi u) = ι (Φi u) + (ι' (Φj w) + ι' (Φj w)) := by
            rw [add_self_eq_zero_of_zmod_two, add_zero]
        _ = (ι (Φi u) + ι' (Φj w)) + ι' (Φj w) := by rw [add_assoc]
        _ = ι' (Φj w) := by rw [h0, zero_add]
    let K : Submodule (ZMod 2) (↥I ⧸ Layer.fixIn L I) := (LinearMap.range ι').comap ι
    have hK : ∀ g x, x ∈ K → secRep e hAn hI g x ∈ K := by
      intro g x hx
      obtain ⟨b, hb⟩ := hx
      refine ⟨secRep e hAn hJ g b, ?_⟩
      show ι' (secRep e hAn hJ g b) = ι (secRep e hAn hI g x)
      rw [← eqι', ← eqι, ← hb]
    have ha0 : Φi u = 0 := by
      rcases hirrI.2.2 K hK with hbot | htop
      · have hmem : Φi u ∈ K := ⟨Φj w, h1.symm⟩
        rw [hbot] at hmem
        exact (Submodule.mem_bot _).1 hmem
      · exfalso
        have hall : ∀ a, ι a ∈ LinearMap.range ι' := fun a => by
          have : a ∈ K := by rw [htop]; trivial
          exact this
        obtain ⟨gl, hgl⟩ := LinearMap.exists_leftInverse_of_injective ι'
          (LinearMap.ker_eq_bot.2 hι')
        let θ : (↥I ⧸ Layer.fixIn L I) →ₗ[ZMod 2] (↥J ⧸ Layer.fixIn L J) := gl ∘ₗ ι
        have hθ : ∀ a, ι' (θ a) = ι a := fun a => by
          obtain ⟨c, hc⟩ := hall a
          show ι' (gl (ι a)) = ι a
          rw [← hc, ← LinearMap.comp_apply gl ι', hgl]
          rfl
        have hθeq : IsEquivAct (fun g x => secRep e hAn hI g x) (fun g x => secRep e hAn hJ g x)
            θ := by
          intro g a
          show θ (secRep e hAn hI g a) = secRep e hAn hJ g (θ a)
          apply hι'
          calc ι' (θ (secRep e hAn hI g a)) = ι (secRep e hAn hI g a) := hθ _
            _ = secRep e hAn hX g (ι a) := (eqι g a).symm
            _ = secRep e hAn hX g (ι' (θ a)) := by rw [hθ]
            _ = ι' (secRep e hAn hJ g (θ a)) := eqι' g _
        have hθ0 : θ ≠ 0 := by
          intro h
          have hnt : Nontrivial (↥I ⧸ Layer.fixIn L I) := hirrI.1
          obtain ⟨a, ha⟩ := exists_ne (0 : ↥I ⧸ Layer.fixIn L I)
          apply ha
          apply hι
          rw [← hθ, h]
          simp
        have hbij := hirrI.bijective_of_ne_zero hirrJ hθeq hθ0
        refine not_modIso_repV_repDual ⟨Φi.trans ((LinearEquiv.ofBijective θ hbij).trans Φj.symm),
          fun g v => ?_⟩
        have hΦj' : ∀ g y, Φj.symm (secRep e hAn hJ g y) = repDual g (Φj.symm y) := by
          intro g y
          apply Φj.injective
          rw [LinearEquiv.apply_symm_apply]
          have h2 := hΦj g (Φj.symm y)
          rw [LinearEquiv.apply_symm_apply] at h2
          exact h2.symm
        show Φj.symm (θ (Φi (repV g v))) = repDual g (Φj.symm (θ (Φi v)))
        rw [hΦi g v]
        have h3 : θ (secRep e hAn hI g (Φi v)) = secRep e hAn hJ g (θ (Φi v)) := hθeq g (Φi v)
        rw [h3, hΦj']
    have hb0 : Φj w = 0 := by
      have : ι' (Φj w) = ι' 0 := by rw [← h1, ha0, map_zero, map_zero]
      exact hι' this
    refine Prod.ext ?_ ?_
    · exact (Φi.map_eq_zero_iff).1 ha0
    · exact (Φj.map_eq_zero_iff).1 hb0
  have hsurj : Function.Surjective Ψ := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 x.2
    refine ⟨(Φi.symm (Submodule.Quotient.mk ⟨i, hi⟩), Φj.symm (Submodule.Quotient.mk ⟨j, hj⟩)),
      ?_⟩
    rw [hΨ]
    show ι (Φi (Φi.symm (Submodule.Quotient.mk ⟨i, hi⟩))) +
      ι' (Φj (Φj.symm (Submodule.Quotient.mk ⟨j, hj⟩))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    show Submodule.Quotient.mk (Submodule.inclusion le_sup_left ⟨i, hi⟩) +
      Submodule.Quotient.mk (Submodule.inclusion le_sup_right ⟨j, hj⟩) = _
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hij
  refine ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun g p => ?_⟩
  exact eqΨ g p

end Pair

section NatDual

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I J : Submodule (ZMod 2) V}

local notation "ρ₀" => MonoidHom.id (V ≃ₗ[ZMod 2] V)

theorem false_of_natDual (e : GL32 ≃* ↥L)
    (hno : Offender.NoPQuotient 2 ↥L) (hch : Offender.CentralPChief 2 ↥L)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hLperf : ⁅L, A⁆ = L)
    (hmax : ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ A →
      Offender.weight ρ₀ B ≤ Offender.weight ρ₀ A)
    (hI : Layer.IsGoodModule ρ₀ L I) (hJ : Layer.IsGoodModule ρ₀ L J)
    (hIA : Offender.IsInvariant ρ₀ A I) (hJA : Offender.IsInvariant ρ₀ A J)
    (hIty : ModIso repV (secRep e hAn (Layer.isInvariant_sup_subgroup hI.inv hIA)))
    (hJty : ModIso repDual (secRep e hAn (Layer.isInvariant_sup_subgroup hJ.inv hJA))) :
    False := by
  have hLAI := Layer.isInvariant_sup_subgroup hI.inv hIA
  have hLAJ := Layer.isInvariant_sup_subgroup hJ.inv hJA
  have hXL : Offender.IsInvariant ρ₀ L (I ⊔ J) := Layer.isInvariant_sup' hI.inv hJ.inv
  have hXA : Offender.IsInvariant ρ₀ A (I ⊔ J) := Layer.isInvariant_sup' hIA hJA
  have hLAX := Layer.isInvariant_sup_subgroup hXL hXA
  have hXc : Offender.commSub ρ₀ L (I ⊔ J) = I ⊔ J := by
    rw [Layer.commSub_sup, hI.comm, hJ.comm]
  have hXnt : ¬ (I ⊔ J) ≤ Offender.fixSub ρ₀ L := fun h => hI.irr.1 (le_sup_left.trans h)
  obtain ⟨-, hoff⟩ := section_offender hno hch hAn hmax hXL hXA hLAX hXc
  have hLbar := section_Lbar_ne hAn hLAX hXc hXnt
  have hAbar := section_Abar_ne hAn hLAX hLperf hLbar
  have hiso := modIso_repPS_of_pair e hAn hLAI hLAJ hLAX hIty hJty
  have hel : CFSG.IsElementaryAbelian 2 ↥(Lift.Abar L A (I ⊔ J) hAn hLAX) :=
    Layer.isElementaryAbelian_range _ hAel
  have : Finite ↥(I ⊔ J) := inferInstance
  have : Finite (↥(I ⊔ J) ⧸ Layer.fixIn L (I ⊔ J)) := inferInstance
  exact false_of_modIso (ρH := repP) goodRep_repP (Ā := Lift.Abar L A (I ⊔ J) hAn hLAX)
    (by rw [repP_comp_sIncl]; exact hiso) (fun a ha g => secRep_normalizes e hAn hLAX ha g)
    hAbar (fun a ha b hb => Layer.Actor.comm_of_isElementaryAbelian_two hel a ha b hb)
    (fun a ha => Layer.Actor.sq_of_isElementaryAbelian_two hel a ha) hoff

end NatDual

end CFSG.QuasithinUnique.Setup.Family
