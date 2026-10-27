module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOuterCharacter
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoNativeActor
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Cover
public import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactor
public import CFSG.LocalAnalysis.ComponentInitial.BlockTwoFactorSylowShape
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.StandardType.TwE6KG7 CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap CFSG.StandardType.GGQ2Frame.ExcPlacement
open CFSG.EvenSmallLie.TwoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PerfectCover
open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

section CenterQuotient

variable {H C : Type*} [Group H] [Group C]

noncomputable def centerQuotientEquivOfSurjective
    (ψ : H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center H) : H ⧸ Subgroup.center H ≃* C :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ)

theorem centerQuotientEquivOfSurjective_apply_mk
    (ψ : H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center H) (l : H) :
    centerQuotientEquivOfSurjective ψ hψ hker
      (QuotientGroup.mk' (Subgroup.center H) l) = ψ l := by
  simp only [centerQuotientEquivOfSurjective, MulEquiv.trans_apply]
  change (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ)
    (QuotientGroup.mk' ψ.ker l) = ψ l
  rfl

end CenterQuotient

section QuotientAction

variable {G : Type} [Group G] {H E : Subgroup G} {C : Type*} [Group C]

noncomputable def originalQuotientAction
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥H) : ↥E →* MulAut C :=
  (MulAut.congr (centerQuotientEquivOfSurjective ψ hψ hker)).toMonoidHom.comp
    (quotientActionHom H hEN)

theorem originalQuotientAction_apply_mk
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥H) (e : ↥E) (l : ↥H) :
    originalQuotientAction hEN ψ hψ hker e (ψ l) = ψ (ggGamma H hEN e l) := by
  let eC := centerQuotientEquivOfSurjective ψ hψ hker
  have hsymm : eC.symm (ψ l) = QuotientGroup.mk' (Subgroup.center ↥H) l := by
    rw [← centerQuotientEquivOfSurjective_apply_mk ψ hψ hker l, MulEquiv.symm_apply_apply]
  change eC ((quotientActionHom H hEN e) (eC.symm (ψ l))) = ψ (ggGamma H hEN e l)
  rw [hsymm, quotientActionHom_apply_mk]
  exact centerQuotientEquivOfSurjective_apply_mk ψ hψ hker (ggGamma H hEN e l)

theorem originalQuotientAction_eq_of_compatible
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥H) (e : ↥E)
    (φ : MulAut C)
    (hφ : ∀ l : ↥H, φ (ψ l) = ψ (ggGamma H hEN e l)) :
    originalQuotientAction hEN ψ hψ hker e = φ := by
  ext y
  obtain ⟨l, rfl⟩ := hψ y
  rw [originalQuotientAction_apply_mk, hφ l]

theorem originalQuotientAction_of_ggGamma_eq_conj
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥H) (e : ↥E) (x : ↥H)
    (hx : ggGamma H hEN e = MulAut.conj x) :
    originalQuotientAction hEN ψ hψ hker e =
      MulAut.conj (centerQuotientEquivOfSurjective ψ hψ hker
        (QuotientGroup.mk' (Subgroup.center ↥H) x)) := by
  let eC := centerQuotientEquivOfSurjective ψ hψ hker
  ext y
  obtain ⟨l, rfl⟩ := hψ y
  rw [originalQuotientAction_apply_mk, hx, MulAut.conj_apply, MulAut.conj_apply]
  rw [centerQuotientEquivOfSurjective_apply_mk ψ hψ hker x]
  rw [map_mul, map_mul, map_inv]

end QuotientAction

section AdditiveCharacter

variable {G : Type} [Group G] {E : Subgroup G} {B : Subgroup G}

@[expose] noncomputable def originalAdditiveCharacter
    (hBE : B ≤ E) (χ : ↥E →* Multiplicative (ZMod 3)) :
    Additive ↥B →+ ZMod 3 :=
  { toFun := fun a => (χ (Subgroup.inclusion hBE (Additive.toMul a))).toAdd
    map_zero' := by simp
    map_add' := by
      intro a b
      change (χ (Subgroup.inclusion hBE (a + b).toMul)).toAdd =
        (χ (Subgroup.inclusion hBE a.toMul)).toAdd +
          (χ (Subgroup.inclusion hBE b.toMul)).toAdd
      rw [show (a + b).toMul = a.toMul * b.toMul from rfl]
      simp [map_mul] }

@[simp] theorem originalAdditiveCharacter_apply
    (hBE : B ≤ E) (χ : ↥E →* Multiplicative (ZMod 3)) (a : Additive ↥B) :
    originalAdditiveCharacter hBE χ a =
      (χ (Subgroup.inclusion hBE (Additive.toMul a))).toAdd := rfl

end AdditiveCharacter

section LinearCharacter

variable {G : Type} [Group G] {E : Subgroup G} {B : Subgroup G}
  [Fact (CFSG.Open.IsElemAbelian 3 B)]

local instance : IsMulCommutative ↥B :=
  (Fact.out (p := CFSG.Open.IsElemAbelian 3 B)).1

local instance : CommGroup ↥B := IsMulCommutative.instCommGroup

local instance : Module (ZMod 3) (Additive ↥B) :=
  AddCommGroup.zmodModule (n := 3) fun a => by
    have h : (Additive.toMul a) ^ 3 = 1 :=
      Subtype.ext ((Fact.out (p := CFSG.Open.IsElemAbelian 3 B)).2 _ (Additive.toMul a).2)
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using h

@[expose] noncomputable def originalLinearCharacter
    (hBE : B ≤ E) (χ : ↥E →* Multiplicative (ZMod 3)) :
    Additive ↥B →ₗ[ZMod 3] ZMod 3 :=
  (originalAdditiveCharacter hBE χ).toZModLinearMap 3

@[simp] theorem originalLinearCharacter_apply
    (hBE : B ≤ E) (χ : ↥E →* Multiplicative (ZMod 3)) (a : Additive ↥B) :
    originalLinearCharacter hBE χ a =
      (χ (Subgroup.inclusion hBE (Additive.toMul a))).toAdd := rfl

end LinearCharacter

section CompatibleAction

variable {G : Type} [Group G] {H E : Subgroup G}
  {L : Type} [Field L] [Finite L] (σ : L ≃+* L)

abbrev CompatibleAction
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* twistedE6RootGroup L σ) : Prop :=
  ∀ e : ↥E, ∃ φ ∈ (RecipeExcLang.twConj L σ).range,
    ∀ l : ↥H, φ (ψ l) = ψ (ggGamma H hEN e l)

end CompatibleAction

section NativeAction

attribute [local instance] finite_stdGroup isPerfect_stdGroup

variable {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
  (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)

noncomputable def nativeStdTransport : twistedE6RootGroup L σ ≃* stdGroup :=
  Classical.choose (exists_std_transport_of_card_four hL4 σ hσ)

theorem nativeStdTransport_spec (φ : MulAut (twistedE6RootGroup L σ)) :
    φ ∈ (RecipeExcLang.twConj L σ).range ↔
      MulAut.congr (nativeStdTransport hL4 σ hσ) φ ∈ nativeTwConj :=
  Classical.choose_spec (exists_std_transport_of_card_four hL4 σ hσ) φ

variable {G : Type} [Group G] {H E : Subgroup G}

variable (hEN : E ≤ Subgroup.normalizer (H : Set G))
  (ψ : ↥H →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
  (hker : ψ.ker = Subgroup.center ↥H)

noncomputable def originalStdAction : ↥E →* MulAut ↥stdGroup :=
  (MulAut.congr (nativeStdTransport hL4 σ hσ)).toMonoidHom.comp
    (originalQuotientAction hEN ψ hψ hker)

theorem originalStdAction_apply_mk (e : ↥E) (l : ↥H) :
    originalStdAction hL4 σ hσ hEN ψ hψ hker e
      (nativeStdTransport hL4 σ hσ (ψ l)) =
    nativeStdTransport hL4 σ hσ (ψ (ggGamma H hEN e l)) := by
  change nativeStdTransport hL4 σ hσ
    (originalQuotientAction hEN ψ hψ hker e
      ((nativeStdTransport hL4 σ hσ).symm (nativeStdTransport hL4 σ hσ (ψ l)))) = _
  rw [MulEquiv.symm_apply_apply, originalQuotientAction_apply_mk]

theorem originalStdAction_mem_nativeTwConj
    (hact : CompatibleAction σ hEN ψ) (e : ↥E) :
    originalStdAction hL4 σ hσ hEN ψ hψ hker e ∈ nativeTwConj := by
  obtain ⟨φ, hφmem, hφeq⟩ := hact e
  have hEq : originalQuotientAction hEN ψ hψ hker e = φ :=
    originalQuotientAction_eq_of_compatible hEN ψ hψ hker e φ hφeq
  change MulAut.congr (nativeStdTransport hL4 σ hσ)
    (originalQuotientAction hEN ψ hψ hker e) ∈ nativeTwConj
  rw [hEq]
  exact (nativeStdTransport_spec hL4 σ hσ φ).1 hφmem

noncomputable def originalNativeAction
    (hact : CompatibleAction σ hEN ψ) : ↥E →* nativeTwConj :=
  (originalStdAction hL4 σ hσ hEN ψ hψ hker).codRestrict nativeTwConj
    (originalStdAction_mem_nativeTwConj hL4 σ hσ hEN ψ hψ hker hact)

noncomputable def originalOuterCharacter
    (hact : CompatibleAction σ hEN ψ)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    ↥E →* Multiplicative (ZMod 3) :=
  (outerCharacter P Q3).comp
    (originalNativeAction hL4 σ hσ hEN ψ hψ hker hact)

theorem originalOuterCharacter_ne_one_iff_of_compatible
    (hact : CompatibleAction σ hEN ψ)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (e : ↥E) (φ : MulAut (twistedE6RootGroup L σ))
    (_hφmem : φ ∈ (RecipeExcLang.twConj L σ).range)
    (hφeq : ∀ l : ↥H, φ (ψ l) = ψ (ggGamma H hEN e l)) :
    originalOuterCharacter hL4 σ hσ hEN ψ hψ hker hact P Q3 e ≠ 1 ↔
      φ ∉ twistedE6Inn L σ := by
  have hEq : originalQuotientAction hEN ψ hψ hker e = φ :=
    originalQuotientAction_eq_of_compatible hEN ψ hψ hker e φ hφeq
  change outerCharacter P Q3
    (originalNativeAction hL4 σ hσ hEN ψ hψ hker hact e) ≠ 1 ↔ _
  rw [outerCharacter_ne_one_iff]
  change MulAut.congr (nativeStdTransport hL4 σ hσ)
    (originalQuotientAction hEN ψ hψ hker e) ∉ nativeInn ↔ _
  rw [hEq]
  exact not_congr (congr_mem_inner_iff σ (nativeStdTransport hL4 σ hσ) φ)

theorem originalOuterCharacter_eq_one_of_ggGamma_mem_inner
    (hact : CompatibleAction σ hEN ψ)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (e : ↥E)
    (hinner : ggGamma H hEN e ∈
      (MulAut.conj : ↥H →* MulAut ↥H).range) :
    originalOuterCharacter hL4 σ hσ hEN ψ hψ hker hact P Q3 e = 1 := by
  obtain ⟨x, hx⟩ := hinner
  have hq := originalQuotientAction_of_ggGamma_eq_conj hEN ψ hψ hker e x hx.symm
  apply outerCharacter_eq_one_of_mem_inner P Q3
  change MulAut.congr (nativeStdTransport hL4 σ hσ)
    (originalQuotientAction hEN ψ hψ hker e) ∈ nativeInn
  rw [hq, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  exact ⟨nativeStdTransport hL4 σ hσ
    ((centerQuotientEquivOfSurjective ψ hψ hker)
      (QuotientGroup.mk' (Subgroup.center ↥H) x)), rfl⟩
end NativeAction

section CoverSupplier

set_option linter.style.haveILetI false

structure ExcTwE6CoverData
    {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 E H) where
  hEN : E ≤ Subgroup.normalizer (H : Set G)
  commH : commutator H = ⊤
  K : Type
  fieldK : Field K
  finiteK : Finite K
  σ : K ≃+* K
  hK4 : Nat.card K = 4
  hσ : ∀ c, σ c = c ^ 2
  ψ : ↥H →* ↥(twistedE6RootGroup K σ)
  hψ : Function.Surjective ψ
  hker : ψ.ker = Subgroup.center ↥H
  hact : CompatibleAction σ hEN ψ

namespace ExcTwE6CoverData

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G}
  {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 E H}

section TwoPartQuotient

open CFSG.GroupTheory CFSG.LieType.Steinberg.Exceptional

noncomputable def stdCover (D : ExcTwE6CoverData hmark) : ↥H →* stdGroup :=
  letI := D.fieldK
  letI := D.finiteK
  (nativeStdTransport D.hK4 D.σ D.hσ).toMonoidHom.comp D.ψ

theorem stdCover_surjective (D : ExcTwE6CoverData hmark) :
    Function.Surjective D.stdCover := by
  letI := D.fieldK
  letI := D.finiteK
  exact (nativeStdTransport D.hK4 D.σ D.hσ).surjective.comp D.hψ

theorem stdCover_ker (D : ExcTwE6CoverData hmark) :
    D.stdCover.ker = Subgroup.center ↥H := by
  letI := D.fieldK
  letI := D.finiteK
  change ((nativeStdTransport D.hK4 D.σ D.hσ).toMonoidHom.comp D.ψ).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ (nativeStdTransport D.hK4 D.σ D.hσ).injective]
  exact D.hker

theorem stdCover_ker_le_center (D : ExcTwE6CoverData hmark) :
    D.stdCover.ker ≤ Subgroup.center ↥H := le_of_eq D.stdCover_ker

noncomputable abbrev twoKernel (D : ExcTwE6CoverData hmark) : Subgroup ↥H :=
  centralTwoKernel D.stdCover_ker_le_center

@[simp] theorem mem_twoKernel (D : ExcTwE6CoverData hmark) (z : ↥H) :
    z ∈ D.twoKernel ↔ z ∈ Subgroup.center ↥H ∧ z ^ 2 = 1 := by
  rw [twoKernel, mem_centralTwoKernel, D.stdCover_ker]

theorem stdCover_action (D : ExcTwE6CoverData hmark) (e : ↥E) (z : ↥H) :
    D.stdCover (ggGamma H D.hEN e z) =
      (letI := D.fieldK
       letI := D.finiteK
       originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e) (D.stdCover z) := by
  letI := D.fieldK
  letI := D.finiteK
  let eC := nativeStdTransport D.hK4 D.σ D.hσ
  change eC (D.ψ (ggGamma H D.hEN e z)) =
    eC (originalQuotientAction D.hEN D.ψ D.hψ D.hker e (eC.symm (eC (D.ψ z))))
  rw [eC.symm_apply_apply, originalQuotientAction_apply_mk]

noncomputable def scMap (D : ExcTwE6CoverData hmark) :
    twistedE6Group 2 1 →* ↥H ⧸ D.twoKernel := by
  letI : Group.IsPerfect ↥H := ⟨D.commH⟩
  exact Classical.choose (exists_sc_map_mod_twoKernel D.stdCover_surjective
    D.stdCover_ker_le_center)

theorem scMap_spec (D : ExcTwE6CoverData hmark) :
    Function.Surjective D.scMap ∧
      D.scMap.ker ≤ Subgroup.center (twistedE6Group 2 1) ∧
      ∀ u, centralTwoQuotientMap D.stdCover_ker_le_center (D.scMap u) = isogenyStd u := by
  letI : Group.IsPerfect ↥H := ⟨D.commH⟩
  exact Classical.choose_spec (exists_sc_map_mod_twoKernel D.stdCover_surjective
    D.stdCover_ker_le_center)

theorem scMap_ker_odd (D : ExcTwE6CoverData hmark) : Odd (Nat.card D.scMap.ker) := by
  have hodd : Odd (Nat.card (Subgroup.center (twistedE6Group 2 1))) := by
    rw [card_center_twistedE6Group]
    decide
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le D.scMap_spec.2.1)

theorem twoKernel_map_ggGamma (D : ExcTwE6CoverData hmark) (e : ↥E) :
    D.twoKernel.map (ggGamma H D.hEN e).toMonoidHom = D.twoKernel := by
  letI := D.fieldK
  letI := D.finiteK
  exact centralTwoKernel_map_eq D.stdCover_ker_le_center (ggGamma H D.hEN e)
    (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e)
    (D.stdCover_action e)

theorem scMap_actor (D : ExcTwE6CoverData hmark) (e : ↥E)
    (β : MulAut (twistedE6Group 2 1))
    (hβ : ∀ u, isogenyStd (β u) =
      (letI := D.fieldK
       letI := D.finiteK
       originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e) (isogenyStd u)) :
    ∀ u, CFSG.GroupTheory.MulAut.quotientNormal (ggGamma H D.hEN e) D.twoKernel
      (D.twoKernel_map_ggGamma e) (D.scMap u) = D.scMap (β u) := by
  letI := D.fieldK
  letI := D.finiteK
  exact sc_map_mod_twoKernel_equivariant D.stdCover_ker_le_center D.scMap
    D.scMap_spec.2.2 (ggGamma H D.hEN e)
    (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e)
    (D.stdCover_action e) β hβ

noncomputable def scAction (D : ExcTwE6CoverData hmark) :
    E →* MulAut (twistedE6Group 2 1) :=
  letI := D.fieldK
  letI := D.finiteK
  scAutHom.comp (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker)

theorem scAction_spec (D : ExcTwE6CoverData hmark) (e : E) (u : twistedE6Group 2 1) :
    isogenyStd (D.scAction e u) =
      (letI := D.fieldK
       letI := D.finiteK
       originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e) (isogenyStd u) := by
  letI := D.fieldK
  letI := D.finiteK
  exact scAutHom_apply _ u

noncomputable abbrev twoKernelInG (D : ExcTwE6CoverData hmark) : Subgroup G :=
  D.twoKernel.map H.subtype

theorem twoKernelInG_isPGroup (D : ExcTwE6CoverData hmark) :
    IsPGroup 2 D.twoKernelInG := by
  have htwo : IsPGroup 2 D.twoKernel := by
    intro z
    refine ⟨1, ?_⟩
    exact Subtype.ext (by simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      using ((D.mem_twoKernel (z : H)).mp z.2).2)
  exact htwo.map H.subtype

theorem twoKernelInG_le (D : ExcTwE6CoverData hmark) : D.twoKernelInG ≤ H :=
  Subgroup.map_subtype_le _

theorem twoKernelInG_le_centralizer (D : ExcTwE6CoverData hmark) :
    D.twoKernelInG ≤ Subgroup.centralizer (H : Set G) := by
  rintro z ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg (fun x : H => (x : G))
    (Subgroup.mem_center_iff.mp ((D.mem_twoKernel a).mp ha).1 ⟨y, hy⟩)

theorem le_normalizer_twoKernelInG (D : ExcTwE6CoverData hmark) :
    E ≤ Subgroup.normalizer (D.twoKernelInG : Set G) := by
  have hclosed (e : E) (z : G) (hz : z ∈ D.twoKernelInG) :
      (e : G) * z * (e : G)⁻¹ ∈ D.twoKernelInG := by
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have hmem : ggGamma H D.hEN e a ∈ D.twoKernel := by
      rw [← D.twoKernel_map_ggGamma e]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨ggGamma H D.hEN e a, hmem, ggGamma_coe (L := H) (hBN := D.hEN) e a⟩
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hclosed ⟨e, he⟩ z
  · intro hz
    have h := hclosed (⟨e, he⟩ : E)⁻¹ (e * z * e⁻¹) hz
    have heq : e⁻¹ * (e * z * e⁻¹) * (e⁻¹)⁻¹ = z := by
      group
    change e⁻¹ * (e * z * e⁻¹) * (e⁻¹)⁻¹ ∈ D.twoKernelInG at h
    rw [heq] at h
    exact h

instance twoKernelInJoin_normal (D : ExcTwE6CoverData hmark) :
    (D.twoKernelInG.subgroupOf (H ⊔ E)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  apply sup_le _ D.le_normalizer_twoKernelInG
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (D.twoKernelInG_le_centralizer hz) h hh).symm

noncomputable abbrev joinedTwoQuotient (D : ExcTwE6CoverData hmark) : Type :=
  ↥(H ⊔ E) ⧸ D.twoKernelInG.subgroupOf (H ⊔ E)

@[expose] noncomputable def joinedMap (D : ExcTwE6CoverData hmark) : H →* D.joinedTwoQuotient :=
  (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))).comp
    (Subgroup.inclusion (show H ≤ H ⊔ E from le_sup_left))

theorem joinedMap_ker (D : ExcTwE6CoverData hmark) : D.joinedMap.ker = D.twoKernel := by
  ext x
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))
    (Subgroup.inclusion (show H ≤ H ⊔ E from le_sup_left) x) = 1 ↔ x ∈ D.twoKernel
  constructor
  · intro hx
    have hxG : (x : G) ∈ D.twoKernelInG :=
      (QuotientGroup.eq_one_iff (N := D.twoKernelInG.subgroupOf (H ⊔ E)) _).mp hx
    obtain ⟨z, hz, heq⟩ := Subgroup.mem_map.mp hxG
    have hzx : z = x := Subtype.ext heq
    simpa only [hzx] using hz
  · intro hx
    apply (QuotientGroup.eq_one_iff (N := D.twoKernelInG.subgroupOf (H ⊔ E)) _).mpr
    change (x : G) ∈ D.twoKernelInG
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

@[expose] noncomputable def joinedQuotientMap (D : ExcTwE6CoverData hmark) :
    (H ⧸ D.twoKernel) →* D.joinedTwoQuotient :=
  QuotientGroup.lift D.twoKernel D.joinedMap D.joinedMap_ker.ge

@[simp] theorem joinedQuotientMap_mk (D : ExcTwE6CoverData hmark) (x : H) :
    D.joinedQuotientMap (QuotientGroup.mk' D.twoKernel x) = D.joinedMap x := rfl

theorem joinedQuotientMap_injective (D : ExcTwE6CoverData hmark) :
    Function.Injective D.joinedQuotientMap := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [joinedQuotientMap, QuotientGroup.ker_lift, D.joinedMap_ker]
  apply le_antisymm _ bot_le
  rintro q ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff (N := D.twoKernel) _).mpr hx

@[expose] noncomputable def joinedActor (D : ExcTwE6CoverData hmark) : E →* D.joinedTwoQuotient :=
  (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))).comp
    (Subgroup.inclusion (show E ≤ H ⊔ E from le_sup_right))

theorem joinedQuotientMap_actor (D : ExcTwE6CoverData hmark) (e : E)
    (x : H ⧸ D.twoKernel) :
    D.joinedActor e * D.joinedQuotientMap x * (D.joinedActor e)⁻¹ =
      D.joinedQuotientMap
        (CFSG.GroupTheory.MulAut.quotientNormal (ggGamma H D.hEN e) D.twoKernel
          (D.twoKernel_map_ggGamma e) x) := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))
        (Subgroup.inclusion le_sup_right e) *
      QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))
        (Subgroup.inclusion le_sup_left x) *
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))
        (Subgroup.inclusion le_sup_right e))⁻¹ =
      QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))
        (Subgroup.inclusion le_sup_left (ggGamma H D.hEN e x))
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E)))
    exact Subtype.ext (ggGamma_coe (L := H) (hBN := D.hEN) e x).symm

@[expose] noncomputable def joinedScMap (D : ExcTwE6CoverData hmark) :
    twistedE6Group 2 1 →* D.joinedTwoQuotient :=
  D.joinedQuotientMap.comp D.scMap

theorem joinedScMap_range (D : ExcTwE6CoverData hmark) :
    D.joinedScMap.range = (H.subgroupOf (H ⊔ E)).map
      (QuotientGroup.mk' (D.twoKernelInG.subgroupOf (H ⊔ E))) := by
  rw [joinedScMap, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr D.scMap_spec.1, Subgroup.map_top]
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D.twoKernel x
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion (show H ≤ H ⊔ E from le_sup_left) h, h.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨QuotientGroup.mk' D.twoKernel ⟨(h : G), hh⟩, rfl⟩

theorem joinedScMap_ker_le_center (D : ExcTwE6CoverData hmark) :
    D.joinedScMap.ker ≤ Subgroup.center (twistedE6Group 2 1) := by
  rw [joinedScMap, MonoidHom.ker_comp_of_injective _ _ D.joinedQuotientMap_injective]
  exact D.scMap_spec.2.1

theorem joinedScMap_actor (D : ExcTwE6CoverData hmark) (e : E)
    (β : MulAut (twistedE6Group 2 1))
    (hβ : ∀ u, isogenyStd (β u) =
      (letI := D.fieldK
       letI := D.finiteK
       originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker e) (isogenyStd u)) :
    ∀ u, D.joinedActor e * D.joinedScMap u * (D.joinedActor e)⁻¹ =
      D.joinedScMap (β u) := by
  intro u
  rw [joinedScMap, MonoidHom.comp_apply, D.joinedQuotientMap_actor, D.scMap_actor e β hβ]
  rfl

theorem joinedScMap_action (D : ExcTwE6CoverData hmark) (e : E) (u : twistedE6Group 2 1) :
    D.joinedActor e * D.joinedScMap u * (D.joinedActor e)⁻¹ =
      D.joinedScMap (D.scAction e u) :=
  D.joinedScMap_actor e (D.scAction e) (D.scAction_spec e) u

end TwoPartQuotient

end ExcTwE6CoverData

end CoverSupplier

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

namespace CFSG.StandardType

open CFSG.Open

theorem GGRk1ConclEx.exists_noninner_quotient_actor_of_central_two
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Group.IsPerfect ↥X]
    {p : ℕ} {r : MulAut ↥Bs} (hR : GGRk1ConclEx p Bs X r)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {C : Type} [Group C] (ψ : ↥X →* C) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X)
    (β : ↥Bs →* MulAut C)
    (hcompat : ∀ b x, β b (ψ x) = ψ (ggGamma X hBN b x))
    {z : ↥X} (hz : z ∈ Subgroup.center ↥X) (hz1 : z ≠ 1)
    {k : ℕ} (hz2 : z ^ (2 ^ k) = 1) :
    ∃ b : ↥Bs, r b = b ∧ β b ∉ (MulAut.conj : C →* MulAut C).range := by
  classical
  by_contra hno
  push Not at hno
  apply hz1
  apply hR.eq_one_of_mem_center hz _ hz2
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨b, hb, rfl⟩
  have hbr : r b = b := hb
  obtain ⟨a, ha⟩ := mem_range_conj_of_induces_inn hψ hker
    Group.IsPerfect.commutator_eq_top (hcompat b) (hno b hbr)
  have hfix : ggGamma X hBN b z = z := by
    rw [← ha, MulAut.conj_apply, Subgroup.mem_center_iff.mp hz a]
    group
  have hfixG := congrArg (fun v : ↥X => (v : G)) hfix
  rw [ggGamma_coe] at hfixG
  calc
    (b : G) * (z : G) = ((b : G) * (z : G) * (b : G)⁻¹) * (b : G) := by group
    _ = (z : G) * (b : G) := by rw [hfixG]

end CFSG.StandardType

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG.StandardType CFSG.LieType.Chevalley

theorem exists_original_hyperplane_outer_actor_of_rk1
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Group.IsPerfect ↥X]
    {p : ℕ} {r : MulAut ↥Bs} (hR : GGRk1ConclEx p Bs X r)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {L : Type} [Field L] [Finite L] (σ : L ≃+* L)
    (ψ : ↥X →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X)
    (hact : CompatibleAction σ hBN ψ)
    {z : ↥X} (hz : z ∈ Subgroup.center ↥X) (hz1 : z ≠ 1)
    {k : ℕ} (hz2 : z ^ (2 ^ k) = 1) :
    ∃ (b : ↥Bs) (φ : MulAut (twistedE6RootGroup L σ)),
      r b = b ∧ φ ∈ (RecipeExcLang.twConj L σ).range ∧
      φ ∉ twistedE6Inn L σ ∧
      ∀ x : ↥X, φ (ψ x) = ψ (ggGamma X hBN b x) := by
  let β := originalQuotientAction hBN ψ hψ hker
  obtain ⟨b, hbr, hbout⟩ := hR.exists_noninner_quotient_actor_of_central_two
    hBN ψ hψ hker.le β
    (fun b x => originalQuotientAction_apply_mk hBN ψ hψ hker b x) hz hz1 hz2
  obtain ⟨φ, hφrange, hφeq⟩ := hact b
  have hβφ : β b = φ :=
    originalQuotientAction_eq_of_compatible hBN ψ hψ hker b φ hφeq
  refine ⟨b, φ, hbr, hφrange, ?_, hφeq⟩
  rw [hβφ] at hbout
  exact hbout

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG.StandardType CFSG.Open CFSG.LieType.Chevalley
open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PerfectCover
open CFSG.LieType.Chevalley.C2E6Std

attribute [local instance] finite_stdGroup isPerfect_stdGroup

set_option maxHeartbeats 2000000

theorem common_two_subkernel_eq_bot_of_rk1_and_coroot_positions
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Group.IsPerfect ↥X]
    [Fact (IsElemAbelian 3 Bs)] {r s : MulAut ↥Bs}
    (hR : GGRk1ConclEx 3 Bs X r)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ψ : ↥X →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X) (hact : CompatibleAction σ hBN ψ)
    {Z : Subgroup ↥X} (hZ : Z ≤ ψ.ker) (hZ2 : IsPGroup 2 Z)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank)
    {A T : Type*} [AddCommGroup A] [Module (ZMod 3) A]
    [AddCommGroup T] [Module (ZMod 3) T]
    (η : Multiplicative A →* ↥Bs) (hη : Function.Surjective η)
    (φ : A →ₗ[ZMod 3] T)
    (root : Fin (ggU t n f).D.rank → T →ₗ[ZMod 3] ZMod 3)
    (coroot : Fin (ggU t n f).D.rank → A)
    (hpair : ∀ i j, root j (φ (coroot i)) = ((ggU t n f).D.cartan i j : ZMod 3))
    (hinner : ∀ i, ggGamma X hBN (η (Multiplicative.ofAdd (coroot i))) ∈
      (MulAut.conj : ↥X →* MulAut ↥X).range)
    {α β : Fin (ggU t n f).D.rank → ℤ}
    (hα : α ∈ (ggU t n f).D.roots) (hβ : β ∈ (ggU t n f).D.roots)
    (hβne : β ≠ α) (hβne' : β ≠ -α)
    (hHr : ∀ a : A, (η (Multiplicative.ofAdd a) : G) ∈ ggHyperplane Bs r ↔
      (∑ j, (α j : ZMod 3) • root j) (φ a) = 0)
    (hHs : ∀ a : A, (η (Multiplicative.ofAdd a) : G) ∈ ggHyperplane Bs s ↔
      (∑ j, (β j : ZMod 3) • root j) (φ a) = 0) :
    Z.map X.subtype ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro y ⟨hyZ, hyC⟩
  obtain ⟨z, hzZ, rfl⟩ := Subgroup.mem_map.mp hyZ
  by_cases hz1 : z = 1
  · simp [hz1]
  have hz : z ∈ Subgroup.center ↥X := hker.le (hZ hzZ)
  obtain ⟨k, hk⟩ := hZ2.exists_orderOf_eq_pow (⟨z, hzZ⟩ : Z)
  have hz2 : z ^ (2 ^ k) = 1 := by
    have hpow : (⟨z, hzZ⟩ : Z) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    exact congrArg Subtype.val hpow
  obtain ⟨e0, δ0, _he0, hδ0, hout0, hδ0eq⟩ :=
    exists_original_hyperplane_outer_actor_of_rk1 hR hBN σ ψ hψ hker hact hz hz1 hz2
  let χ0 := originalOuterCharacter hL4 σ hσ hBN ψ hψ hker hact P Q3
  let χM : Multiplicative A →* Multiplicative (ZMod 3) := χ0.comp η
  let χA : A →+ ZMod 3 :=
    { toFun := fun a => (χM (Multiplicative.ofAdd a)).toAdd
      map_zero' := by simp [χM]
      map_add' := by
        intro a b
        change (χM (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).toAdd = _
        rw [map_mul]
        rfl }
  let χ : A →ₗ[ZMod 3] ZMod 3 := χA.toZModLinearMap 3
  have hχ : ∀ a, χ a = (χ0 (η (Multiplicative.ofAdd a))).toAdd := fun _ => rfl
  have hχinner : ∀ i, χ (coroot i) = 0 := by
    intro i
    rw [hχ]
    have hc := originalOuterCharacter_eq_one_of_ggGamma_mem_inner
      hL4 σ hσ hBN ψ hψ hker hact P Q3 (η (Multiplicative.ofAdd (coroot i))) (hinner i)
    change (χ0 (η (Multiplicative.ofAdd (coroot i)))).toAdd = 0
    rw [hc]
    rfl
  obtain ⟨a0, ha0⟩ := hη e0
  have hex : ∃ a : A, χ a ≠ 0 := by
    refine ⟨a0.toAdd, ?_⟩
    rw [hχ]
    change (χ0 (η a0)).toAdd ≠ 0
    rw [ha0]
    exact (originalOuterCharacter_ne_one_iff_of_compatible
      hL4 σ hσ hBN ψ hψ hker hact P Q3 e0 δ0 hδ0 hδ0eq).2 hout0
  obtain ⟨a, haH, haχ⟩ := ggRootPair_exists_nonzero_outer_actor_in_common_hyperplanes
    hadm ht h3 Nat.prime_three (by decide) φ χ root coroot hpair hχinner
    hα hβ hβne hβne' (Bs.subtype.comp η)
    (ggHyperplane Bs r) (ggHyperplane Bs s) hHr hHs hex
  let e : ↥Bs := η (Multiplicative.ofAdd a)
  have heH : (e : G) ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s := haH
  have he3 : e ^ 3 = 1 :=
    Subtype.ext ((Fact.out (p := IsElemAbelian 3 Bs)).2 (e : G) e.property)
  obtain ⟨δ, hδ, hδeq⟩ := hact e
  have hout : δ ∉ twistedE6Inn L σ := by
    apply (originalOuterCharacter_ne_one_iff_of_compatible
      hL4 σ hσ hBN ψ hψ hker hact P Q3 e δ hδ hδeq).1
    change (χ0 e).toAdd ≠ 0
    exact haχ
  have hbot := native_actor_Z_map_inf_centralizer_eq_bot
    hL4 σ hσ ψ hψ hker.le hBN e heH he3 δ hδ hδeq hout hZ hZ2 P Q3
  have hzC : (z : G) ∈ Z.map X.subtype ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) :=
    ⟨Subgroup.mem_map.mpr ⟨z, hzZ, rfl⟩, hyC⟩
  rw [hbot] at hzC
  exact hzC

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
