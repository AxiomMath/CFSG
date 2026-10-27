module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem exists_component_lift {G : Type} [Group G] [Finite G] (Y : Subgroup G) {P : Type}
    [Group P] [Finite P] (ρ : ↥Y →* P) (hρ : OddCentralCover ρ) {w : G} (hwY : w ∈ Y)
    (hw : w * w = 1) {X : Subgroup P}
    (hX : IsComponentIn X (centralizer ({ρ ⟨w, hwY⟩} : Set P))) (hwX : ρ ⟨w, hwY⟩ ∈ X)
    (h2 : IsTwoU43 ↥X) :
    ∃ X' : Subgroup G, IsComponentIn X' (Y ⊓ centralizer ({w} : Set G)) ∧ w ∈ X' ∧
      IsTwoU43 (↥X' ⧸ oddCore ↥X') ∧ X ≤ (X'.comap Y.subtype).map ρ := by
  have hw' : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := Subtype.ext hw
  have hXq : CFSG.IsQuasisimple ↥X := hX.isQuasisimple
  have hDcomp := hρ.isComponentIn_coverDerived hw' hX
  have hcov := hρ.oddCentralCover_coverDerivedHom hXq
  have hker : oddCore ↥(coverDerived ρ X) = (coverDerivedHom ρ X).ker :=
    hcov.oddCore_eq_ker (oddCore_eq_bot_of_isTwoU43 hXq h2)
  let e : ↥(coverDerived ρ X) ⧸ oddCore ↥(coverDerived ρ X) ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcov.surjective)
  let ι : ↥(coverDerived ρ X) ≃* ↥((coverDerived ρ X).map Y.subtype) :=
    (coverDerived ρ X).equivMapOfInjective Y.subtype Y.subtype_injective
  have hXcomp : IsComponentIn ((coverDerived ρ X).map Y.subtype)
      (Y ⊓ centralizer ({w} : Set G)) := by
    have := isComponentIn_map_of_injective Y.subtype Y.subtype_injective hDcomp
    rwa [map_subtype_centralizer Y hwY] at this
  have hwD : (⟨w, hwY⟩ : ↥Y) ∈ coverDerived ρ X := hρ.mem_coverDerived hXq hw' hwX
  obtain ⟨ε⟩ := nonempty_quotient_oddCore_mulEquiv ι
  refine ⟨(coverDerived ρ X).map Y.subtype, hXcomp, ⟨_, hwD, rfl⟩,
    isTwoU43_of_mulEquiv ε (isTwoU43_of_mulEquiv e.symm h2), ?_⟩
  intro q hq
  obtain ⟨a, ha, haq⟩ := hρ.exists_mem_coverDerived hXq hq
  refine ⟨a, ?_, haq⟩
  have hcomap : ((coverDerived ρ X).map Y.subtype).comap Y.subtype = coverDerived ρ X :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  show a ∈ ((coverDerived ρ X).map Y.subtype).comap Y.subtype
  rw [hcomap]
  exact ha

theorem not_isI4PlusIn_of_notQuat {G : Type} [Group G] [Finite G] {Y : Subgroup G} {P : Type}
    [Group P] (e : ↥Y ⧸ oddCore ↥Y ≃* P) (d : ↥Y) (hnq : NotQuat (e (QuotientGroup.mk d))) :
    ¬ IsI4PlusIn Y (d : G) := by
  intro hI
  obtain ⟨huY, f, hf, hfd⟩ := exists_quaternion_quotient_of_le (le_refl Y) hI
  refine hnq (e.toMonoidHom.comp f) (e.injective.comp hf) ?_
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hfd]

theorem gen_of_genP {G : Type} [Group G] [Finite G] (Y : Subgroup G) (hq : CFSG.IsQuasisimple ↥Y)
    {P : Type} [Group P] (e : ↥Y ⧸ oddCore ↥Y ≃* P) {z : G} (hzY : z ∈ Y) (hz : z * z = 1)
    (hGen : GenP (e (QuotientGroup.mk (⟨z, hzY⟩ : ↥Y)))) :
    Y ≤ ⨆ (d : G) (_ : orderOf d = 2 ∧ d ∈ pocketCore2 Y z ∧ ¬ IsI4PlusIn Y d),
      twoU43Comps Y d := by
  haveI : Finite P := Finite.of_equiv _ e.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥Y →* P := e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))
  have hρ : OddCentralCover ρ := oddCentralCover_quotient_oddCore hq e
  let H : Subgroup G := ⨆ (d : G) (_ : orderOf d = 2 ∧ d ∈ pocketCore2 Y z ∧ ¬ IsI4PlusIn Y d),
    twoU43Comps Y d
  have hcore := genPocketCore_le_map Y ρ hρ hzY hz
  have hle : genLayers (ρ ⟨z, hzY⟩) ≤ (H.comap Y.subtype).map ρ := by
    unfold genLayers
    refine iSup_le fun db => iSup_le fun Xb => iSup_le fun hgood => ?_
    obtain ⟨hd1, hdd, hdcore, hnq, hXc, hdX, hX2⟩ := hgood
    obtain ⟨x, hxT, hxd⟩ := hcore hdcore
    obtain ⟨hd'd', hρd'⟩ := hρ.pow_card_ker (a := x) (by rw [hxd]; exact hdd)
    set d' : ↥Y := x ^ Nat.card ρ.ker with hd'def
    have hd'T : d' ∈ (pocketCore2 Y z).comap Y.subtype := Subgroup.pow_mem _ hxT _
    have hρd : ρ d' = db := hρd'.trans hxd
    have hd'1 : d' ≠ 1 := by
      intro h1
      rw [h1, map_one] at hρd
      exact hd1 hρd.symm
    have hord : orderOf (d' : G) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        exact congrArg Subtype.val hd'd'
      · intro h1
        exact hd'1 (Subtype.ext h1)
    have hdnp : ¬ IsI4PlusIn Y (d' : G) := by
      refine not_isI4PlusIn_of_notQuat e d' ?_
      change NotQuat (ρ d')
      rw [hρd]
      exact hnq
    have hdd'eq : (⟨(d' : G), d'.2⟩ : ↥Y) = d' := rfl
    have hXc' : IsComponentIn Xb (centralizer ({ρ ⟨(d' : G), d'.2⟩} : Set P)) := by
      rw [hdd'eq, hρd]
      exact hXc
    have hdX2 : ρ ⟨(d' : G), d'.2⟩ ∈ Xb := by
      rw [hdd'eq, hρd]
      exact hdX
    obtain ⟨X', hX'c, hdX', hX'2, hXle⟩ := exists_component_lift Y ρ hρ d'.2
      (congrArg Subtype.val hd'd') hXc' hdX2 hX2
    have hX'H : X' ≤ H := by
      refine le_trans ?_ (le_iSup₂ (f := fun (d : G) (_ : orderOf d = 2 ∧ d ∈ pocketCore2 Y z ∧
        ¬ IsI4PlusIn Y d) => twoU43Comps Y d) (d' : G) ⟨hord, hd'T, hdnp⟩)
      exact le_iSup₂ (f := fun (K : Subgroup G) (_ : IsComponentIn K (Y ⊓ centralizer
        ({(d' : G)} : Set G)) ∧ (d' : G) ∈ K ∧ IsTwoU43 (↥K ⧸ oddCore ↥K)) => K) X'
        ⟨hX'c, hdX', hX'2⟩
    exact hXle.trans (Subgroup.map_mono (Subgroup.comap_mono hX'H))
  have hM : ⊤ ≤ (H.comap Y.subtype).map ρ := hGen.trans hle
  have hMtop := eq_top_of_map_eq_top ρ hρ.ker_le_center hq.1.commutator_eq_top hM
  intro y hy
  have : (⟨y, hy⟩ : ↥Y) ∈ H.comap Y.subtype := by
    rw [hMtop]
    exact Subgroup.mem_top _
  exact this

end CFSG.OddStandard.SmallF3.Omega
