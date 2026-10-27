module

public import CFSG.GF2Type.Smith1979.CaseIIA7
public import CFSG.GF2Type.Smith1979.CaseIIA8Sp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem commutator_Gam (hCE : S4.CentralExtInput.{u}) : commutator ↥D.Gam = ⊤ := by
  have hAlt : Sp.AltGrp (omegaU t) (Vsub g t) D.spData ≤ D.Gam := by
    rw [← D.Gam0_eq_Alt hCE]
    exact D.Gam0_le_Gam
  refine D.isGamma.commutator_eq_top D.spData hAlt ?_
  rintro _ ⟨r, rfl⟩ hV
  have hrN : (r : S.O) ∈ Nbar S g t := by
    refine ⟨r.2, fun v hv => ?_⟩
    have h1 := hV ⟨v, Vt_le_commSpace D.H D.ht1 hv⟩ hv
    exact congrArg Subtype.val h1
  exact D.Gam0_le_Alt hCE ⟨⟨r, hrN⟩, rfl⟩

variable {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} (hχ : χ D.tR = Multiplicative.ofAdd 1)
include hχ

theorem bijective_ker_resR :
    Function.Bijective (D.resR.rangeRestrict.comp χ.ker.subtype) := by
  constructor
  · intro u v h
    have h1 : D.resR (u : ↥(Rbar S g t)) = D.resR (v : ↥(Rbar S g t)) :=
      congrArg Subtype.val h
    have h2 : χ (u : ↥(Rbar S g t)) = χ (v : ↥(Rbar S g t)) := by
      rw [MonoidHom.mem_ker.mp u.2, MonoidHom.mem_ker.mp v.2]
    exact Subtype.ext (D.pair_inj hχ _ _ h1 h2)
  · rintro ⟨_, r, rfl⟩
    by_cases h : χ r = 1
    · exact ⟨⟨r, h⟩, rfl⟩
    · have h1 : χ r = Multiplicative.ofAdd 1 := (mult_zmod2_cases _).resolve_left h
      have h2 : r * D.tR ∈ χ.ker := by
        rw [MonoidHom.mem_ker, map_mul, h1, hχ]
        exact mult_zmod2_mul_self _
      refine ⟨⟨r * D.tR, h2⟩, Subtype.ext ?_⟩
      show D.resR (r * D.tR) = D.resR r
      rw [map_mul, (D.resR_eq_one_iff D.tR).mpr (Or.inr rfl), mul_one]

theorem isPerfect_Rprime (hCE : S4.CentralExtInput.{u}) : Group.IsPerfect ↥(Rprime S g t χ) := by
  haveI : Group.IsPerfect ↥D.Gam := ⟨D.commutator_Gam hCE⟩
  let e1 : ↥χ.ker ≃* ↥D.Gam := MulEquiv.ofBijective _ (D.bijective_ker_resR hχ)
  haveI : Group.IsPerfect ↥χ.ker :=
    Group.IsPerfect.ofSurjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  let e2 : ↥χ.ker ≃* ↥(Rprime S g t χ) :=
    Subgroup.equivMapOfInjective χ.ker (Rbar S g t).subtype Subtype.val_injective
  exact Group.IsPerfect.ofSurjective (f := e2.toMonoidHom) e2.surjective

theorem commutator_Rbar_le_ker : commutator ↥(Rbar S g t) ≤ χ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

omit hχ in
theorem map_commutator_rangeRestrict (hCE : S4.CentralExtInput.{u}) :
    (commutator ↥(Rbar S g t)).map D.resR.rangeRestrict = ⊤ := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥(Rbar S g t)) ⊤ D.resR.rangeRestrict
  rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _
    D.resR.rangeRestrict_surjective] at h1
  exact h1.trans (D.commutator_Gam hCE)

theorem ker_le_commutator (hCE : S4.CentralExtInput.{u}) :
    χ.ker ≤ commutator ↥(Rbar S g t) := by
  intro k hk
  have hmem : D.resR.rangeRestrict k ∈ (⊤ : Subgroup D.resR.range) := Subgroup.mem_top _
  rw [← D.map_commutator_rangeRestrict hCE] at hmem
  obtain ⟨c, hc, hck⟩ := hmem
  have h1 : D.resR c = D.resR k := congrArg Subtype.val hck
  have h2 : χ c = χ k := by
    rw [MonoidHom.mem_ker.mp (D.commutator_Rbar_le_ker hχ hc), MonoidHom.mem_ker.mp hk]
  rw [← D.pair_inj hχ c k h1 h2]
  exact hc

theorem ker_eq_commutator (hCE : S4.CentralExtInput.{u}) :
    χ.ker = commutator ↥(Rbar S g t) :=
  le_antisymm (D.ker_le_commutator hχ hCE) (D.commutator_Rbar_le_ker hχ)

end Data

@[expose] noncomputable def Rder (S : Setting G) (g : G) (t : S.O) : Subgroup S.O :=
  (commutator ↥(Rbar S g t)).map (Rbar S g t).subtype

theorem Rprime_eq_Rder {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} (D : Data S g t)
    (hχ : χ D.tR = Multiplicative.ofAdd 1) (hCE : S4.CentralExtInput.{u}) :
    Rprime S g t χ = Rder S g t := by
  unfold Rprime Rder
  rw [D.ker_eq_commutator hχ hCE]

theorem Rbar_structure_II (D : Data S g t) (hCE : S4.CentralExtInput.{u}) :
    centralizer ({t} : Set S.O) ⊓ S.Mbar = Rbar S g t ∧ Nat.card (Rbar S g t) = 2688 ∧
    (∀ r ∈ Rbar S g t, r * t = t * r) ∧
    Rder S g t ≤ Rbar S g t ∧ t ∉ Rder S g t ∧ Rder S g t ⊔ zpowers t = Rbar S g t ∧
    Rder S g t ⊓ zpowers t = ⊥ ∧ Nat.card (Rder S g t) = 1344 ∧
    Group.IsPerfect ↥(Rder S g t) ∧ Nat.card ↥(Rder S g t ⊓ Nbar S g t) = 8 ∧
    Nat.card (Nbar S g t) = 16 ∧ (∀ a ∈ Nbar S g t, ∀ b ∈ Nbar S g t, a * b = b * a) ∧
    (∀ a ∈ Nbar S g t, a * a = 1) := by
  obtain ⟨χ, hχ⟩ := D.exists_chiR
  have e := Rprime_eq_Rder D hχ hCE
  rw [← e]
  refine ⟨D.centralizer_inf_Mbar_eq hCE, D.card_Rbar hCE,
    fun r hr => commute_of_mem_Rbar D.H.conj_mem hr, Rprime_le_Rbar,
    D.t_notMem_Rprime hχ, D.Rprime_sup hχ, D.Rprime_inf hχ, D.card_Rprime hχ hCE,
    D.isPerfect_Rprime hχ hCE, D.card_Rprime_inf_Nbar hχ hCE, D.card_Nbar hCE,
    fun a ha b hb => ?_, fun a ha => ?_⟩
  · have := D.Nbar_commute hχ hCE ⟨a, Nbar_le_Rbar ha⟩ ⟨b, Nbar_le_Rbar hb⟩ ha hb
    exact congrArg Subtype.val this
  · have := D.Nbar_mul_self hχ hCE ⟨a, Nbar_le_Rbar ha⟩ ha
    exact congrArg Subtype.val this

end CFSG.GF2Type.Smith1979.Case2
