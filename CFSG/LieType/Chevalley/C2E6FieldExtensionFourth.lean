module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue
public import CFSG.LieType.Chevalley.C2E6FourthResidueOpposite

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open FourthResidue (V0 Qminus sMinus rhoMinus fourthJ two_mem_fourthJ)

theorem sO_mul_self : FourthResidue.sO * FourthResidue.sO = 1 :=
  Subtype.ext FourthResidue.sMinus_mul_self

abbrev sHom :
    betaGroup →* TauCeti.QuadraticMap.orthogonalGroup Qminus :=
  betaGroupHom FourthResidue.sO sO_mul_self

@[expose] noncomputable def rhoO :
    nativeParabolic fourthJ →*
    TauCeti.QuadraticMap.orthogonalGroup Qminus :=
  (MonoidHom.codRestrict rhoMinus _ FourthResidue.rhoMinus_mem_orthogonalGroup).comp
    (leviProj two_mem_fourthJ)

theorem coe_rhoO
    (p : nativeParabolic fourthJ) :
    (rhoO p : V0 ≃ₗ[ZMod 2] V0) = rhoMinus (leviProj two_mem_fourthJ p) :=
  rfl

theorem rhoO_betaPar_mul_sHom
    (b : betaGroup) (p : nativeParabolic fourthJ) :
    rhoO (betaPar b p) * sHom b = sHom b * rhoO p := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h, mul_one, one_mul]
    congr 1
    exact Subtype.ext (by simp [h])
  · rw [betaGroupHom_of_eq_betaG _ h]
    apply Subtype.ext
    have e : leviProj two_mem_fourthJ (betaPar b p) =
        ⟨betaGL (leviProj two_mem_fourthJ p : ModGL Tag.E6 K),
          betaGL_mem_stdLevi (leviProj two_mem_fourthJ p).2⟩ := by
      apply Subtype.ext
      have e' : betaPar b p = ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ :=
        Subtype.ext (by simp [h, coe_betaG_apply])
      rw [e']
      exact leviProj_betaGL two_mem_fourthJ p
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_rhoO, coe_rhoO, e, FourthResidue.rhoMinus_betaGL]
    change sMinus * rhoMinus _ * sMinus * sMinus = sMinus * rhoMinus _
    rw [mul_assoc, FourthResidue.sMinus_mul_self, mul_one]

@[expose] noncomputable def thetaFour :
    parStar fourthJ →*
    TauCeti.QuadraticMap.orthogonalGroup Qminus where
  toFun γ := rhoO (parLeft γ) * sHom γ.1.right
  map_one' := by
    change rhoO 1 * sHom 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' γ γ' := by
    change rhoO (parLeft (γ * γ')) * sHom (γ.1.right * γ'.1.right) = _
    rw [parStar_left_mul, map_mul, map_mul, mul_assoc, ← mul_assoc (rhoO _) (sHom _),
      rhoO_betaPar_mul_sHom, ← mul_assoc, ← mul_assoc, ← mul_assoc]

theorem thetaFour_apply
    (γ : parStar fourthJ) :
    thetaFour γ = rhoO (parLeft γ) * sHom γ.1.right :=
  rfl

theorem residueFlag_betaPar
    (b : betaGroup) (p : nativeParabolic fourthJ) (k : Fin 3) :
    (FourthResidue.residueFlag (QuotientGroup.mk (betaPar b p)) :
        Fin 3 → Submodule (ZMod 2) V0) k =
      ((FourthResidue.residueFlag (QuotientGroup.mk p) : Fin 3 → Submodule (ZMod 2) V0) k).map
        ((sHom b : V0 ≃ₗ[ZMod 2] V0) : V0 →ₗ[ZMod 2] V0) := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h]
    have e : betaPar b p = p := Subtype.ext (by simp [h])
    rw [e]
    exact (Submodule.map_id _).symm
  · rw [betaGroupHom_of_eq_betaG _ h]
    have e : betaPar b p = ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ :=
      Subtype.ext (by simp [h, coe_betaG_apply])
    rw [e]
    exact FourthResidue.residueFlag_betaGL p k

theorem residueFlag_parSmul_four
    (γ : parStar fourthJ) (y : ParabolicCosets fourthJ)
    (k : Fin 3) :
    (FourthResidue.residueFlag (parSmul γ y) : Fin 3 → Submodule (ZMod 2) V0) k =
      ((FourthResidue.residueFlag y : Fin 3 → Submodule (ZMod 2) V0) k).map
        ((thetaFour γ : V0 ≃ₗ[ZMod 2] V0) : V0 →ₗ[ZMod 2] V0) := by
  induction y using QuotientGroup.induction_on with | H p => ?_
  rw [parSmul_mk, parMap_eq_mul, ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
    FourthResidue.residueFlag_smul_apply, residueFlag_betaPar, thetaFour_apply,
    ← Submodule.map_comp]
  rfl


theorem mem_zpowers_sO_iff {t : TauCeti.QuadraticMap.orthogonalGroup Qminus} :
    t ∈ Subgroup.zpowers FourthResidue.sO ↔ t = 1 ∨ t = FourthResidue.sO := by
  constructor
  · intro ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← zpow_mod_orderOf, FourthResidue.orderOf_sO]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    exacts [one_mem _, Subgroup.mem_zpowers _]

theorem rhoO_parLeft_leviStar
    (l : stdLevi fourthJ) (b : betaGroup) :
    rhoO (parLeft (leviStar two_mem_fourthJ l b)) = ⟨rhoMinus l,
      FourthResidue.rhoMinus_mem_orthogonalGroup l⟩ := by
  apply Subtype.ext
  rw [coe_rhoO]
  congr 1
  exact leviProj_of_mem two_mem_fourthJ l.2 _

theorem thetaFour_surjective
    : Function.Surjective thetaFour := by
  intro g
  obtain ⟨⟨e, t⟩, he⟩ := FourthResidue.isComplement'_elemO.2 g
  dsimp only at he
  obtain ⟨l, hl⟩ : ((e : TauCeti.QuadraticMap.orthogonalGroup Qminus) : V0 ≃ₗ[ZMod 2] V0) ∈
      rhoMinus.range := FourthResidue.range_rhoMinus ▸ e.2
  have hel : (⟨rhoMinus l, FourthResidue.rhoMinus_mem_orthogonalGroup l⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Qminus) = e := Subtype.ext hl
  rcases mem_zpowers_sO_iff.mp t.2 with ht | ht
  · refine ⟨leviStar two_mem_fourthJ l 1, ?_⟩
    rw [thetaFour_apply, rhoO_parLeft_leviStar, hel, map_one, mul_one, ← he, ht, mul_one]
  · refine ⟨leviStar two_mem_fourthJ l betaElt, ?_⟩
    rw [thetaFour_apply, rhoO_parLeft_leviStar, hel, betaGroupHom_of_eq_betaG _ rfl, ← he, ht]

theorem thetaFour_eq_one_iff
    (γ : parStar fourthJ) :
    thetaFour γ = 1 ↔ (γ.1.right : MulAut stdGroup) = 1 ∧
      (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical fourthJ := by
  rw [thetaFour_apply]
  rcases mem_betaGroup_iff.mp γ.1.right.2 with h | h
  · rw [betaGroupHom_of_eq_one _ h, mul_one, and_iff_right h,
      ← leviProj_eq_one_iff two_mem_fourthJ (parLeft γ)]
    constructor
    · intro h1
      apply FourthResidue.rhoMinus_injective
      rw [map_one, ← coe_rhoO, h1]
      rfl
    · intro h1
      apply Subtype.ext
      rw [coe_rhoO, h1, map_one]
      rfl
  · rw [betaGroupHom_of_eq_betaG _ h]
    constructor
    · intro h1
      exfalso
      have h2 : rhoO (parLeft γ) = FourthResidue.sO := by
        rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right sO_mul_self]
      have h3 := FourthResidue.rhoMinus_mem_elementaryGroup
        (leviProj two_mem_fourthJ (parLeft γ))
      rw [← coe_rhoO, h2] at h3
      exact FourthResidue.sMinus_not_mem_elementaryGroup h3
    · rintro ⟨h1, -⟩
      exact absurd (h.symm.trans h1) betaG_ne_one

theorem forall_smul_eq_iff_four
    (γ : parStar fourthJ) :
    (∀ x ∈ baseResidue fourthJ, γ.1 • x = x) ↔
      (γ.1.right : MulAut stdGroup) = 1 ∧ (γ.1.left : ModGL Tag.E6 K) ∈ stdRadical fourthJ := by
  rw [forall_smul_eq_iff, ← thetaFour_eq_one_iff]
  constructor
  · intro h
    apply Subtype.ext
    refine FourthResidue.eq_one_of_forall_smul_flag (thetaFour γ).2 fun W hW k => ?_
    obtain ⟨y, hy⟩ := FourthResidue.residueFlag.surjective ⟨W, hW⟩
    have := residueFlag_parSmul_four γ y k
    rw [h y, hy] at this
    exact this.symm
  · intro h y
    apply FourthResidue.residueFlag.injective
    apply Subtype.ext
    funext k
    rw [residueFlag_parSmul_four, h]
    exact Submodule.map_id _


theorem coe_thetaFour_of_eq_one
    {γ : parStar fourthJ} (h : (γ.1.right : MulAut stdGroup) = 1) :
    (thetaFour γ : V0 ≃ₗ[ZMod 2] V0) = rhoMinus (leviProj two_mem_fourthJ (parLeft γ)) := by
  rw [thetaFour_apply, betaGroupHom_of_eq_one _ h, mul_one]
  rfl

theorem coe_thetaFour_of_eq_betaG
    {γ : parStar fourthJ}
    (h : (γ.1.right : MulAut stdGroup) = betaG) :
    (thetaFour γ : V0 ≃ₗ[ZMod 2] V0) =
      rhoMinus (leviProj two_mem_fourthJ (parLeft γ)) * sMinus := by
  rw [thetaFour_apply, betaGroupHom_of_eq_betaG _ h]
  rfl

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
