module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ7
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin
open scoped MatrixGroups commutatorElement

universe v

section Generic

theorem map_center_eq_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ g
    obtain ⟨a', rfl⟩ := e.surjective g
    show e a' * e a = e a * e a'
    rw [← map_mul, ← map_mul, ha a']
  · intro hb
    refine ⟨e.symm b, fun g => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hb (e g)

@[expose] noncomputable def quotientCenterCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (map_center_eq_of_equiv e)

theorem nonempty_equiv_of_center_eq_bot {A B : Type*} [Group A] [Group B]
    (h : Subgroup.center A = ⊥) (β : (A ⧸ Subgroup.center A) ≃* B) : Nonempty (A ≃* B) := by
  refine ⟨MulEquiv.ofBijective (β.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A)))
    ⟨fun a b hab => ?_, fun y => ?_⟩⟩
  · have h1 : (QuotientGroup.mk a : A ⧸ Subgroup.center A) = QuotientGroup.mk b := β.injective hab
    rw [QuotientGroup.eq, h, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  · obtain ⟨q, rfl⟩ := β.surjective y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, rfl⟩

end Generic

section Layer

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H T M : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem odd_card_center_component (hnl : NonsolvableLayer H T M) {K : Subgroup ↥H}
    (hK : CFSG.IsComponent K) : Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  have h1 := CFSG.LocalCores.center_component_le_center_layer (G := ↥H) hK
  have hC := hnl.C_eq_center
  rw [hnl.K_eq_layer] at hC
  rw [hC] at h1
  have h2 : Nat.card ↥((Subgroup.center ↥K).map K.subtype) ∣
      Nat.card ↥(kerIn (M.subgroupOf H) ⊤) := Subgroup.card_dvd_of_le h1
  have h3 : Nat.card ↥((Subgroup.center ↥K).map K.subtype) = Nat.card ↥(Subgroup.center ↥K) :=
    Nat.card_congr ((Subgroup.center ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm.toEquiv
  rw [h3] at h2
  exact Odd.of_dvd_nat hnl.C_odd h2

theorem component_iso_of_trans (hnl : NonsolvableLayer H T M) {F : Type} [Field F]
    {K K' : Subgroup ↥H} (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K')
    (β : (↥K ⧸ Subgroup.center ↥K) ≃* SL(2, F)) :
    Nonempty ((↥K' ⧸ Subgroup.center ↥K') ≃* SL(2, F)) := by
  obtain ⟨t, -, ht⟩ := hnl.comp_trans K K' hK hK'
  let e : ↥K ≃* ↥K' := ((MulAut.conj t).subgroupMap K).trans (MulEquiv.subgroupCongr ht)
  exact ⟨(quotientCenterCongr e).symm.trans β⟩

theorem component_iso_ambient (hnl : NonsolvableLayer H T M) {F : Type} [Field F]
    {X Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hX : IsComponentIn X H) (hY : IsComponentIn Y H)
    (β : (↥X ⧸ Subgroup.center ↥X) ≃* SL(2, F)) :
    Nonempty ((↥Y ⧸ Subgroup.center ↥Y) ≃* SL(2, F)) := by
  obtain ⟨β'⟩ := component_iso_of_trans hnl hX.2 hY.2
    ((quotientCenterCongr (Subgroup.subgroupOfEquivOfLe hX.1)).trans β)
  exact ⟨(quotientCenterCongr (Subgroup.subgroupOfEquivOfLe hY.1)).symm.trans β'⟩

theorem center_component_eq_bot
    (hnl : NonsolvableLayer H T M) {F : Type} [Field F] [Fintype F]
    {n : ℕ} (hF : Fintype.card F = 2 ^ n) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : IsComponentIn X H) (β : (↥X ⧸ Subgroup.center ↥X) ≃* SL(2, F)) :
    Subgroup.center ↥X = ⊥ := by
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥X)) := by
    have := odd_card_center_component hnl hX.2
    rwa [Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hX.1)).toEquiv] at this
  exact center_eq_bot_of_odd_central_extension hF (isQuasisimple_of_isComponentIn hX).1 β hodd

theorem rad_eq_bot
    (hnl : NonsolvableLayer H T M) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {Lstar : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hLstar : IsComponentIn Lstar H) (α : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* SL(2, F)) :
    CFSG.solvableRadical ↥H = ⊥ := by
  have hC := hnl.C_eq_center
  rw [hnl.K_eq_layer] at hC
  rw [← hnl.C_eq_rad, ← hC, (CFSG.LocalCores.layer_center (G := ↥H)).1, iSup_eq_bot]
  intro K
  have hX : IsComponentIn (K.1.map H.subtype) H := BenderBranch.isComponentIn_of_isComponent K.2
  obtain ⟨β⟩ := component_iso_ambient hnl hLstar hX α
  have hc := center_component_eq_bot hnl hF hX β
  let e : ↥K.1 ≃* ↥(K.1.map H.subtype) := K.1.equivMapOfInjective H.subtype H.subtype_injective
  have : Subgroup.center ↥K.1 = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective e.toMonoidHom from e.injective)).1 ?_
    rw [map_center_eq_of_equiv, hc]
  rw [this, Subgroup.map_bot]

end Layer

end CFSG.QuasithinUnique.Setup.Lift
