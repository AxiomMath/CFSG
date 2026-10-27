module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open Subgroup

variable {X : Type*} [Group X]

@[expose] def centerInvolutions (F : Subgroup X) : Subgroup X where
  carrier := {y | y ∈ F ∧ (∀ x ∈ F, y * x = x * y) ∧ y ^ 2 = 1}
  mul_mem' := by
    rintro y y' ⟨hyF, hyc, hy2⟩ ⟨hy'F, hy'c, hy'2⟩
    refine ⟨F.mul_mem hyF hy'F, fun x hx => ?_, ?_⟩
    · rw [mul_assoc, hy'c x hx, ← mul_assoc, hyc x hx, mul_assoc]
    · have hc : y * y' = y' * y := hyc y' hy'F
      rw [pow_two, mul_assoc, ← mul_assoc y' y y', ← hc, mul_assoc, ← mul_assoc,
        ← pow_two, ← pow_two, hy2, hy'2, one_mul]
  one_mem' := ⟨F.one_mem, fun x _ => by rw [one_mul, mul_one], one_pow 2⟩
  inv_mem' := by
    rintro y ⟨hyF, hyc, hy2⟩
    have hyinv : y⁻¹ = y := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hy2]
    show y⁻¹ ∈ F ∧ (∀ x ∈ F, y⁻¹ * x = x * y⁻¹) ∧ y⁻¹ ^ 2 = 1
    rw [hyinv]
    exact ⟨hyF, hyc, hy2⟩

instance centerInvolutions_normal (F : Subgroup X) [hF : F.Normal] :
    (centerInvolutions F).Normal where
  conj_mem := by
    rintro y ⟨hyF, hyc, hy2⟩ g
    refine ⟨hF.conj_mem y hyF g, fun x hx => ?_, ?_⟩
    · have hx' : g⁻¹ * x * g ∈ F := by
        have := hF.conj_mem x hx g⁻¹
        rwa [inv_inv] at this
      have h := hyc _ hx'
      calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [h]
        _ = x * (g * y * g⁻¹) := by group
    · rw [conj_pow, hy2, mul_one, mul_inv_cancel]

theorem isPGroup_centerInvolutions (F : Subgroup X) : IsPGroup 2 (centerInvolutions F) := by
  intro y
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using y.2.2.2

theorem centerInvolutions_eq_bot (hO2 : CFSG.pCore 2 X = ⊥) (F : Subgroup X) [F.Normal] :
    centerInvolutions F = ⊥ := by
  have hle : centerInvolutions F ≤ CFSG.pCore 2 X :=
    le_sSup ⟨centerInvolutions_normal F, isPGroup_centerInvolutions F⟩
  rw [hO2] at hle
  exact le_bot_iff.mp hle

theorem le_centralizer_of_le_centralizer_genFitting [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    {L A : Subgroup X} [hL : L.Normal] (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAF : A ≤ centralizer
      (((CFSG.generalizedFitting ↥L).map L.subtype : Subgroup X) : Set X)) :
    A ≤ centralizer (L : Set X) := by
  classical
  set F : Subgroup X := (CFSG.generalizedFitting ↥L).map L.subtype with hFdef
  have : (CFSG.generalizedFitting ↥L).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic).1
  have hFn : F.Normal := by rw [hFdef]; infer_instance
  intro a ha
  rw [mem_centralizer_iff]
  intro l hl
  have haF : ∀ x ∈ F, x * a = a * x := mem_centralizer_iff.mp (hAF ha)
  obtain ⟨z, hz⟩ : ∃ z : X, z = l⁻¹ * (a⁻¹ * l * a) := ⟨_, rfl⟩
  have hlconj : a⁻¹ * l * a ∈ L := by
    have := hL.conj_mem l hl a⁻¹
    rwa [inv_inv] at this
  have hzL : z ∈ L := hz ▸ L.mul_mem (L.inv_mem hl) hlconj
  have hzc : ∀ x ∈ F, z * x = x * z := by
    intro x hx
    have hlx : l * x * l⁻¹ ∈ F := hFn.conj_mem x hx l
    have h1 : x * a = a * x := haF x hx
    have h2 : Commute a⁻¹ (l * x * l⁻¹) := (Commute.inv_left (haF _ hlx).symm)
    calc z * x = l⁻¹ * a⁻¹ * l * (a * x) := by rw [hz]; group
      _ = l⁻¹ * a⁻¹ * l * (x * a) := by rw [h1]
      _ = l⁻¹ * (a⁻¹ * (l * x * l⁻¹)) * l * a := by group
      _ = l⁻¹ * ((l * x * l⁻¹) * a⁻¹) * l * a := by rw [h2.eq]
      _ = x * z := by rw [hz]; group
  have hzF : z ∈ F := by
    have hmem : (⟨z, hzL⟩ : ↥L) ∈ centralizer (CFSG.generalizedFitting ↥L : Set ↥L) := by
      rw [mem_centralizer_iff]
      intro h hh
      apply Subtype.ext
      have hhF : (h : X) ∈ F := ⟨h, hh, rfl⟩
      exact (hzc _ hhF).symm
    exact ⟨⟨z, hzL⟩, CFSG.centralizer_generalizedFitting_le ↥L hmem, rfl⟩
  have haz : z * a = a * z := haF z hzF
  have ha2 : a ^ 2 = 1 := hA2 a ha
  have haa : a * a = 1 := by rw [← pow_two, ha2]
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, haa]
  have hza : a⁻¹ * z * a = z := by
    rw [mul_assoc, haz, ← mul_assoc, inv_mul_cancel, one_mul]
  have hlz : a⁻¹ * l * a = l * z := by rw [hz]; group
  have key : a⁻¹ * (a⁻¹ * l * a) * a = l := by
    calc a⁻¹ * (a⁻¹ * l * a) * a = (a⁻¹ * a⁻¹) * l * (a * a) := by group
      _ = l := by rw [hainv, haa]; group
  have hzz : l * (z * z) = l * 1 := by
    calc l * (z * z) = (a⁻¹ * l * a) * (a⁻¹ * z * a) := by rw [hlz, hza, mul_assoc]
      _ = a⁻¹ * (l * z) * a := by group
      _ = a⁻¹ * (a⁻¹ * l * a) * a := by rw [hlz]
      _ = l * 1 := by rw [key, mul_one]
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact mul_left_cancel hzz
  have hzbot : z ∈ centerInvolutions F := ⟨hzF, hzc, hz2⟩
  rw [centerInvolutions_eq_bot hO2 F, mem_bot] at hzbot
  have hconj : a⁻¹ * l * a = l := by rw [hlz, hzbot, mul_one]
  calc l * a = a * (a⁻¹ * l * a) := by group
    _ = a * l := by rw [hconj]

theorem exists_pCore_or_component_of_not_le_centralizer [Finite X] {L A : Subgroup X}
    (h : ¬ A ≤ centralizer
      (((CFSG.generalizedFitting ↥L).map L.subtype : Subgroup X) : Set X)) :
    (∃ p : ℕ, p.Prime ∧
      ¬ A ≤ centralizer (((CFSG.pCore p ↥L).map L.subtype : Subgroup X) : Set X)) ∨
    (∃ K : Subgroup ↥L, CFSG.IsComponent K ∧
      ¬ A ≤ centralizer ((K.map L.subtype : Subgroup X) : Set X)) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hp, hK⟩ := hcon
  apply h
  rw [le_centralizer_iff]
  rw [CFSG.generalizedFitting, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    have hpp : (p.1 : ℕ).Prime := (Nat.prime_of_mem_primeFactors p.1.2)
    exact le_centralizer_iff.mp (hp p.1 hpp)
  · rw [CFSG.layer, (Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun K hK' => ?_
    exact le_centralizer_iff.mp (hK K hK')

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
