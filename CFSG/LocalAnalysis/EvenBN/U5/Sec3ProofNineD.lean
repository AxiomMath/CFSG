module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.ModelThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

section Generic39dKey

variable {G : Type*} [Group G]

def sec39dECent (V E : Subgroup G) (hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v) (z : G) :
    Subgroup G where
  carrier := {u | u ∈ E ∧ ⁅u, z⁆ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, show a * ⁅b, z⁆ * a⁻¹ = ⁅b, z⁆ by
      rw [← hV _ hcb a ha]
      group]
    exact mul_mem hcb hca
  one_mem' := ⟨one_mem _, by simpa using one_mem V⟩
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e, show a⁻¹ * ⁅a, z⁆⁻¹ * a = ⁅a, z⁆⁻¹ by
      rw [← hV _ (inv_mem hca) a⁻¹ (inv_mem ha)]
      group]
    exact inv_mem hca

theorem sec39d_mem_ECent {V E : Subgroup G} {hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v} {z u : G} :
    u ∈ sec39dECent V E hV z ↔ u ∈ E ∧ ⁅u, z⁆ ∈ V := Iff.rfl

theorem sec39d_key_comm_mul (u a b : G) : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem sec39d_key_inf_le {V E S : Subgroup G} (hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v) {y : G} (hy : y ∈ S) (y' : G) :
    sec39dECent V E hV y ⊓ sec39dECent V E hV y' ≤ sec39dECent V E hV (y * y') := by
  intro u hu
  rw [mem_inf, sec39d_mem_ECent, sec39d_mem_ECent] at hu
  obtain ⟨⟨huE, hu1⟩, ⟨-, hu2⟩⟩ := hu
  rw [sec39d_mem_ECent]
  refine ⟨huE, ?_⟩
  rw [sec39d_key_comm_mul, show y * ⁅u, y'⁆ * y⁻¹ = ⁅u, y'⁆ by
    rw [← hVS _ hu2 y hy]; group]
  exact mul_mem hu1 hu2

theorem sec39d_key_conj_card [Finite G] {V E : Subgroup G}
    (hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    (t : G) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (y : G) :
    Nat.card (sec39dECent V E hV y) ≤ Nat.card (sec39dECent V E hV (t * y * t⁻¹)) := by
  have hmem : ∀ u ∈ sec39dECent V E hV y,
      t * u * t⁻¹ ∈ sec39dECent V E hV (t * y * t⁻¹) := by
    intro u hu
    rw [sec39d_mem_ECent] at hu ⊢
    refine ⟨htE u hu.1, ?_⟩
    have h : ⁅t * u * t⁻¹, t * y * t⁻¹⁆ = t * ⁅u, y⁆ * t⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact htV _ hu.2
  refine Nat.card_le_card_of_injective (fun u => ⟨t * u.1 * t⁻¹, hmem u.1 u.2⟩) ?_
  intro a b hab
  have h1 : t * a.1 * t⁻¹ = t * b.1 * t⁻¹ := congrArg Subtype.val hab
  exact Subtype.ext (by simpa using h1)

theorem sec39d_key_card_mul_le [Finite G] {A B E : Subgroup G} (hA : A ≤ E) (hB : B ≤ E) :
    Nat.card A * Nat.card B ≤ Nat.card E * Nat.card (A ⊓ B : Subgroup G) := by
  have h1 : B.relIndex A * Nat.card (B ⊓ A : Subgroup G) = Nat.card A := relIndex_mul_card B A
  have h2 : B.relIndex E * Nat.card (B ⊓ E : Subgroup G) = Nat.card E := relIndex_mul_card B E
  rw [inf_of_le_left hB] at h2
  have h0 : B.relIndex E ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact Nat.card_pos.ne h2
  have h3 : B.relIndex A ≤ B.relIndex E := relIndex_le_of_le_right hA h0
  rw [inf_comm] at h1
  calc Nat.card A * Nat.card B = (B.relIndex A * Nat.card (A ⊓ B : Subgroup G)) * Nat.card B := by
        rw [h1]
    _ ≤ (B.relIndex E * Nat.card (A ⊓ B : Subgroup G)) * Nat.card B :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ = (B.relIndex E * Nat.card B) * Nat.card (A ⊓ B : Subgroup G) := by ring
    _ = Nat.card E * Nat.card (A ⊓ B : Subgroup G) := by rw [h2]


theorem sec39d_key_step1 [Finite G] (q : ℕ) (hq : 2 ≤ q)
    (S E V R Ω : Subgroup G) (t : G) (ht : t * t = 1)
    (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v) (hES : E ≤ S)
    (hcardE : Nat.card E = q ^ 14) (hRS : R ≤ S)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (htR : ∀ y ∈ R, t * y * t⁻¹ ∈ R)
    (hΩ : ∀ y, y ∈ Ω ↔ y ∈ R ∧ y * y = 1)
    (hH4 : ∀ z ∈ Ω, z ≠ 1 → t * z * t⁻¹ = z →
      Nat.card (sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z) ≤ q ^ 10)
    (y : G) (hy : y ∈ Ω) (hy1 : y ≠ 1) :
    Nat.card (sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) y) ≤ q ^ 12 := by
  have hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v := fun v hv e he => hVS v hv e (hES he)
  obtain ⟨hyR, hyy⟩ := (hΩ y).1 hy
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨y', hy'⟩ : ∃ y', y' = t * y * t⁻¹ := ⟨_, rfl⟩
  have hy'R : y' ∈ R := by rw [hy']; exact htR y hyR
  have hy'y' : y' * y' = 1 := by
    rw [hy']
    calc t * y * t⁻¹ * (t * y * t⁻¹) = t * (y * y) * t⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  have hy'Ω : y' ∈ Ω := (hΩ y').2 ⟨hy'R, hy'y'⟩
  by_cases hyy' : y' = y
  · refine (hH4 y hy hy1 (hy'.symm.trans hyy')).trans ?_
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  · have hy'inv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'y'
    have hzΩ : y * y' ∈ Ω := mul_mem hy hy'Ω
    have hzz : (y * y') * (y * y') = 1 := ((hΩ _).1 hzΩ).2
    have hcomm : y' * y = y * y' := by
      have h := eq_inv_of_mul_eq_one_left hzz
      rw [mul_inv_rev, hyinv, hy'inv] at h
      exact h.symm
    have hz1 : y * y' ≠ 1 := by
      intro h
      apply hyy'
      have h2 := inv_eq_of_mul_eq_one_right h
      rw [hyinv] at h2
      exact h2.symm
    have htz : t * (y * y') * t⁻¹ = y * y' := by
      have htt : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
      have h1 : t * y' * t⁻¹ = y := by
        rw [hy']
        calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
          _ = y := by rw [ht, htt]; simp
      calc t * (y * y') * t⁻¹ = (t * y * t⁻¹) * (t * y' * t⁻¹) := by group
        _ = y' * y := by rw [← hy', h1]
        _ = y * y' := hcomm
    have hc1 : Nat.card (sec39dECent V E hV y) ≤ Nat.card (sec39dECent V E hV y') := by
      rw [hy']; exact sec39d_key_conj_card hV t htE htV y
    have hc2 := sec39d_key_card_mul_le (A := sec39dECent V E hV y)
      (B := sec39dECent V E hV y') (E := E)
      (fun u hu => ((sec39d_mem_ECent).1 hu).1) (fun u hu => ((sec39d_mem_ECent).1 hu).1)
    have hc3 : Nat.card (sec39dECent V E hV y ⊓ sec39dECent V E hV y' : Subgroup G) ≤
        Nat.card (sec39dECent V E hV (y * y')) :=
      card_le_of_le (sec39d_key_inf_le hV hVS (hRS hyR) y')
    have hc4 := hH4 (y * y') hzΩ hz1 htz
    have hsq : (Nat.card (sec39dECent V E hV y)) ^ 2 ≤ (q ^ 12) ^ 2 := by
      calc (Nat.card (sec39dECent V E hV y)) ^ 2
          = Nat.card (sec39dECent V E hV y) * Nat.card (sec39dECent V E hV y) := sq _
        _ ≤ Nat.card (sec39dECent V E hV y) * Nat.card (sec39dECent V E hV y') :=
          Nat.mul_le_mul_left _ hc1
        _ ≤ Nat.card E *
            Nat.card (sec39dECent V E hV y ⊓ sec39dECent V E hV y' : Subgroup G) := hc2
        _ ≤ q ^ 14 * q ^ 10 := by
          rw [hcardE]; exact Nat.mul_le_mul_left _ (hc3.trans hc4)
        _ = (q ^ 12) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq

theorem sec39d_key_A_inv {E V R X : Subgroup G} {S : Subgroup G} (hVE : V ≤ E)
    (hEn : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hRS : R ≤ S)
    (hER : ∀ x ∈ E, x ∈ R → x = 1) (hX2 : ∀ x ∈ X, x * x ∈ V)
    {y e : G} (hyR : y ∈ R) (he : e ∈ E) (hX : e * y ∈ X) : y * y = 1 := by
  have h1 : (e * y) * (e * y) ∈ E := hVE (hX2 _ hX)
  have h2 : y * e * y⁻¹ ∈ E := hEn y (hRS hyR) e he
  have h3 : y * y ∈ E := by
    have h : y * y = (e * (y * e * y⁻¹))⁻¹ * ((e * y) * (e * y)) := by group
    rw [h]
    exact mul_mem (inv_mem (mul_mem he h2)) h1
  exact hER _ h3 (mul_mem hyR hyR)

theorem sec39d_key_A_cent {S E V X : Subgroup G} (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v)
    (hES : E ≤ S) (hE2 : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ V)
    (hX3 : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ V) (hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    {y e : G} (he : e ∈ E) (hX : e * y ∈ X) :
    X ⊓ E ≤ sec39dECent V E hV y := by
  intro u hu
  rw [mem_inf] at hu
  obtain ⟨huX, huE⟩ := hu
  rw [sec39d_mem_ECent]
  refine ⟨huE, ?_⟩
  have h1 : ⁅u, e * y⁆ ∈ V := hX3 u huX _ hX
  have h2 : ⁅u, e⁆ ∈ V := hE2 u huE e he
  have h3 : ⁅u, e * y⁆ = ⁅u, e⁆ * (e * ⁅u, y⁆ * e⁻¹) := sec39d_key_comm_mul u e y
  have h4 : e * ⁅u, y⁆ * e⁻¹ ∈ V := by
    have h : e * ⁅u, y⁆ * e⁻¹ = ⁅u, e⁆⁻¹ * ⁅u, e * y⁆ := by rw [h3]; group
    rw [h]
    exact mul_mem (inv_mem h2) h1
  have h5 : ⁅u, y⁆ = e⁻¹ * (e * ⁅u, y⁆ * e⁻¹) * e := by group
  have h6 := hVS _ h4 e (hES he)
  rw [h5, mul_assoc, h6, ← mul_assoc, inv_mul_cancel, one_mul]
  exact h4

theorem sec39d_key_card_X [Finite G] {S E R Ω X : Subgroup G} (hXS : X ≤ S)
    (hdec : ∀ s ∈ S, ∃ e ∈ E, ∃ y ∈ R, s = e * y)
    (hΩy : ∀ y ∈ R, ∀ e ∈ E, e * y ∈ X → y ∈ Ω) :
    Nat.card X ≤ Nat.card (X ⊓ E : Subgroup G) *
      Nat.card {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X} := by
  classical
  have hch : ∀ y : {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X}, ∃ e, e ∈ E ∧ e * y.1.1 ∈ X := fun y => by
    obtain ⟨e, he, hX⟩ := y.2
    exact ⟨e, he, hX⟩
  choose f hfE hfX using hch
  let Φ : (↥(X ⊓ E) × {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X}) → X := fun p =>
    ⟨p.1.1 * (f p.2 * p.2.1.1), mul_mem (mem_inf.1 p.1.2).1 (hfX p.2)⟩
  have hΦ : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    obtain ⟨e, he, y, hyR, rfl⟩ := hdec x (hXS hx)
    have hyΩ : y ∈ Ω := hΩy y hyR e he hx
    let a : {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X} := ⟨⟨y, hyΩ⟩, e, he, hx⟩
    have hfa : f a * y ∈ X := hfX a
    have hw : e * y * (f a * y)⁻¹ ∈ X ⊓ E := by
      refine mem_inf.2 ⟨mul_mem hx (inv_mem hfa), ?_⟩
      have h : e * y * (f a * y)⁻¹ = e * (f a)⁻¹ := by group
      rw [h]
      exact mul_mem he (inv_mem (hfE a))
    refine ⟨(⟨_, hw⟩, a), ?_⟩
    apply Subtype.ext
    show e * y * (f a * y)⁻¹ * (f a * y) = e * y
    group
  calc Nat.card X ≤ Nat.card (↥(X ⊓ E) × {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X}) :=
        Nat.card_le_card_of_surjective Φ hΦ
    _ = _ := Nat.card_prod _ _

theorem sec39d_key_abstract [Finite G] (q : ℕ) (hq : 2 ≤ q)
    (S E V R Ω : Subgroup G) (t : G) (ht : t * t = 1)
    (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v)
    (hVE : V ≤ E) (hES : E ≤ S) (hEn : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hE1 : ∀ x ∈ E, x * x ∈ V) (hE2 : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ V)
    (hcardE : Nat.card E = q ^ 14)
    (hRS : R ≤ S) (hdec : ∀ s ∈ S, ∃ e ∈ E, ∃ y ∈ R, s = e * y)
    (hER : ∀ x ∈ E, x ∈ R → x = 1)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (htR : ∀ y ∈ R, t * y * t⁻¹ ∈ R)
    (hΩ : ∀ y, y ∈ Ω ↔ y ∈ R ∧ y * y = 1) (hΩcard : Nat.card Ω ≤ q ^ 2)
    (hz₀ : ∃ z ∈ Ω, z ≠ 1 ∧ t * z * t⁻¹ = z)
    (hH4 : ∀ z ∈ Ω, z ≠ 1 → t * z * t⁻¹ = z →
      Nat.card (sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z) ≤ q ^ 10) :
    ∀ X : Subgroup G, V ≤ X → X ≤ S → (∀ x ∈ X, x * x ∈ V) → (∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ V) →
      q ^ 14 ≤ Nat.card X → X = E := by
  intro X hVX hXS hX2 hX3 hcardX
  have hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v := fun v hv e he => hVS v hv e (hES he)
  have hΩy : ∀ y ∈ R, ∀ e ∈ E, e * y ∈ X → y ∈ Ω := fun y hyR e he hX =>
    (hΩ y).2 ⟨hyR, sec39d_key_A_inv hVE hEn hRS hER hX2 hyR he hX⟩
  have hcX := sec39d_key_card_X hXS hdec hΩy
  have hΩ' : Nat.card {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X} ≤ Nat.card Ω :=
    Finite.card_subtype_le _
  have hq12 : q ^ 12 * q ^ 2 = q ^ 14 := by ring
  have hq10 : q ^ 10 * q ^ 2 = q ^ 12 := by ring
  have hlt : q ^ 12 < q ^ 14 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  by_cases hcase : ∃ y ∈ Ω, y ≠ 1 ∧ ∃ e ∈ E, e * y ∈ X
  · exfalso
    obtain ⟨y₁, hy₁Ω, hy₁1, e₁, he₁, hX₁⟩ := hcase
    have hinf1 : Nat.card (X ⊓ E : Subgroup G) ≤ q ^ 12 :=
      (card_le_of_le (sec39d_key_A_cent hVS hES hE2 hX3 hV he₁ hX₁)).trans
        (sec39d_key_step1 q hq S E V R Ω t ht hVS hES hcardE hRS htE htV htR hΩ hH4 y₁ hy₁Ω hy₁1)
    have hpos : 0 < Nat.card (X ⊓ E : Subgroup G) := Nat.card_pos
    by_cases hall : ∀ y : ↥Ω, ∃ e ∈ E, e * y.1 ∈ X
    · obtain ⟨z, hzΩ, hz1, htz⟩ := hz₀
      obtain ⟨e, he, hXz⟩ := hall ⟨z, hzΩ⟩
      have hXz' : e * z ∈ X := hXz
      have hinf2 : Nat.card (X ⊓ E : Subgroup G) ≤ q ^ 10 :=
        (card_le_of_le (sec39d_key_A_cent hVS hES hE2 hX3 hV he hXz')).trans
          (hH4 z hzΩ hz1 htz)
      have h1 : Nat.card X ≤ q ^ 10 * q ^ 2 :=
        hcX.trans (Nat.mul_le_mul hinf2 (hΩ'.trans hΩcard))
      omega
    · rw [not_forall] at hall
      obtain ⟨y, hy⟩ := hall
      have hlt' : Nat.card {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X} < Nat.card Ω :=
        Finite.card_subtype_lt (p := fun y : ↥Ω => ∃ e ∈ E, e * y.1 ∈ X) (x := y) hy
      have h2 : Nat.card {y : ↥Ω // ∃ e ∈ E, e * y.1 ∈ X} + 1 ≤ q ^ 2 :=
        Nat.succ_le_of_lt (hlt'.trans_le hΩcard)
      have h3 := Nat.mul_le_mul hinf1 h2
      rw [mul_add, mul_one, hq12] at h3
      omega
  · have hXE : X ≤ E := by
      intro x hx
      obtain ⟨e, he, y, hyR, rfl⟩ := hdec x (hXS hx)
      have hyΩ : y ∈ Ω := hΩy y hyR e he hx
      by_cases hy1 : y = 1
      · rw [hy1, mul_one]
        exact he
      · exact (hcase ⟨y, hyΩ, hy1, e, he, hx⟩).elim
    exact Subgroup.eq_of_le_of_card_ge hXE (by rw [hcardE]; exact hcardX)

end Generic39dKey

section Generic39dJF

theorem sec39d_jf_inj {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (hker : Odd (Nat.card φ.ker)) (T : Subgroup X) (hT : IsPGroup 2 T) :
    ∀ x ∈ T, φ x = 1 → x = 1 := by
  intro x hx hφx
  obtain ⟨n, hn⟩ := hT ⟨x, hx⟩
  have h1 : x ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf x ∣ Nat.card φ.ker := by
    have := orderOf_dvd_natCard (⟨x, (MonoidHom.mem_ker).2 hφx⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ n) (Nat.card φ.ker) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hker)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2 h3)

theorem sec39d_lift {X Y : Type*} [Group X] [Finite X] [Group Y] (φ : X →* Y)
    (hker : Odd (Nat.card φ.ker)) (T : Subgroup Y) (hT : IsPGroup 2 T) (hTr : T ≤ φ.range) :
    ∃ T' : Subgroup X, IsPGroup 2 T' ∧ T'.map φ = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : (T.comap φ).map φ = T := Subgroup.map_comap_eq_self hTr
  haveI hrfin : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI hTfin : Finite T := Finite.of_injective (Subgroup.inclusion hTr)
    (Subgroup.inclusion_injective hTr)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT
  have hdvd : 2 ^ k ∣ Nat.card (T.comap φ) := by
    rw [← hk]
    conv_lhs => rw [← hK]
    exact Subgroup.card_map_dvd (T.comap φ) φ
  let Q₀ : Sylow 2 (T.comap φ) := default
  have hQ₀ : 2 ^ k ∣ Nat.card Q₀ := Q₀.pow_dvd_card_of_pow_dvd_card hdvd
  let T' : Subgroup X := (Q₀ : Subgroup (T.comap φ)).map (T.comap φ).subtype
  have hT'p : IsPGroup 2 T' := Q₀.2.map (T.comap φ).subtype
  have hcardT' : Nat.card T' = Nat.card Q₀ := Subgroup.card_subtype (T.comap φ) Q₀
  have hinj := sec39d_jf_inj φ hker T' hT'p
  have hinjOn : Set.InjOn φ (T' : Set X) := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ T' := T'.mul_mem (T'.inv_mem ha) hb
    have h2 : φ (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have := hinj _ h1 h2
    exact (inv_mul_eq_one.1 this)
  have hcardmap : Nat.card (T'.map φ) = Nat.card T' := Nat.card_image_of_injOn hinjOn
  have hle : T'.map φ ≤ T := by
    rw [Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_subtype_le (Q₀ : Subgroup (T.comap φ))
  refine ⟨T', hT'p, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcardmap, hcardT', hk]
  exact Nat.le_of_dvd Nat.card_pos hQ₀

open scoped Pointwise in
theorem sec39d_jf_conj {X : Type*} [Group X] [Finite X] (Q' Q : Sylow 2 X) :
    ∃ g : X, ∀ x ∈ (Q' : Subgroup X), g * x * g⁻¹ ∈ (Q : Subgroup X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q' Q
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (Q' : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q' : Subgroup X) hx
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  simpa using h1

theorem sec39d_jf_comm {X : Type*} [Group X] (S P : Subgroup X) (g : X)
    (hg : ∀ x ∈ S, g * x * g⁻¹ ∈ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * x = 1 → y * y = 1 → x * y = y * x) :
    ∀ x ∈ S, ∀ y ∈ S, x * x = 1 → y * y = 1 → x * y = y * x := by
  intro x hx y hy hx2 hy2
  have hx2' : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hy2' : g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have h := hcomm _ (hg x hx) _ (hg y hy) hx2' hy2'
  have e1 : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  have e2 : g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by rw [e1, e2]; exact h
  exact mul_left_cancel (mul_right_cancel h')

theorem sec39d_jf_count {X : Type*} [Group X] [Finite X] (S P : Subgroup X) (g : X)
    (hg : ∀ x ∈ S, g * x * g⁻¹ ∈ P) :
    Nat.card {x : X // x ∈ S ∧ x * x = 1} ≤ Nat.card {x : X // x ∈ P ∧ x * x = 1} := by
  have key : ∀ x : {x : X // x ∈ S ∧ x * x = 1}, (g * x.1 * g⁻¹) * (g * x.1 * g⁻¹) = 1 := by
    intro x
    calc g * x.1 * g⁻¹ * (g * x.1 * g⁻¹) = g * (x.1 * x.1) * g⁻¹ := by group
      _ = 1 := by rw [x.2.2]; group
  refine Nat.card_le_card_of_injective (fun x => ⟨g * x.1 * g⁻¹, hg x.1 x.2.1, key x⟩) ?_
  intro x y hxy
  have h : g * x.1 * g⁻¹ = g * y.1 * g⁻¹ := congrArg Subtype.val hxy
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h))

theorem sec39d_J_facts {X J : Type*} [Group X] [Finite X] [Group J] (φ : X →* J)
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker))
    (P₀ : Subgroup X) (hP₀ : ∃ Q : Sylow 2 X, (Q : Subgroup X) = P₀) (q : ℕ)
    (hcomm : ∀ x ∈ P₀, ∀ y ∈ P₀, x * x = 1 → y * y = 1 → x * y = y * x)
    (hcount : Nat.card {x : X // x ∈ P₀ ∧ x * x = 1} ≤ q) :
    ∀ T : Subgroup J, IsPGroup 2 T →
      (∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x) ∧
      Nat.card {x : J // x ∈ T ∧ x * x = 1} ≤ q ∧ Nat.card T ≤ Nat.card P₀ := by
  intro T hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP₀
  obtain ⟨T', hT'p, hT'T⟩ := sec39d_lift φ hker T hT
    (by rw [MonoidHom.range_eq_top_of_surjective φ hφ]; exact le_top)
  obtain ⟨Q', hQ'⟩ := hT'p.exists_le_sylow
  obtain ⟨g, hg⟩ := sec39d_jf_conj Q' Q
  have hg' : ∀ x ∈ T', g * x * g⁻¹ ∈ (Q : Subgroup X) := fun x hx => hg x (hQ' hx)
  have hinj := sec39d_jf_inj φ hker T' hT'p
  have hcomm' := sec39d_jf_comm T' _ g hg' hcomm
  have hcount' := (sec39d_jf_count T' _ g hg').trans hcount
  have hmap : ∀ x ∈ T', φ x ∈ T := fun x hx => by
    rw [← hT'T]; exact Subgroup.mem_map_of_mem φ hx
  have hlift : ∀ y ∈ T, y * y = 1 → ∃ x ∈ T', x * x = 1 ∧ φ x = y := by
    intro y hy hy2
    have hy' : y ∈ T'.map φ := by rw [hT'T]; exact hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy'
    refine ⟨x, hx, hinj _ (T'.mul_mem hx hx) ?_, rfl⟩
    rw [map_mul]; exact hy2
  refine ⟨?_, ?_, ?_⟩
  · intro y₁ hy₁ y₂ hy₂ h₁ h₂
    obtain ⟨x₁, hx₁, hx₁2, rfl⟩ := hlift y₁ hy₁ h₁
    obtain ⟨x₂, hx₂, hx₂2, rfl⟩ := hlift y₂ hy₂ h₂
    rw [← map_mul, ← map_mul, hcomm' x₁ hx₁ x₂ hx₂ hx₁2 hx₂2]
  · refine le_trans ?_ hcount'
    refine Nat.card_le_card_of_surjective
      (fun x : {x : X // x ∈ T' ∧ x * x = 1} =>
        (⟨φ x.1, hmap x.1 x.2.1, by rw [← map_mul, x.2.2, map_one]⟩ :
          {y : J // y ∈ T ∧ y * y = 1})) ?_
    rintro ⟨y, hy, hy2⟩
    obtain ⟨x, hx, hx2, rfl⟩ := hlift y hy hy2
    exact ⟨⟨x, hx, hx2⟩, rfl⟩
  · have h1 : Nat.card T ≤ Nat.card T' := by
      rw [← hT'T]; exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd T' φ)
    have h2 : Nat.card T' ≤ Nat.card (Q' : Subgroup X) := Subgroup.card_le_of_le hQ'
    have h3 : Nat.card (Q' : Subgroup X) = Nat.card (Q : Subgroup X) := by
      rw [Sylow.card_eq_multiplicity Q', Sylow.card_eq_multiplicity Q]
    exact h1.trans (h2.trans h3.le)

end Generic39dJF

section Generic39dPhi

theorem sec39d_phi_comm {J : Type*} [Group J]
    (hJ : ∀ T : Subgroup J, IsPGroup 2 T →
      ∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x)
    (T : Subgroup (J × J)) (hT : IsPGroup 2 T) :
    ∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x := by
  intro x hx y hy hxx hyy
  have h1 : IsPGroup 2 (T.map (MonoidHom.fst J J)) := hT.map _
  have h2 : IsPGroup 2 (T.map (MonoidHom.snd J J)) := hT.map _
  have hx1 : x.1 * x.1 = 1 := by simpa using congrArg Prod.fst hxx
  have hx2 : x.2 * x.2 = 1 := by simpa using congrArg Prod.snd hxx
  have hy1 : y.1 * y.1 = 1 := by simpa using congrArg Prod.fst hyy
  have hy2 : y.2 * y.2 = 1 := by simpa using congrArg Prod.snd hyy
  have c1 := hJ _ h1 x.1 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) y.1
    (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩) hx1 hy1
  have c2 := hJ _ h2 x.2 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) y.2
    (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩) hx2 hy2
  exact Prod.ext c1 c2

theorem sec39d_phi_card_inv {J : Type*} [Group J] [Finite J] (q : ℕ)
    (hJ : ∀ T : Subgroup J, IsPGroup 2 T → Nat.card {x : J // x ∈ T ∧ x * x = 1} ≤ q)
    (T : Subgroup (J × J)) (hT : IsPGroup 2 T) :
    Nat.card {x : J × J // x ∈ T ∧ x * x = 1} ≤ q ^ 2 := by
  have h1 : IsPGroup 2 (T.map (MonoidHom.fst J J)) := hT.map _
  have h2 : IsPGroup 2 (T.map (MonoidHom.snd J J)) := hT.map _
  let f : {x : J × J // x ∈ T ∧ x * x = 1} →
      {a : J // a ∈ T.map (MonoidHom.fst J J) ∧ a * a = 1} ×
        {b : J // b ∈ T.map (MonoidHom.snd J J) ∧ b * b = 1} :=
    fun x => (⟨x.1.1, Subgroup.mem_map.mpr ⟨x.1, x.2.1, rfl⟩, by simpa using congrArg Prod.fst x.2.2⟩,
      ⟨x.1.2, Subgroup.mem_map.mpr ⟨x.1, x.2.1, rfl⟩, by simpa using congrArg Prod.snd x.2.2⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    have e1 := congrArg (fun p => p.1.1) hxy
    have e2 := congrArg (fun p => p.2.1) hxy
    exact Subtype.ext (Prod.ext e1 e2)
  calc Nat.card {x : J × J // x ∈ T ∧ x * x = 1}
      ≤ Nat.card ({a : J // a ∈ T.map (MonoidHom.fst J J) ∧ a * a = 1} ×
        {b : J // b ∈ T.map (MonoidHom.snd J J) ∧ b * b = 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = _ * _ := Nat.card_prod _ _
    _ ≤ q * q := Nat.mul_le_mul (hJ _ h1) (hJ _ h2)
    _ = q ^ 2 := (sq q).symm

theorem sec39d_phi_card_swap {J : Type*} [Group J] [Finite J] (q₃ : ℕ)
    (hJ : ∀ T : Subgroup J, IsPGroup 2 T → Nat.card T ≤ q₃)
    (T : Subgroup (J × J)) (hT : IsPGroup 2 T) :
    Nat.card {x : J × J // x ∈ T ∧ x.swap = x} ≤ q₃ := by
  have h1 : IsPGroup 2 (T.map (MonoidHom.fst J J)) := hT.map _
  let f : {x : J × J // x ∈ T ∧ x.swap = x} → T.map (MonoidHom.fst J J) :=
    fun x => ⟨x.1.1, Subgroup.mem_map.mpr ⟨x.1, x.2.1, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have e1 : x.1.1 = y.1.1 := congrArg (fun p => p.1) hxy
    have hx : x.1.2 = x.1.1 := congrArg Prod.fst x.2.2
    have hy : y.1.2 = y.1.1 := congrArg Prod.fst y.2.2
    exact Subtype.ext (Prod.ext e1 (by rw [hx, hy, e1]))
  exact (Nat.card_le_card_of_injective f hf).trans (hJ _ h1)

theorem sec39d_JJ {J : Type*} [Group J] [Finite J] (q q₃ : ℕ)
    (hJ : ∀ T : Subgroup J, IsPGroup 2 T →
      (∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x) ∧
      Nat.card {x : J // x ∈ T ∧ x * x = 1} ≤ q ∧ Nat.card T ≤ q₃)
    (T : Subgroup (J × J)) (hT : IsPGroup 2 T) :
    (∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x) ∧
    Nat.card {x : J × J // x ∈ T ∧ x * x = 1} ≤ q ^ 2 ∧
    Nat.card {x : J × J // x ∈ T ∧ x.swap = x} ≤ q₃ :=
  ⟨sec39d_phi_comm (fun T hT => (hJ T hT).1) T hT,
    sec39d_phi_card_inv q (fun T hT => (hJ T hT).2.1) T hT,
    sec39d_phi_card_swap q₃ (fun T hT => (hJ T hT).2.2) T hT⟩

theorem sec39d_phi_inj {M N : Type*} [Group M] [Group N]
    (Φ : M →* N) (hker : Odd (Nat.card Φ.ker)) (R : Subgroup M) (hR : IsPGroup 2 R)
    {x y : M} (hx : x ∈ R) (hy : y ∈ R) (h : Φ x = Φ y) : x = y := by
  have hg : x⁻¹ * y ∈ R := R.mul_mem (R.inv_mem hx) hy
  have hk : x⁻¹ * y ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨k, hk2⟩ := IsPGroup.exists_orderOf_eq_pow hR (⟨x⁻¹ * y, hg⟩ : R)
  have h1 : orderOf (x⁻¹ * y) = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk2
  have h2 : orderOf (x⁻¹ * y) ∣ Nat.card Φ.ker := by
    have := orderOf_dvd_natCard (⟨x⁻¹ * y, hk⟩ : Φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Φ.ker) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hker)
  have h3 : orderOf (x⁻¹ * y) = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_of_eq h1) h2
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h3)

theorem sec39d_Phi_facts {M J : Type*} [Group M] [Finite M] [Group J] [Finite J] (q q₃ : ℕ)
    (hJ : ∀ T : Subgroup J, IsPGroup 2 T →
      (∀ x ∈ T, ∀ y ∈ T, x * x = 1 → y * y = 1 → x * y = y * x) ∧
      Nat.card {x : J // x ∈ T ∧ x * x = 1} ≤ q ∧ Nat.card T ≤ q₃)
    (Φ : M →* J × J) (hker : Odd (Nat.card Φ.ker)) (τ : M ≃* M)
    (hτ : ∀ m, Φ (τ m) = (Φ m).swap) (R : Subgroup M) (hR : IsPGroup 2 R) :
    (∀ x ∈ R, ∀ y ∈ R, x * x = 1 → y * y = 1 → x * y = y * x) ∧
    Nat.card {x : M // x ∈ R ∧ x * x = 1} ≤ q ^ 2 ∧
    Nat.card {x : M // x ∈ R ∧ τ x = x} ≤ q₃ := by
  have hinj : ∀ {x y : M}, x ∈ R → y ∈ R → Φ x = Φ y → x = y :=
    fun hx hy h => sec39d_phi_inj Φ hker R hR hx hy h
  have hT : IsPGroup 2 (R.map Φ) := hR.map Φ
  obtain ⟨hcomm, hcard, hswap⟩ := sec39d_JJ q q₃ hJ (R.map Φ) hT
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxx hyy
    have hx' : Φ x ∈ R.map Φ := Subgroup.mem_map_of_mem Φ hx
    have hy' : Φ y ∈ R.map Φ := Subgroup.mem_map_of_mem Φ hy
    have hxx' : Φ x * Φ x = 1 := by rw [← map_mul, hxx, map_one]
    have hyy' : Φ y * Φ y = 1 := by rw [← map_mul, hyy, map_one]
    have hc := hcomm _ hx' _ hy' hxx' hyy'
    exact hinj (R.mul_mem hx hy) (R.mul_mem hy hx) (by rw [map_mul, map_mul]; exact hc)
  · refine le_trans (Nat.card_le_card_of_injective
      (fun x : {x : M // x ∈ R ∧ x * x = 1} =>
        (⟨Φ x.1, Subgroup.mem_map_of_mem Φ x.2.1, by rw [← map_mul, x.2.2, map_one]⟩ :
          {u : J × J // u ∈ R.map Φ ∧ u * u = 1})) ?_) hcard
    intro x y hxy
    exact Subtype.ext (hinj x.2.1 y.2.1 (congrArg Subtype.val hxy))
  · refine le_trans (Nat.card_le_card_of_injective
      (fun x : {x : M // x ∈ R ∧ τ x = x} =>
        (⟨Φ x.1, Subgroup.mem_map_of_mem Φ x.2.1, by rw [← hτ, x.2.2]⟩ :
          {u : J × J // u ∈ R.map Φ ∧ u.swap = u})) ?_) hswap
    intro x y hxy
    exact Subtype.ext (hinj x.2.1 y.2.1 (congrArg Subtype.val hxy))

end Generic39dPhi

section Generic39dNormal

theorem sec39d_nonabelian_simple_not_pGroup {X : Type*} [Group X] [Finite X] (D : Subgroup X)
    (hs : IsSimpleGroup ↥D) (hnab : ∃ x y : ↥D, x * y ≠ y * x) : ¬ IsPGroup 2 D := by
  intro hp
  haveI : Nontrivial ↥D := by
    obtain ⟨x, y, hxy⟩ := hnab
    refine ⟨⟨x, y, fun h => hxy ?_⟩⟩
    rw [h]
  haveI := hp.center_nontrivial
  have hz : Subgroup.center ↥D = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥D) with h | h
    · exfalso
      have := (Subgroup.center ↥D).nontrivial_iff_ne_bot.1 inferInstance
      exact this h
    · exact h
  obtain ⟨x, y, hxy⟩ := hnab
  apply hxy
  have hx : x ∈ Subgroup.center ↥D := by rw [hz]; exact mem_top x
  exact (Subgroup.mem_center_iff.1 hx y).symm

theorem sec39d_inf_eq_bot_of_simple {X : Type*} [Group X] [Finite X] (D T : Subgroup X)
    (hs : IsSimpleGroup ↥D) (hnab : ∃ x y : ↥D, x * y ≠ y * x) (hT2 : IsPGroup 2 T)
    (hn : ∀ g ∈ D, ∀ x ∈ T, g * x * g⁻¹ ∈ T) : T ⊓ D = ⊥ := by
  have hN : ((T ⊓ D).subgroupOf D).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [mem_subgroupOf, mem_inf] at hn' ⊢
    exact ⟨hn _ g.2 _ hn'.1, mul_mem (mul_mem g.2 hn'.2) (inv_mem g.2)⟩
  haveI := hN
  rcases hs.eq_bot_or_eq_top_of_normal ((T ⊓ D).subgroupOf D) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : D) ∈ (T ⊓ D).subgroupOf D := mem_subgroupOf.2 hx
    rw [h] at this
    have h1 : (⟨x, hx.2⟩ : D) = 1 := (mem_bot).1 this
    exact (mem_bot).2 (congrArg Subtype.val h1)
  · exfalso
    refine sec39d_nonabelian_simple_not_pGroup D hs hnab (hT2.to_le fun x hx => ?_)
    have : (⟨x, hx⟩ : D) ∈ (T ⊓ D).subgroupOf D := by rw [h]; exact mem_top _
    exact (mem_subgroupOf.1 this).1

open scoped Pointwise in
theorem sec39d_exists_mul {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) {x : X} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ (A : Set X) * (B : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hB]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem sec39d_normal_two_trivial {X : Type*} [Group X] [Finite X] (D₁ D₂ T : Subgroup X)
    (hs₁ : IsSimpleGroup ↥D₁) (hnab₁ : ∃ x y : ↥D₁, x * y ≠ y * x)
    (hs₂ : IsSimpleGroup ↥D₂) (hnab₂ : ∃ x y : ↥D₂, x * y ≠ y * x)
    (hcomm : ⁅D₁, D₂⁆ = ⊥) (hT2 : IsPGroup 2 T) (hTD : T ≤ D₁ ⊔ D₂)
    (hTn : ∀ g ∈ D₁ ⊔ D₂, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hcent : centralizer ((D₁ ⊔ D₂ : Subgroup X) : Set X) = ⊥) : T = ⊥ := by
  have h12 : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ (⁅D₁, D₂⁆ : Subgroup X) := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, mem_bot, commutatorElement_def] at h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hT1 : T ⊓ D₁ = ⊥ := sec39d_inf_eq_bot_of_simple D₁ T hs₁ hnab₁ hT2
    (fun g hg x hx => hTn g (mem_sup_left hg) x hx)
  have hT2' : T ⊓ D₂ = ⊥ := sec39d_inf_eq_bot_of_simple D₂ T hs₂ hnab₂ hT2
    (fun g hg x hx => hTn g (mem_sup_right hg) x hx)
  have hN₂ : D₂ ≤ normalizer (D₁ : Set X) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun a => by
      constructor
      · intro ha
        rw [show b * a * b⁻¹ = a by rw [← h12 a ha b hb]; group]
        exact ha
      · intro hba
        have e : b⁻¹ * (b * a * b⁻¹) * b = a := by group
        have e2 : b⁻¹ * (b * a * b⁻¹) * b = b * a * b⁻¹ := by
          rw [← h12 _ hba b⁻¹ (inv_mem hb)]
          group
        rw [← e, e2]
        exact hba
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := sec39d_exists_mul hN₂ (hTD hx)
  have hc1 : ∀ g ∈ D₁, (y₁ * y₂) * g = g * (y₁ * y₂) := by
    intro g hg
    have hc : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ ∈ T ⊓ D₁ := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have e : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ = (y₁ * y₂) * (g * (y₁ * y₂)⁻¹ * g⁻¹) := by
          group
        rw [e]
        exact mul_mem hx (hTn g (mem_sup_left hg) _ (inv_mem hx))
      · have e : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ = (y₁ * g * y₁⁻¹) * g⁻¹ := by
          calc (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹
              = y₁ * (y₂ * g * y₂⁻¹) * y₁⁻¹ * g⁻¹ := by group
            _ = (y₁ * g * y₁⁻¹) * g⁻¹ := by rw [show y₂ * g * y₂⁻¹ = g by
                rw [← h12 g hg y₂ hy₂]; group]
        rw [e]
        exact mul_mem (mul_mem (mul_mem hy₁ hg) (inv_mem hy₁)) (inv_mem hg)
    rw [hT1, mem_bot] at hc
    calc (y₁ * y₂) * g = ((y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹) * (g * (y₁ * y₂)) := by group
      _ = g * (y₁ * y₂) := by rw [hc, one_mul]
  have hc2 : ∀ g ∈ D₂, (y₁ * y₂) * g = g * (y₁ * y₂) := by
    intro g hg
    have hc : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ ∈ T ⊓ D₂ := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have e : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ = (y₁ * y₂) * (g * (y₁ * y₂)⁻¹ * g⁻¹) := by
          group
        rw [e]
        exact mul_mem hx (hTn g (mem_sup_right hg) _ (inv_mem hx))
      · have e : (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹ = (y₂ * g * y₂⁻¹) * g⁻¹ := by
          calc (y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹
              = y₁ * (y₂ * g * y₂⁻¹) * y₁⁻¹ * g⁻¹ := by group
            _ = (y₂ * g * y₂⁻¹) * g⁻¹ := by
                rw [show y₁ * (y₂ * g * y₂⁻¹) * y₁⁻¹ = y₂ * g * y₂⁻¹ by
                  rw [h12 y₁ hy₁ (y₂ * g * y₂⁻¹) (show y₂ * g * y₂⁻¹ ∈ D₂ from
                    mul_mem (mul_mem hy₂ hg) (inv_mem hy₂))]; group]
        rw [e]
        exact mul_mem (mul_mem (mul_mem hy₂ hg) (inv_mem hy₂)) (inv_mem hg)
    rw [hT2', mem_bot] at hc
    calc (y₁ * y₂) * g = ((y₁ * y₂) * g * (y₁ * y₂)⁻¹ * g⁻¹) * (g * (y₁ * y₂)) := by group
      _ = g * (y₁ * y₂) := by rw [hc, one_mul]
  have hle : D₁ ⊔ D₂ ≤ Subgroup.centralizer ({y₁ * y₂} : Set X) :=
    sup_le (fun g hg => by rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc1 g hg).symm)
      (fun g hg => by rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc2 g hg).symm)
  have hmem : y₁ * y₂ ∈ centralizer ((D₁ ⊔ D₂ : Subgroup X) : Set X) :=
    mem_centralizer_iff.2 fun g hg => by
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      exact this
  rw [hcent] at hmem
  exact hmem

end Generic39dNormal

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}




theorem sec39d_ec_z_mem {z : G} (hz : z ∈ d.CPI₆) : z ∈ d.P ∧ z ∈ d.N₂ := by
  obtain ⟨g, hg, rfl⟩ := hz
  exact ⟨⟨g, patSub_le_U _ _ hg, rfl⟩, ⟨g, patSub_sI₆_le_N₂sub hg, rfl⟩⟩

theorem sec39d_ec_z_not_mem_A₂ {z : G} (hz : z ∈ d.CPI₆) (hz1 : z ≠ 1) : z ∉ d.A₂ := by
  obtain ⟨g, hg, rfl⟩ := hz
  rintro ⟨g', hg', hgg⟩
  have e := d.η_injOn (A₂sub_le_U hg') (patSub_le_U _ _ hg) hgg
  rw [e] at hg'
  have h0 := (mem_A₂sub.1 hg').2.2.2
  have e1 := eq_of_mem_patSub_sI₆ hg (one_mem _)
    (by rw [h0, CFSG.RankThree.PartOne.U5K.Hyp.mat_one, Matrix.one_apply_ne (by decide)])
  exact hz1 (by rw [e1, map_one])

theorem sec39d_ec_z_NC (hd : d.Hyp) {z : G} (hz : z ∈ d.CPI₆) :
    z ∈ normalizer (d.ZtP : Set G) ∧ z ∈ centralizer ({d.t} : Set G) := by
  have h := Subgroup.mem_inf.1 (hd.N₂_le_K₀ (sec39d_ec_z_mem hz).2)
  exact ⟨(Subgroup.mem_inf.1 h.1).1, h.2⟩

theorem sec39d_ec_key {z : G} (hz : z ∈ d.CPI₆) (hz1 : z ≠ 1) {a : G}
    (ha : a ∈ d.A₂) (hc : ⁅a, z⁆ ∈ d.Zp) : a ∈ d.A₂ ⊓ d.A₃ :=
  (sec2_2_five d).2 z (sec39d_ec_z_mem hz).1 (sec39d_ec_z_not_mem_A₂ hz hz1) a ha hc

open CFSG.RankThree.PartOne.U5K.Hyp in
theorem sec39d_ec_card_A₂A₃ : Nat.card (d.A₂ ⊓ d.A₃ : Subgroup G) = (2 ^ f) ^ 5 := by
  have e : d.A₂ ⊓ d.A₃ = d.pull (A₂sub h ⊓ Ssub h) :=
    (d.pull_inf A₂sub_le_U (Ssub_le_Usub)).symm
  rw [e, d.card_pull (inf_le_left.trans A₂sub_le_U), card_A₂sub_inf_Ssub]

open CFSG.RankThree.PartOne.U5K.Hyp in
theorem sec39d_ec_Zp_le_A₃ : d.Zp ≤ d.A₃ :=
  d.pull_mono (ZPsub_le_Vsub.trans Vsub_le_Ssub)

theorem sec39d_ec_card_VB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hVL : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v) :
    Nat.card (d.V ⊔ (d.A₂ ⊓ d.A₃) : Subgroup G) = (2 ^ f) ^ 6 := by
  have hB : d.A₂ ⊓ d.A₃ ≤ normalizer (d.V : Set G) := fun b hb =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun v hv =>
      hVL v hv b (d.E_le_L₂ (hd.VA_le_E hGMS (mem_sup_right hb.1))))
  have h1 := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hB
  have hinf : (d.V ⊓ (d.A₂ ⊓ d.A₃) : Subgroup G) = d.Zp := by
    rw [← inf_assoc, hd.V_inf_A₂]
    exact inf_eq_left.2 (sec39d_ec_Zp_le_A₃ (d := d))
  rw [hinf, d.card_Zp, hd.card_V, sec39d_ec_card_A₂A₃] at h1
  have hq : 0 < 2 ^ f := by positivity
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h1]
  ring

theorem sec39d_ec_ker_le (hd : d.Hyp) (hVL : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v) {z : G}
    (hz : z ∈ d.CPI₆) (hz1 : z ≠ 1) {u : G} (hu : ⁅u, z⁆ ∈ d.V) (huVA : u ∈ d.V ⊔ d.A₂) :
    u ∈ d.V ⊔ (d.A₂ ⊓ d.A₃) := by
  obtain ⟨v, hv, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA huVA
  obtain ⟨hzN, hzC⟩ := sec39d_ec_z_NC hd hz
  have hzL : z ∈ d.L₂ := d.N₂_le_L₂ (sec39d_ec_z_mem hz).2
  have hvz : v * z = z * v := hVL v hv z hzL
  have hw : ⁅a, z⁆ ∈ d.A₂ := by
    have h1 := mul_mem ha (hd.conj_mem_A₂ hzN hzC (inv_mem ha))
    simpa only [commutatorElement_def, mul_assoc] using h1
  have hvw : v * ⁅a, z⁆ = ⁅a, z⁆ * v := hd.V_comm_A₂ hv hw
  have e1 : ⁅v * a, z⁆ = (v * ⁅a, z⁆ * v⁻¹) * ⁅v, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e1, commutatorElement_eq_one_iff_mul_comm.2 hvz, mul_one, hvw, mul_inv_cancel_right] at hu
  have hZ : ⁅a, z⁆ ∈ d.Zp := by
    rw [← hd.V_inf_A₂]
    exact ⟨hu, hw⟩
  exact mul_mem (mem_sup_left hv) (mem_sup_right (sec39d_ec_key hz hz1 ha hZ))

theorem sec39d_ec_range (hd : d.Hyp) {z : G} (hz : z ∈ d.CPI₆) (hz1 : z ≠ 1)
    (ψ : d.E →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂)
    (hker : ψ.ker = (d.V ⊔ d.A₂).subgroupOf d.E)
    (hequiv : ∀ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (e : d.E)
        (a : d.A₂) (he : c * e * c⁻¹ ∈ d.E) (ha : c * a * c⁻¹ ∈ d.A₂),
        ψ e = QuotientGroup.mk a → ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩)
    {u : G} (huE : u ∈ d.E) (hu : ⁅u, z⁆ ∈ d.V) :
    ∃ a : d.A₂, (a : G) ∈ d.A₃ ∧ ψ ⟨u, huE⟩ = QuotientGroup.mk a := by
  obtain ⟨hzN, hzC⟩ := sec39d_ec_z_NC hd hz
  have hzL : z ∈ d.L₂ := d.N₂_le_L₂ (sec39d_ec_z_mem hz).2
  have hzB : z ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    ⟨hd.normalizer_ZtP_le_normalizer_B₂ hzN, hzC⟩
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨u, huE⟩)
  have hzuE : z * u * z⁻¹ ∈ d.E :=
    (mem_normalizer_iff.1 (d.L₂_le_normalizer_E hzL) u).1 huE
  have hzaA : z * (a : G) * z⁻¹ ∈ d.A₂ := hd.conj_mem_A₂ hzN hzC a.2
  have h1 := hequiv z hzB ⟨u, huE⟩ a hzuE hzaA ha.symm
  have hvE : ⁅u, z⁆⁻¹ ∈ d.E := d.V_le_E (inv_mem hu)
  have h2 : (⟨z * u * z⁻¹, hzuE⟩ : d.E) = ⟨⁅u, z⁆⁻¹, hvE⟩ * ⟨u, huE⟩ := by
    apply Subtype.ext
    change z * u * z⁻¹ = ⁅u, z⁆⁻¹ * u
    simp only [commutatorElement_def]
    group
  have h3 : ψ ⟨⁅u, z⁆⁻¹, hvE⟩ = 1 := by
    have : (⟨⁅u, z⁆⁻¹, hvE⟩ : d.E) ∈ ψ.ker := by
      rw [hker, mem_subgroupOf]
      exact mem_sup_left (inv_mem hu)
    exact this
  rw [h2, map_mul, h3, one_mul, ← ha] at h1
  have hw' := QuotientGroup.eq.1 h1.symm
  have hw : (z * (a : G) * z⁻¹)⁻¹ * (a : G) ∈ d.Zp := mem_subgroupOf.1 hw'
  have hc : ⁅(a : G), z⁆ ∈ d.Zp := by
    have e : ⁅(a : G), z⁆ = (a : G) * ((z * (a : G) * z⁻¹)⁻¹ * (a : G)) * (a : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, ← hd.V_comm_A₂ (hd.Zp_le_V hw) a.2, mul_inv_cancel_right]
    exact hw
  exact ⟨a, (sec39d_ec_key hz hz1 a.2 hc).2, ha.symm⟩

theorem sec39d_ec_card_range_le (R : Subgroup (d.A₂ ⧸ d.Zp.subgroupOf d.A₂))
    (hR : ∀ x ∈ R, ∃ a : d.A₂, (a : G) ∈ d.A₃ ∧ x = QuotientGroup.mk a) :
    Nat.card R ≤ (2 ^ f) ^ 4 := by
  set N := d.Zp.subgroupOf d.A₂ with hN
  set Bs : Subgroup d.A₂ := (d.A₂ ⊓ d.A₃).subgroupOf d.A₂ with hBs
  let κ : Bs →* d.A₂ ⧸ N := (QuotientGroup.mk' N).comp Bs.subtype
  have hRκ : R ≤ κ.range := by
    intro x hx
    obtain ⟨a, ha3, rfl⟩ := hR x hx
    exact ⟨⟨a, mem_subgroupOf.2 ⟨a.2, ha3⟩⟩, rfl⟩
  have hcardB : Nat.card Bs = (2 ^ f) ^ 5 := by
    rw [← sec39d_ec_card_A₂A₃ (d := d)]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hZ : d.Zp ≤ d.A₂ ⊓ d.A₃ := le_inf d.Zp_le_A₂ sec39d_ec_Zp_le_A₃
  have hker : 2 ^ f ≤ Nat.card κ.ker := by
    let ι : d.Zp → κ.ker := fun x =>
      ⟨⟨⟨x, d.Zp_le_A₂ x.2⟩, mem_subgroupOf.2 (hZ x.2)⟩,
        (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 x.2)⟩
    have hι : Function.Injective ι := fun x y hxy =>
      Subtype.ext (congrArg (fun w : κ.ker => ((w.1 : d.A₂) : G)) hxy)
    have := Nat.card_le_card_of_injective ι hι
    rwa [d.card_Zp] at this
  have h1 := Subgroup.card_ker_mul_card_range κ
  have h2 := Subgroup.card_le_of_le hRκ
  have hq : 0 < 2 ^ f := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hq
  calc 2 ^ f * Nat.card R ≤ Nat.card κ.ker * Nat.card κ.range := Nat.mul_le_mul hker h2
    _ = (2 ^ f) ^ 5 := by rw [h1, hcardB]
    _ = 2 ^ f * (2 ^ f) ^ 4 := by ring

theorem sec39d_card_ECent_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hVL : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v) {z : G} (hz : z ∈ d.CPI₆) (hz1 : z ≠ 1) :
    Nat.card (sec39dECent d.V d.E (fun v hv e he => hVL v hv e (d.E_le_L₂ he)) z) ≤
      (2 ^ f) ^ 10 := by
  obtain ⟨ψ, -, hker, -, hequiv⟩ := hd.exists_E_hom hGMS
  set Y := sec39dECent d.V d.E (fun v hv e he => hVL v hv e (d.E_le_L₂ he)) z with hY
  have hYE : Y ≤ d.E := fun u hu => (sec39d_mem_ECent.1 hu).1
  let φ : Y →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂ := ψ.comp (Subgroup.inclusion hYE)
  have hmem : ∀ x : φ.ker, (x.1 : G) ∈ d.V ⊔ (d.A₂ ⊓ d.A₃) := fun x => by
    have hx : (⟨(x.1 : G), hYE x.1.2⟩ : d.E) ∈ ψ.ker := x.2
    rw [hker, mem_subgroupOf] at hx
    exact sec39d_ec_ker_le hd hVL hz hz1 (sec39d_mem_ECent.1 x.1.2).2 hx
  have hk : Nat.card φ.ker ≤ (2 ^ f) ^ 6 := by
    rw [← sec39d_ec_card_VB hGMS hd hVL]
    exact Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨(x.1 : G), hmem x⟩ : ↥(d.V ⊔ (d.A₂ ⊓ d.A₃))))
      fun x y hxy => by simpa using hxy
  have hr : Nat.card φ.range ≤ (2 ^ f) ^ 4 := by
    refine sec39d_ec_card_range_le φ.range ?_
    rintro _ ⟨u, rfl⟩
    obtain ⟨huE, hu⟩ := sec39d_mem_ECent.1 u.2
    exact sec39d_ec_range hd hz hz1 ψ hker hequiv huE hu
  calc Nat.card Y = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ (2 ^ f) ^ 6 * (2 ^ f) ^ 4 := Nat.mul_le_mul hk hr
    _ = (2 ^ f) ^ 10 := by ring






theorem sec39d_N₂_le_M₂ (d : Data G h) : d.N₂ ≤ d.M₂ := by
  intro n hn
  refine ⟨⟨n, d.N₂_le_centralizer_I₂ hn⟩, Subgroup.subset_normalClosure ?_, rfl⟩
  exact mem_subgroupOf.2 hn

theorem sec39d_M₂_le_centralizer (d : Data G h) : d.M₂ ≤ centralizer (d.I₂ : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem sec39d_t_mem_normalizer_M₂ (hd : d.Hyp) : d.t ∈ normalizer (d.M₂ : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  obtain ⟨x, hx, rfl⟩ := hz
  have hn : (normalClosure ((d.N₂.subgroupOf (centralizer (d.I₂ : Set G)) :
      Subgroup (centralizer (d.I₂ : Set G))) : Set (centralizer (d.I₂ : Set G)))).Normal :=
    inferInstance
  refine ⟨⟨d.t, hd.t_mem_centralizer_I₂⟩ * x * ⟨d.t, hd.t_mem_centralizer_I₂⟩⁻¹,
    hn.conj_mem x hx _, ?_⟩
  simp

theorem sec39d_odd_card_of_le {X H' : Type*} [Group X] [Group H'] (O : Subgroup H')
    (hO : Odd (Nat.card O)) (g : X →* H') (hg : Function.Injective g) (K : Subgroup X)
    (hK : ∀ k ∈ K, g k ∈ O) : Odd (Nat.card K) := by
  let g' : K →* O := (g.comp K.subtype).codRestrict O (fun k => hK k.1 k.2)
  have hinj : Function.Injective g' := fun a b hab =>
    Subtype.ext (hg (congrArg Subtype.val hab))
  exact Odd.of_dvd_nat hO (Subgroup.card_dvd_of_injective g' hinj)

theorem sec39d_structure (hp : d.ProductCaseHyp) :
    ∃ (J : Type) (_ : Group J) (_ : Finite J) (Φ : ↥d.M₂ →* J × J) (φ : ↥d.N₂ →* J),
      Odd (Nat.card Φ.ker) ∧ Function.Surjective φ ∧ Odd (Nat.card φ.ker) ∧
      (∀ n : ↥d.N₂, Φ ⟨n, sec39d_N₂_le_M₂ d n.2⟩ = (φ n, φ n)) ∧
      (∀ (z : G) (hz : z ∈ d.M₂) (hz' : d.t * z * d.t⁻¹ ∈ d.M₂),
          Φ ⟨d.t * z * d.t⁻¹, hz'⟩ = (Φ ⟨z, hz⟩).swap) ∧
      (d.M₂ ≤ normalizer (d.E : Set G) → IsPGroup 2 d.E → d.M₂ ⊓ d.E = ⊥) := by
  have hd := hp.hyp
  obtain ⟨hSharp, hM⟩ := hd.sec3_3_two hp.gms
  set H : Subgroup G := centralizer (d.I₂ : Set G) with hH
  set O : Subgroup ↥H := standardComponentOddCore ↥H with hO
  set θ : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hθ
  set A : Subgroup (↥H ⧸ O) := (d.N₂.subgroupOf H).map θ with hA
  unfold GMSK.SharpOutcome at hSharp
  obtain ⟨hOne, -⟩ := hSharp
  obtain ⟨-, -, hJle, hnc, hcent, halt, -⟩ := hOne
  have hns := hp.caseB
  unfold Data.M₂Linear at hns
  unfold SteinbergBV.OneOrTwoLayerAlternatives at halt
  have hP2 := halt.elim (fun h1 => absurd (by rw [← hnc]; exact h1.1.1) hns) (fun h2 => h2.1)
  obtain ⟨D₁, D₂, -, -, hne, hs₁, hnab₁, hs₂, hnab₂, hsup, hinf, hcomm, hconj, hJeq, ψ, hψJ, hψt⟩ := hP2
  have hM₂H : d.M₂ ≤ H := sec39d_M₂_le_centralizer d
  have hN₂H : d.N₂ ≤ H := d.N₂_le_centralizer_I₂
  have hθM : ∀ z (hz : z ∈ d.M₂), θ ⟨z, hM₂H hz⟩ ∈ normalClosure (A : Set (↥H ⧸ O)) := by
    intro z hz
    rw [hnc, ← hM]
    exact ⟨⟨z, hM₂H hz⟩, mem_subgroupOf.2 hz, rfl⟩
  have hOodd : Odd (Nat.card O) := GMSK.odd_card_standardComponentOddCore ↥H
  let θM : ↥d.M₂ →* ↥(normalClosure (A : Set (↥H ⧸ O))) :=
    (θ.comp (Subgroup.inclusion hM₂H)).codRestrict _ (fun z => hθM z.1 z.2)
  let Φ : ↥d.M₂ →* ↥A × ↥A := ψ.toMonoidHom.comp θM
  let φ : ↥d.N₂ →* ↥A := (θ.comp (Subgroup.inclusion hN₂H)).codRestrict A
    (fun n => ⟨⟨n.1, hN₂H n.2⟩, mem_subgroupOf.2 n.2, rfl⟩)
  refine ⟨↥A, inferInstance, inferInstance, Φ, φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sec39d_odd_card_of_le O hOodd (Subgroup.inclusion hM₂H)
      (Subgroup.inclusion_injective hM₂H) Φ.ker fun z hz => ?_
    have h1 : ψ (θM z) = 1 := hz
    have h2 : θM z = 1 := (map_eq_one_iff _ ψ.injective).1 h1
    have h3 : θ (Subgroup.inclusion hM₂H z) = 1 := congrArg Subtype.val h2
    exact (QuotientGroup.eq_one_iff _).1 h3
  · rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n.1, mem_subgroupOf.1 hn⟩, rfl⟩
  · refine sec39d_odd_card_of_le O hOodd (Subgroup.inclusion hN₂H)
      (Subgroup.inclusion_injective hN₂H) φ.ker fun n hn => ?_
    have h2 : φ n = 1 := hn
    have h3 : θ (Subgroup.inclusion hN₂H n) = 1 := congrArg Subtype.val h2
    exact (QuotientGroup.eq_one_iff _).1 h3
  · intro n
    have hj : θ (Subgroup.inclusion hN₂H n) ∈ A := ⟨⟨n.1, hN₂H n.2⟩, mem_subgroupOf.2 n.2, rfl⟩
    exact hψJ _ hj (hθM n.1 (sec39d_N₂_le_M₂ d n.2))
  · intro z hz hz'
    set t' : ↥H := ⟨d.t, hd.t_mem_centralizer_I₂⟩ with ht'def
    have ht'1 : t' * t' = 1 := Subtype.ext hd.t_mul_t
    have ht'i : (θ t')⁻¹ = θ t' :=
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, ht'1, map_one])
    have hcd : θ ⟨d.t * z * d.t⁻¹, hM₂H hz'⟩ = (θ t')⁻¹ * θ ⟨z, hM₂H hz⟩ * θ t' := by
      have e : (⟨d.t * z * d.t⁻¹, hM₂H hz'⟩ : ↥H) = t' * ⟨z, hM₂H hz⟩ * t'⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, ht'i]
    have key := hψt (θ ⟨z, hM₂H hz⟩) (hθM z hz) (hcd ▸ hθM _ hz')
    have e2 : (⟨θ ⟨d.t * z * d.t⁻¹, hM₂H hz'⟩, hθM _ hz'⟩ : ↥(normalClosure (A : Set (↥H ⧸ O)))) =
        ⟨(θ t')⁻¹ * θ ⟨z, hM₂H hz⟩ * θ t', hcd ▸ hθM _ hz'⟩ := Subtype.ext hcd
    show ψ ⟨θ ⟨d.t * z * d.t⁻¹, hM₂H hz'⟩, hθM _ hz'⟩ = (ψ ⟨θ ⟨z, hM₂H hz⟩, hθM z hz⟩).swap
    rw [e2]
    exact key
  · intro hME hE2
    have hNnM : d.M₂ ⊓ d.E ≤ d.M₂ := inf_le_left
    have hNnH : d.M₂ ⊓ d.E ≤ H := hNnM.trans hM₂H
    let T : Subgroup (↥H ⧸ O) := ((d.M₂ ⊓ d.E).subgroupOf H).map θ
    have hT2 : IsPGroup 2 T := ((hE2.to_le (inf_le_right : d.M₂ ⊓ d.E ≤ d.E)).comap_subtype).map θ
    have hTD : T ≤ D₁ ⊔ D₂ := by
      rw [hsup, hnc, ← hM]
      exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hNnM (mem_subgroupOf.1 hx))
    have hTn : ∀ g ∈ D₁ ⊔ D₂, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
      intro g hg x hx
      rw [hsup, hnc, ← hM] at hg
      obtain ⟨m, hm, rfl⟩ := hg
      obtain ⟨n, hn, rfl⟩ := hx
      refine ⟨m * n * m⁻¹, ?_, by simp⟩
      have hm' : (m : G) ∈ d.M₂ := mem_subgroupOf.1 hm
      have hn' : (n : G) ∈ d.M₂ ⊓ d.E := mem_subgroupOf.1 hn
      have hmN : (m : G) ∈ normalizer (d.E : Set G) := hME hm'
      have h1 : (m : G) * n * (m : G)⁻¹ ∈ d.E :=
        (mem_normalizer_iff.1 hmN (n : G)).1 (mem_inf.1 hn').2
      exact mem_subgroupOf.2 (mem_inf.2 ⟨mul_mem (mul_mem hm' (mem_inf.1 hn').1) (inv_mem hm'), h1⟩)
    have hcent' : centralizer ((D₁ ⊔ D₂ : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) = ⊥ := by
      rw [hsup]; exact hcent
    have hT := sec39d_normal_two_trivial D₁ D₂ T hs₁ hnab₁ hs₂ hnab₂ hcomm hT2 hTD hTn hcent'
    rw [eq_bot_iff]
    intro n hn
    have hnO : (⟨n, hNnH hn⟩ : ↥H) ∈ O := by
      have h1 : θ ⟨n, hNnH hn⟩ ∈ T := ⟨⟨n, hNnH hn⟩, mem_subgroupOf.2 hn, rfl⟩
      rw [hT, mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := hE2 ⟨n, hn.2⟩
    have hk' : (⟨⟨n, hNnH hn⟩, hnO⟩ : ↥O) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf (⟨⟨n, hNnH hn⟩, hnO⟩ : ↥O) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h3 : orderOf (⟨⟨n, hNnH hn⟩, hnO⟩ : ↥O) ∣ Nat.card O := orderOf_dvd_natCard _
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hio' : Odd (orderOf (⟨⟨n, hNnH hn⟩, hnO⟩ : ↥O)) :=
      Odd.of_dvd_nat (GMSK.odd_card_standardComponentOddCore ↥H) h3
    have hi0 : i = 0 := by
      by_contra hne'
      rw [hio] at hio'
      exact (Nat.not_even_iff_odd.2 hio') ((Nat.even_pow.2 ⟨even_two, hne'⟩))
    rw [hi0, pow_zero] at hio
    have := orderOf_eq_one_iff.1 hio
    have h4 : n = 1 := congrArg (fun x : ↥O => ((x : ↥H) : G)) this
    rw [h4]
    exact one_mem _




theorem sec39d_D_char {S : Subgroup G} (hc : d.Sec39c S) :
    (d.D.subgroupOf S).Characteristic := by
  obtain ⟨-, hW, hD⟩ := hc
  have hWleS : d.W ≤ S := hW ▸ map_subtype_le _
  have hWS : d.W.subgroupOf S = Subgroup.upperCentralSeries ↥S 2 := by
    rw [← hW, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  have key : d.D.subgroupOf S =
      Subgroup.centralizer ((Subgroup.upperCentralSeries ↥S 2 : Subgroup S) : Set S) := by
    ext x
    rw [mem_subgroupOf, hD, mem_inf, Subgroup.mem_centralizer_iff, ← hWS]
    constructor
    · rintro ⟨-, hx⟩ y hy
      exact Subtype.ext (mem_centralizer_iff.1 hx (y : G) (mem_subgroupOf.1 hy))
    · intro hx
      refine ⟨x.2, mem_centralizer_iff.2 fun w hw => ?_⟩
      exact congrArg Subtype.val (hx ⟨w, hWleS hw⟩ (mem_subgroupOf.2 hw))
  rw [key]
  infer_instance

theorem sec39d_mem_V_iff {S : Subgroup G} (hV : CFSG.centerIn S = d.V) (v : S) :
    (v : G) ∈ d.V ↔ v ∈ Subgroup.center ↥S := by
  rw [← hV, CFSG.centerIn, mem_inf, Subgroup.mem_center_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨-, hv⟩ w
    exact Subtype.ext (hv (w : G) w.2)
  · intro hv
    exact ⟨v.2, fun w hw => congrArg Subtype.val (hv ⟨w, hw⟩)⟩

theorem sec39d_E_char (S : Subgroup G) (hV : CFSG.centerIn S = d.V) (hES : d.E ≤ S)
    (hcardE : Nat.card d.E = (2 ^ f) ^ 14) (hEab : ElemAbMod d.V d.E)
    (key : ∀ X : Subgroup G, d.V ≤ X → X ≤ S → ElemAbMod d.V X →
      (2 ^ f) ^ 14 ≤ Nat.card X → X = d.E) :
    (d.E.subgroupOf S).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro ϕ
  set E' := d.E.subgroupOf S with hE'
  have hZ : ∀ v : S, ϕ v ∈ Subgroup.center ↥S ↔ v ∈ Subgroup.center ↥S := by
    intro v
    have hc : (Subgroup.center ↥S).map ϕ.toMonoidHom = Subgroup.center ↥S :=
      Subgroup.characteristic_iff_map_eq.1 inferInstance ϕ
    constructor
    · intro hv
      rw [← hc] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      exact (ϕ.injective hwv) ▸ hw
    · intro hv
      rw [← hc]
      exact ⟨v, hv, rfl⟩
  set X : Subgroup G := (E'.map ϕ.toMonoidHom).map S.subtype with hX
  have hXS : X ≤ S := map_subtype_le _
  have hmemX : ∀ x : G, x ∈ X ↔ ∃ e : S, e ∈ E' ∧ ((ϕ e : S) : G) = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨_, ⟨e, he, rfl⟩, rfl⟩
  have hVE : d.V ≤ d.E := d.V_le_E
  have hVX : d.V ≤ X := by
    intro g hg
    have hgS : g ∈ S := hES (hVE hg)
    have hcen : (⟨g, hgS⟩ : S) ∈ Subgroup.center ↥S := (sec39d_mem_V_iff hV _).1 hg
    refine (hmemX g).2 ⟨ϕ.symm ⟨g, hgS⟩, ?_, by simp⟩
    have h1 : ϕ.symm ⟨g, hgS⟩ ∈ Subgroup.center ↥S := by
      rw [← hZ]; simpa using hcen
    exact hVE ((sec39d_mem_V_iff hV _).2 h1)
  have hXel : ElemAbMod d.V X := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := (hmemX x).1 hx
      have h1 := hEab.1 (e : G) he
      have h2 : e * e ∈ Subgroup.center ↥S :=
        (sec39d_mem_V_iff hV _).1 (by simpa using h1)
      have h3 := (sec39d_mem_V_iff hV (ϕ (e * e))).2 ((hZ _).2 h2)
      simpa using h3
    · intro x hx y hy
      obtain ⟨e, he, rfl⟩ := (hmemX x).1 hx
      obtain ⟨e', he', rfl⟩ := (hmemX y).1 hy
      have h1 := hEab.2 (e : G) he (e' : G) he'
      have h2 : ⁅e, e'⁆ ∈ Subgroup.center ↥S :=
        (sec39d_mem_V_iff hV _).1 h1
      have h3 := (sec39d_mem_V_iff hV (ϕ ⁅e, e'⁆)).2 ((hZ _).2 h2)
      have e1 : ((ϕ ⁅e, e'⁆ : S) : G) = ⁅((ϕ e : S) : G), ((ϕ e' : S) : G)⁆ := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
        simp [commutatorElement_def]
      rw [e1] at h3
      exact h3
  have hcard : Nat.card X = (2 ^ f) ^ 14 := by
    rw [hX, Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective ϕ.injective, hE',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hcardE]
  have hXE : X = d.E := key X hVX hXS hXel hcard.ge
  rintro _ ⟨e, he, rfl⟩
  have := (hmemX ((ϕ e : S) : G)).2 ⟨e, he, rfl⟩
  rw [hXE] at this
  exact this

theorem sec39d_CPI₆_sq (d : Data G h) {x : G} (hx : x ∈ d.CPI₆) : x * x = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hu2 : u * u = 1 :=
    (mul_self_eq_one_iff_mem_patSub_sI₆ (patSub_sI₆_le_sI₂ hu)).2 hu
  rw [← map_mul, hu2, map_one]

theorem sec39d_mem_CPI₆_of_sq (d : Data G h) {x : G} (hx : x ∈ d.CPI₂) (hx2 : x * x = 1) :
    x ∈ d.CPI₆ := by
  rw [← d.closure_involutions_CPI₂.1]
  exact Subgroup.subset_closure ⟨hx, hx2⟩

theorem sec39d_R_facts (hp : d.ProductCaseHyp) (S : Subgroup G) (hS2 : IsPGroup 2 S)
    (hP : d.P ≤ S) :
    (∀ x ∈ S ⊓ d.M₂, ∀ y ∈ S ⊓ d.M₂, x * x = 1 → y * y = 1 → x * y = y * x) ∧
    Nat.card {x : G // x ∈ S ⊓ d.M₂ ∧ x * x = 1} ≤ (2 ^ f) ^ 2 ∧
    (∀ z ∈ S ⊓ d.M₂, d.t * z * d.t⁻¹ = z → z ∈ d.CPI₂) := by
  have hd := hp.hyp
  obtain ⟨J, _, _, Φ, φ, hΦker, hφsurj, hφker, hΦφ, hΦt, -⟩ := sec39d_structure hp
  have hN₂CPI : d.CPI₂ ≤ d.N₂ := (d.isSylowOf_N₂_inf_P.2).le
  have hCP : d.CPI₂ ≤ d.P := d.pull_mono (patSub_le_U _ _)
  have hCM : d.CPI₂ ≤ d.M₂ := hN₂CPI.trans (sec39d_N₂_le_M₂ d)
  have hCR : d.CPI₂ ≤ S ⊓ d.M₂ := le_inf (hCP.trans hP) hCM
  obtain ⟨Q, hQ⟩ := (d.isSylowOf_N₂_inf_P.2).exists_sylow_eq_subgroupOf
  set P₀ : Subgroup ↥d.N₂ := d.CPI₂.subgroupOf d.N₂ with hP₀
  have hcomm0 : ∀ x ∈ P₀, ∀ y ∈ P₀, x * x = 1 → y * y = 1 → x * y = y * x := by
    intro x hx y hy hx2 hy2
    have hx6 := sec39d_mem_CPI₆_of_sq d (mem_subgroupOf.1 hx) (congrArg Subtype.val hx2)
    exact Subtype.ext (d.closure_involutions_CPI₂.2 _ hx6 _ (mem_subgroupOf.1 hy))
  have hcount0 : Nat.card {x : ↥d.N₂ // x ∈ P₀ ∧ x * x = 1} ≤ 2 ^ f := by
    let ι : {x : ↥d.N₂ // x ∈ P₀ ∧ x * x = 1} → ↥d.CPI₆ := fun x =>
      ⟨x.1.1, sec39d_mem_CPI₆_of_sq d (mem_subgroupOf.1 x.2.1) (congrArg Subtype.val x.2.2)⟩
    have hι : Function.Injective ι := fun a b hab => by
      have h1 : (ι a).1 = (ι b).1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact (Nat.card_le_card_of_injective ι hι).trans (d.card_CPI₆ ▸ le_rfl)
  have hJ := sec39d_J_facts φ hφsurj hφker P₀ ⟨Q, hQ⟩ (2 ^ f) hcomm0 hcount0
  have hti : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  have hMt : ∀ z ∈ d.M₂, d.t * z * d.t⁻¹ ∈ d.M₂ := fun z hz =>
    (mem_normalizer_iff.1 (sec39d_t_mem_normalizer_M₂ hd) z).1 hz
  have htt : ∀ z : G, d.t * (d.t * z * d.t⁻¹) * d.t⁻¹ = z := fun z => by
    calc d.t * (d.t * z * d.t⁻¹) * d.t⁻¹ = (d.t * d.t) * z * (d.t⁻¹ * d.t⁻¹) := by group
      _ = z := by rw [hd.t_mul_t, hti, hd.t_mul_t, one_mul, mul_one]
  let τ : ↥d.M₂ ≃* ↥d.M₂ :=
    { toFun := fun z => ⟨d.t * z * d.t⁻¹, hMt z.1 z.2⟩
      invFun := fun z => ⟨d.t * z * d.t⁻¹, hMt z.1 z.2⟩
      left_inv := fun z => Subtype.ext (htt z)
      right_inv := fun z => Subtype.ext (htt z)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hτ : ∀ m, Φ (τ m) = (Φ m).swap := fun m => hΦt m.1 m.2 (hMt m.1 m.2)
  have hR2 : IsPGroup 2 ↥(S ⊓ d.M₂) := hS2.to_le inf_le_left
  set R' : Subgroup ↥d.M₂ := (S ⊓ d.M₂).subgroupOf d.M₂ with hR'
  have hR'2 : IsPGroup 2 R' := hR2.comap_subtype
  obtain ⟨ha', hb', hc'⟩ := sec39d_Phi_facts (2 ^ f) (Nat.card P₀) hJ Φ hΦker τ hτ R' hR'2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hx2 hy2
    have := ha' ⟨x, (mem_inf.1 hx).2⟩ (mem_subgroupOf.2 hx) ⟨y, (mem_inf.1 hy).2⟩
      (mem_subgroupOf.2 hy) (Subtype.ext hx2) (Subtype.ext hy2)
    exact congrArg Subtype.val this
  · let ι : {x : G // x ∈ S ⊓ d.M₂ ∧ x * x = 1} → {x : ↥d.M₂ // x ∈ R' ∧ x * x = 1} := fun x =>
      ⟨⟨x.1, (mem_inf.1 x.2.1).2⟩, mem_subgroupOf.2 x.2.1, Subtype.ext x.2.2⟩
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (congrArg (fun w : {x : ↥d.M₂ // x ∈ R' ∧ x * x = 1} => (w.1 : G)) hab)
    exact (Nat.card_le_card_of_injective ι hι).trans hb'
  · have hcardP₀ : Nat.card P₀ = Nat.card d.CPI₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₂CPI).toEquiv
    let κ : ↥d.CPI₂ → {x : ↥d.M₂ // x ∈ R' ∧ τ x = x} := fun z =>
      ⟨⟨z.1, hCM z.2⟩, mem_subgroupOf.2 (hCR z.2), Subtype.ext (by
        have := mem_centralizer_singleton_iff.1 (hd.N₂_le_C (hN₂CPI z.2))
        show d.t * (z : G) * d.t⁻¹ = z
        rw [← this]; group)⟩
    have hκ : Function.Injective κ := fun a b hab =>
      Subtype.ext (congrArg (fun w : {x : ↥d.M₂ // x ∈ R' ∧ τ x = x} => (w.1 : G)) hab)
    have hbij := hκ.bijective_of_nat_card_le (hcardP₀ ▸ hc')
    intro z hz hzt
    obtain ⟨w, hw⟩ := hbij.2 ⟨⟨z, (mem_inf.1 hz).2⟩, mem_subgroupOf.2 hz, Subtype.ext hzt⟩
    have := congrArg (fun w : {x : ↥d.M₂ // x ∈ R' ∧ τ x = x} => (w.1 : G)) hw
    simp only [κ] at this
    rw [← this]
    exact w.2

theorem sec39d_of_hyp (hp : d.ProductCaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b)
    (hc : d.Sec39c S) : d.Sec39d S := by
  refine ⟨?_, sec39d_D_char hc⟩
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨hML₂, hVL, -, -, -⟩ := k8.s8
  have hSL₂ : S ≤ d.L₂ := hS.le
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) hd.four_le
  obtain ⟨-, -, hN3, -, -, -, hEab, hcardE⟩ := hd.sec3_6 hGMS
  have hES : d.E ≤ S := ha.S_eq ▸ le_sup_left
  have hVL' : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v := fun v hv x hx =>
    (mem_centralizer_iff.1 (mem_inf.1 (hVL hv)).2 x hx).symm
  have hVS : ∀ v ∈ d.V, ∀ s ∈ S, v * s = s * v := fun v hv s hs => hVL' v hv s (hSL₂ hs)
  have hEn : ∀ s ∈ S, ∀ e ∈ d.E, s * e * s⁻¹ ∈ d.E := fun s hs e he =>
    (mem_normalizer_iff.1 (d.L₂_le_normalizer_E (hSL₂ hs)) e).1 he
  have htB : d.t ∈ d.B₂ := mem_sup_left (mem_zpowers d.t)
  have htE : d.t ∈ normalizer (d.E : Set G) :=
    hN3 (le_normalizer ((le_sup_right : d.B₂ ≤ d.V ⊔ d.B₂) htB))
  have htS : d.t ∈ normalizer (S : Set G) := by
    rw [ha.S_eq]
    exact Common.mem_normalizer_sup htE hd.t_mem_normalizer_D
  have htE' : ∀ e ∈ d.E, d.t * e * d.t⁻¹ ∈ d.E := fun e he => (mem_normalizer_iff.1 htE e).1 he
  have htV : ∀ v ∈ d.V, d.t * v * d.t⁻¹ ∈ d.V := by
    intro v hv
    have hvS : v ∈ S := hES (d.V_le_E hv)
    have h1 : d.t * v * d.t⁻¹ ∈ S := (mem_normalizer_iff.1 htS v).1 hvS
    rw [← hc.1]
    refine mem_inf.2 ⟨h1, mem_centralizer_iff.2 fun s hs => ?_⟩
    have hs' : d.t⁻¹ * s * d.t ∈ S := by
      refine (mem_normalizer_iff.1 htS (d.t⁻¹ * s * d.t)).2 ?_
      rw [show d.t * (d.t⁻¹ * s * d.t) * d.t⁻¹ = s by group]
      exact hs
    have hc' := hVS v hv _ hs'
    calc s * (d.t * v * d.t⁻¹) = d.t * ((d.t⁻¹ * s * d.t) * v) * d.t⁻¹ := by group
      _ = d.t * (v * (d.t⁻¹ * s * d.t)) * d.t⁻¹ := by rw [← hc']
      _ = (d.t * v * d.t⁻¹) * s := by group
  have htM : d.t ∈ normalizer (d.M₂ : Set G) := sec39d_t_mem_normalizer_M₂ hd
  have hM₂L₂ : d.M₂ ≤ d.L₂ := hML₂ ▸ le_sup_right
  have hME : d.M₂ ≤ normalizer (d.E : Set G) := hM₂L₂.trans d.L₂_le_normalizer_E
  obtain ⟨_J, _, _, _Φ, _φ, -, -, -, -, -, hMEimp⟩ := sec39d_structure hp
  have hMEbot : d.M₂ ⊓ d.E = ⊥ := hMEimp hME (hS2.to_le hES)
  have hEMbot : d.E ⊓ d.M₂ = ⊥ := by rw [inf_comm]; exact hMEbot
  have hle : S ⊓ centralizer (d.I₂ : Set G) ≤ S ⊓ d.M₂ := le_inf inf_le_left ha.sylow₂.le
  have hRS : S ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G) :=
    ha.sylow₂.eq_of_le hle inf_le_right (hS2.to_le inf_le_left)
  have hRsylow : IsSylowOf 2 (S ⊓ d.M₂) d.M₂ := by rw [hRS]; exact ha.sylow₂
  have hRn : S ⊓ d.M₂ ≤ normalizer (d.E : Set G) :=
    inf_le_left.trans (hSL₂.trans d.L₂_le_normalizer_E)
  have hRt : ∀ y ∈ S ⊓ d.M₂, d.t * y * d.t⁻¹ ∈ S ⊓ d.M₂ := fun y hy =>
    mem_inf.2 ⟨(mem_normalizer_iff.1 htS y).1 (mem_inf.1 hy).1,
      (mem_normalizer_iff.1 htM y).1 (mem_inf.1 hy).2⟩
  have hcardL₂ : Nat.card d.L₂ = Nat.card d.E * Nat.card d.M₂ := by
    have h1 := Common.card_sup_mul_card_inf_eq hME
    rw [hEMbot, Subgroup.card_bot, mul_one, ← hML₂] at h1
    exact h1
  have hEpow : Nat.card d.E = 2 ^ (f * 14) := by rw [hcardE, ← pow_mul]
  have hv : (Nat.card d.L₂).factorization 2 = f * 14 + (Nat.card d.M₂).factorization 2 := by
    rw [hcardL₂, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hEpow,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hcardS : Nat.card S = Nat.card d.E * Nat.card (S ⊓ d.M₂ : Subgroup G) := by
    have h1 := hS.card_eq
    have h2 := hRsylow.card_eq
    rw [h2, hEpow, ← pow_add, ← hv]
    exact h1
  have hERbot : d.E ⊓ (S ⊓ d.M₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ d.E ⊓ d.M₂ := mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (mem_inf.1 hx).2).2⟩
    rwa [hEMbot] at this
  have hERsup : d.E ⊔ (S ⊓ d.M₂) = S := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hES inf_le_left) ?_)
    have h1 := Common.card_sup_mul_card_inf_eq hRn
    rw [hERbot, Subgroup.card_bot, mul_one] at h1
    rw [hcardS, ← h1]
  have hdec : ∀ s ∈ S, ∃ e ∈ d.E, ∃ y ∈ S ⊓ d.M₂, s = e * y := fun s hs =>
    exists_mul_of_mem_sup_of_le_normalizer (A := d.E) (B := S ⊓ d.M₂) hRn
      (by rw [hERsup]; exact hs)
  have hER : ∀ x ∈ d.E, x ∈ S ⊓ d.M₂ → x = 1 := fun x hx hxR => by
    have : x ∈ d.E ⊓ (S ⊓ d.M₂) := mem_inf.2 ⟨hx, hxR⟩
    rw [hERbot] at this
    exact (mem_bot).1 this
  obtain ⟨hcomm, hcard, hCfix⟩ := sec39d_R_facts hp S hS2 hP
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ S ⊓ d.M₂ ∧ y * y = 1}
      mul_mem' := fun {a b} ha' hb' => ⟨mul_mem ha'.1 hb'.1, by
        have hab : a * b = b * a := hcomm a ha'.1 b hb'.1 ha'.2 hb'.2
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha'.2, hb'.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {a} ha' => ⟨inv_mem ha'.1, by
        have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'.2
        rw [this]; exact ha'.2⟩ }
  have hΩ : ∀ y, y ∈ Ω ↔ y ∈ S ⊓ d.M₂ ∧ y * y = 1 := fun y => Iff.rfl
  have hΩcard : Nat.card Ω ≤ (2 ^ f) ^ 2 := hcard
  have hz₀ : ∃ z ∈ Ω, z ≠ 1 ∧ d.t * z * d.t⁻¹ = z := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x ∈ d.CPI₆, x = 1 := by
      intro x hx
      have hN₂CPI : d.CPI₂ ≤ d.N₂ := (d.isSylowOf_N₂_inf_P.2).le
      have hx2 : x ∈ d.CPI₂ := d.pull_mono patSub_sI₆_le_sI₂ hx
      have hxP : x ∈ d.P := (d.pull_mono (patSub_le_U _ _) : d.CPI₂ ≤ d.P) hx2
      have hxM : x ∈ d.M₂ := sec39d_N₂_le_M₂ d (hN₂CPI hx2)
      have hxC := mem_centralizer_singleton_iff.1 (hd.N₂_le_C (hN₂CPI hx2))
      refine by_contra fun hx1 => hcon x ⟨mem_inf.2 ⟨hP hxP, hxM⟩, sec39d_CPI₆_sq d hx⟩ hx1 ?_
      rw [← hxC]; group
    have hbot : d.CPI₆ = ⊥ := eq_bot_iff.2 fun x hx => (mem_bot).2 (hall x hx)
    have h1 := d.card_CPI₆
    rw [hbot, Subgroup.card_bot] at h1
    have : 1 < 2 ^ f := lt_of_lt_of_le (by norm_num) hd.four_le
    omega
  have hH4 : ∀ z ∈ Ω, z ≠ 1 → d.t * z * d.t⁻¹ = z →
      Nat.card (sec39dECent d.V d.E (fun v hv e he => hVS v hv e (hES he)) z) ≤ (2 ^ f) ^ 10 := by
    intro z hz hz1 hzt
    have hz6 := sec39d_mem_CPI₆_of_sq d (hCfix z hz.1 hzt) hz.2
    exact sec39d_card_ECent_le hGMS hd hVL' hz6 hz1
  have key := sec39d_key_abstract (2 ^ f) hq S d.E d.V (S ⊓ d.M₂) Ω d.t hd.t_mul_t hVS
    d.V_le_E hES hEn hEab.1 hEab.2 hcardE inf_le_left hdec hER htE' htV hRt hΩ hΩcard hz₀ hH4
  exact sec39d_E_char S hc.1 hES hcardE hEab
    (fun X hVX hXS hX hcardX => key X hVX hXS hX.1 hX.2 hcardX)

end Data

namespace CaseBParts

theorem sec39d : Sec39dStatement :=
  fun _ _ _ _ _ _ _ _ hp k8 S hS hP ha hb hc => Data.sec39d_of_hyp hp k8 S hS hP ha hb hc

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
