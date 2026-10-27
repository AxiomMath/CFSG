module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.GroupTheory

private lemma conj_mem_of_map_conj_eq {X : Type*} [Group X] {b : X} {L K : Subgroup X}
    (h : L.map (MulAut.conj b).toMonoidHom = K) {y : X} (hy : y ∈ L) :
    b * y * b⁻¹ ∈ K := by
  rw [← h]
  simpa [MulAut.conj_apply] using
    Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hy

private lemma conj_sq_mem_of_map_conj_eq {X : Type*} [Group X] {b : X} {L K M : Subgroup X}
    (h₁ : L.map (MulAut.conj b).toMonoidHom = K)
    (h₂ : K.map (MulAut.conj b).toMonoidHom = M) {y : X} (hy : y ∈ L) :
    b ^ 2 * y * (b ^ 2)⁻¹ ∈ M := by
  have hk : b * y * b⁻¹ ∈ K := conj_mem_of_map_conj_eq h₁ hy
  have hm : b * (b * y * b⁻¹) * b⁻¹ ∈ M := conj_mem_of_map_conj_eq h₂ hk
  have e : b * (b * y * b⁻¹) * b⁻¹ = b ^ 2 * y * (b ^ 2)⁻¹ := by
    rw [pow_two]
    group
  rwa [e] at hm

private lemma diag_mul {X : Type*} [Group X] {b y z : X}
    (h1 : Commute z (b * y * b⁻¹))
    (h2 : Commute z (b ^ 2 * y * (b ^ 2)⁻¹))
    (h3 : Commute (b * z * b⁻¹) (b ^ 2 * y * (b ^ 2)⁻¹)) :
    (y * z) * (b * (y * z) * b⁻¹) * (b ^ 2 * (y * z) * (b ^ 2)⁻¹) =
      (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) *
        (z * (b * z * b⁻¹) * (b ^ 2 * z * (b ^ 2)⁻¹)) := by
  have e1 : b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹) := by group
  have e2 : b ^ 2 * (y * z) * (b ^ 2)⁻¹ =
      (b ^ 2 * y * (b ^ 2)⁻¹) * (b ^ 2 * z * (b ^ 2)⁻¹) := by group
  rw [e1, e2]
  generalize b * y * b⁻¹ = a₁ at h1 h2 h3 ⊢
  generalize b ^ 2 * y * (b ^ 2)⁻¹ = a₂ at h1 h2 h3 ⊢
  generalize b * z * b⁻¹ = c₁ at h1 h2 h3 ⊢
  generalize b ^ 2 * z * (b ^ 2)⁻¹ = c₂ at h1 h2 h3 ⊢
  calc y * z * (a₁ * c₁) * (a₂ * c₂)
      = y * (z * a₁) * c₁ * a₂ * c₂ := by group
    _ = y * (a₁ * z) * c₁ * a₂ * c₂ := by rw [h1.eq]
    _ = y * a₁ * z * (c₁ * a₂) * c₂ := by group
    _ = y * a₁ * z * (a₂ * c₁) * c₂ := by rw [h3.eq]
    _ = y * a₁ * (z * a₂) * c₁ * c₂ := by group
    _ = y * a₁ * (a₂ * z) * c₁ * c₂ := by rw [h2.eq]
    _ = y * a₁ * a₂ * (z * c₁ * c₂) := by group

private lemma diag_mem_centralizer {X : Type*} [Group X] {b y : X} (hb : b ^ 3 = 1)
    (h01 : Commute y (b * y * b⁻¹)) (h02 : Commute y (b ^ 2 * y * (b ^ 2)⁻¹)) :
    y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹) ∈
      Subgroup.centralizer ({b} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e2 : b * (b * y * b⁻¹) * b⁻¹ = b ^ 2 * y * (b ^ 2)⁻¹ := by
    rw [pow_two]
    group
  have e3 : b * (b ^ 2 * y * (b ^ 2)⁻¹) * b⁻¹ = y := by
    calc b * (b ^ 2 * y * (b ^ 2)⁻¹) * b⁻¹ = b ^ 3 * y * (b ^ 3)⁻¹ := by group
      _ = y := by rw [hb]; group
  have e : b * (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) * b⁻¹ =
      y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹) := by
    calc b * (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) * b⁻¹ =
        (b * y * b⁻¹) * (b * (b * y * b⁻¹) * b⁻¹) *
          (b * (b ^ 2 * y * (b ^ 2)⁻¹) * b⁻¹) := by group
      _ = (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹) * y := by rw [e2, e3]
      _ = y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹) := by
        rw [((h01.mul_right h02).symm).eq, ← mul_assoc]
  calc (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) * b =
      b * (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) * b⁻¹ * b := by rw [e]
    _ = b * (y * (b * y * b⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) := by group

private lemma exists_mul_mul_of_mem_sup {X : Type*} [Group X] {A B C : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) {x : X} (hx : x ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, x = a * b * c := by
  have hAB_C : ∀ y ∈ A ⊔ B, ∀ c ∈ C, y * c = c * y := by
    intro y hy c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hy
    calc a * b * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [hBC b hb c hc]
      _ = a * c * b := by group
      _ = c * a * b := by rw [hAC a ha c hc]
      _ = c * (a * b) := by group
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB_C hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hy
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

private lemma fst_eq_of_mul_mul_eq_mul_mul {X : Type*} [Group X] {A B C : Subgroup X}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) (hA : A ⊓ (B ⊔ C) = ⊥)
    {a₁ a₂ a₃ b₁ b₂ b₃ : X}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ B) (ha₃ : a₃ ∈ C)
    (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ B) (hb₃ : b₃ ∈ C)
    (h : a₁ * a₂ * a₃ = b₁ * b₂ * b₃) : a₁ = b₁ := by
  have hprod : b₁⁻¹ * a₁ = (b₂ * a₂⁻¹) * (b₃ * a₃⁻¹) := by
    have hb₃a₂ : Commute b₃ a₂ := (hBC a₂ ha₂ b₃ hb₃).symm
    have ha₃a₂ : Commute a₃ a₂ := (hBC a₂ ha₂ a₃ ha₃).symm
    have h1 : Commute b₃ a₂⁻¹ := hb₃a₂.inv_right
    have h2 : Commute a₃⁻¹ a₂⁻¹ := ha₃a₂.inv_inv
    have hc : Commute (b₃ * a₃⁻¹) (a₂⁻¹) := h1.mul_left h2
    calc b₁⁻¹ * a₁
        = b₁⁻¹ * (a₁ * a₂ * a₃) * (a₂ * a₃)⁻¹ := by group
      _ = b₁⁻¹ * (b₁ * b₂ * b₃) * (a₂ * a₃)⁻¹ := by rw [h]
      _ = (b₂ * a₂⁻¹) * (b₃ * a₃⁻¹) := by
        calc b₁⁻¹ * (b₁ * b₂ * b₃) * (a₂ * a₃)⁻¹
            = b₂ * b₃ * a₃⁻¹ * a₂⁻¹ := by group
          _ = b₂ * ((b₃ * a₃⁻¹) * a₂⁻¹) := by group
          _ = b₂ * (a₂⁻¹ * (b₃ * a₃⁻¹)) := by rw [hc.eq]
          _ = (b₂ * a₂⁻¹) * (b₃ * a₃⁻¹) := by group
  have hmemA : b₁⁻¹ * a₁ ∈ A := A.mul_mem (A.inv_mem hb₁) ha₁
  have hmemBC : b₁⁻¹ * a₁ ∈ B ⊔ C := by
    rw [hprod]
    exact Subgroup.mul_mem_sup (B.mul_mem hb₂ (B.inv_mem ha₂))
      (C.mul_mem hb₃ (C.inv_mem ha₃))
  have hone : b₁⁻¹ * a₁ = 1 := by
    have hbot : b₁⁻¹ * a₁ ∈ A ⊓ (B ⊔ C) := ⟨hmemA, hmemBC⟩
    rw [hA] at hbot
    simpa using hbot
  calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
    _ = b₁ * 1 := by rw [hone]
    _ = b₁ := by group

private lemma eq_of_mul_eq_mul {X : Type*} [Group X] {B C : Subgroup X}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) (hBCbot : B ⊓ C = ⊥)
    {a₂ a₃ b₂ b₃ : X} (ha₂ : a₂ ∈ B) (ha₃ : a₃ ∈ C)
    (hb₂ : b₂ ∈ B) (hb₃ : b₃ ∈ C) (h : a₂ * a₃ = b₂ * b₃) :
    a₂ = b₂ ∧ a₃ = b₃ := by
  have hprod : b₂⁻¹ * a₂ = b₃ * a₃⁻¹ := by
    calc b₂⁻¹ * a₂ = b₂⁻¹ * (a₂ * a₃) * a₃⁻¹ := by group
      _ = b₂⁻¹ * (b₂ * b₃) * a₃⁻¹ := by rw [h]
      _ = b₃ * a₃⁻¹ := by group
  have hmemB : b₂⁻¹ * a₂ ∈ B := B.mul_mem (B.inv_mem hb₂) ha₂
  have hmemC : b₂⁻¹ * a₂ ∈ C := by
    rw [hprod]
    exact C.mul_mem hb₃ (C.inv_mem ha₃)
  have hone : b₂⁻¹ * a₂ = 1 := by
    have hbot : b₂⁻¹ * a₂ ∈ B ⊓ C := ⟨hmemB, hmemC⟩
    rw [hBCbot] at hbot
    simpa using hbot
  have h₂ : a₂ = b₂ := by
    calc a₂ = b₂ * (b₂⁻¹ * a₂) := by group
      _ = b₂ * 1 := by rw [hone]
      _ = b₂ := by group
  have h₃ : a₃ = b₃ := by
    have h' : b₂ * a₃ = b₂ * b₃ := by
      calc b₂ * a₃ = a₂ * a₃ := by rw [h₂]
        _ = b₂ * b₃ := h
    exact mul_left_cancel h'
  exact ⟨h₂, h₃⟩

private lemma eq_of_mul_mul_eq_mul_mul {X : Type*} [Group X] {A B C : Subgroup X}
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hA : A ⊓ (B ⊔ C) = ⊥) (hBCbot : B ⊓ C = ⊥)
    {a₁ a₂ a₃ b₁ b₂ b₃ : X}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ B) (ha₃ : a₃ ∈ C)
    (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ B) (hb₃ : b₃ ∈ C)
    (h : a₁ * a₂ * a₃ = b₁ * b₂ * b₃) :
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  have h₁ : a₁ = b₁ :=
    fst_eq_of_mul_mul_eq_mul_mul hBC hA ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ h
  have h₂₃ : a₂ * a₃ = b₂ * b₃ := by
    have h' : b₁ * (a₂ * a₃) = b₁ * (b₂ * b₃) := by
      calc b₁ * (a₂ * a₃) = a₁ * a₂ * a₃ := by rw [h₁]; group
        _ = b₁ * b₂ * b₃ := h
        _ = b₁ * (b₂ * b₃) := by group
    exact mul_left_cancel h'
  obtain ⟨h₂, h₃⟩ := eq_of_mul_eq_mul hBC hBCbot ha₂ ha₃ hb₂ hb₃ h₂₃
  exact ⟨h₁, h₂, h₃⟩

private def diagHom {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X} {b : X}
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a)
    (hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (hcomm23 : ∀ a ∈ L₂, ∀ c ∈ L₃, a * c = c * a) :
    ↥L₁ →* X where
  toFun y := (y : X) * (b * (y : X) * b⁻¹) * (b ^ 2 * (y : X) * (b ^ 2)⁻¹)
  map_one' := by simp
  map_mul' y z := by
    have hy₂ : b * (y : X) * b⁻¹ ∈ L₂ := conj_mem_of_map_conj_eq hb₁ y.2
    have hz₂ : b * (z : X) * b⁻¹ ∈ L₂ := conj_mem_of_map_conj_eq hb₁ z.2
    have hy₃ : b ^ 2 * (y : X) * (b ^ 2)⁻¹ ∈ L₃ :=
      conj_sq_mem_of_map_conj_eq hb₁ hb₂ y.2
    have hz₃ : b ^ 2 * (z : X) * (b ^ 2)⁻¹ ∈ L₃ :=
      conj_sq_mem_of_map_conj_eq hb₁ hb₂ z.2
    exact diag_mul (hcomm12 (z : X) z.2 _ hy₂) (hcomm13 (z : X) z.2 _ hy₃)
      (hcomm23 _ hz₂ _ hy₃)

private lemma diagHom_mem {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X} {b : X}
    (hb : b ^ 3 = 1)
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a)
    (hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (hcomm23 : ∀ a ∈ L₂, ∀ c ∈ L₃, a * c = c * a) (y : ↥L₁) :
    diagHom hb₁ hb₂ hcomm12 hcomm13 hcomm23 y ∈
      Subgroup.centralizer ({b} : Set X) ⊓ (L₁ ⊔ L₂ ⊔ L₃) := by
  have hy₂ : b * (y : X) * b⁻¹ ∈ L₂ := conj_mem_of_map_conj_eq hb₁ y.2
  have hy₃ : b ^ 2 * (y : X) * (b ^ 2)⁻¹ ∈ L₃ :=
    conj_sq_mem_of_map_conj_eq hb₁ hb₂ y.2
  refine ⟨?_, ?_⟩
  · change (y : X) * (b * (y : X) * b⁻¹) * (b ^ 2 * (y : X) * (b ^ 2)⁻¹) ∈
      Subgroup.centralizer ({b} : Set X)
    exact diag_mem_centralizer hb (hcomm12 (y : X) y.2 _ hy₂) (hcomm13 (y : X) y.2 _ hy₃)
  · change (y : X) * (b * (y : X) * b⁻¹) * (b ^ 2 * (y : X) * (b ^ 2)⁻¹) ∈
      (L₁ ⊔ L₂ ⊔ L₃ : Subgroup X)
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup y.2 hy₂) hy₃

private lemma diagHom_injective {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X} {b : X}
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a)
    (hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (hcomm23 : ∀ a ∈ L₂, ∀ c ∈ L₃, a * c = c * a)
    (hA : L₁ ⊓ (L₂ ⊔ L₃) = ⊥) (hBCbot : L₂ ⊓ L₃ = ⊥) :
    Function.Injective (diagHom hb₁ hb₂ hcomm12 hcomm13 hcomm23) := by
  intro y z h
  have h' : (y : X) * (b * (y : X) * b⁻¹) * (b ^ 2 * (y : X) * (b ^ 2)⁻¹) =
      (z : X) * (b * (z : X) * b⁻¹) * (b ^ 2 * (z : X) * (b ^ 2)⁻¹) := h
  exact Subtype.ext (eq_of_mul_mul_eq_mul_mul hcomm23 hA hBCbot y.2
    (conj_mem_of_map_conj_eq hb₁ y.2) (conj_sq_mem_of_map_conj_eq hb₁ hb₂ y.2) z.2
    (conj_mem_of_map_conj_eq hb₁ z.2) (conj_sq_mem_of_map_conj_eq hb₁ hb₂ z.2) h').1

private lemma cyclic_conj_mul {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X} {b y₁ y₂ y₃ : X}
    (hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a)
    (hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (hz1 : b * y₃ * b⁻¹ ∈ L₁) (hz2 : b * y₁ * b⁻¹ ∈ L₂)
    (hz3 : b * y₂ * b⁻¹ ∈ L₃) :
    (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) * (b * y₃ * b⁻¹) =
      (b * y₃ * b⁻¹) * (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) := by
  have h31 : Commute (b * y₃ * b⁻¹) (b * y₁ * b⁻¹) := hcomm12 _ hz1 _ hz2
  have h32 : Commute (b * y₃ * b⁻¹) (b * y₂ * b⁻¹) := hcomm13 _ hz1 _ hz3
  calc (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) * (b * y₃ * b⁻¹)
      = (b * y₁ * b⁻¹) * ((b * y₂ * b⁻¹) * (b * y₃ * b⁻¹)) := by group
    _ = (b * y₁ * b⁻¹) * ((b * y₃ * b⁻¹) * (b * y₂ * b⁻¹)) := by rw [h32.symm.eq]
    _ = ((b * y₁ * b⁻¹) * (b * y₃ * b⁻¹)) * (b * y₂ * b⁻¹) := by group
    _ = ((b * y₃ * b⁻¹) * (b * y₁ * b⁻¹)) * (b * y₂ * b⁻¹) := by rw [h31.symm.eq]
    _ = (b * y₃ * b⁻¹) * (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) := by group

private lemma exists_diagHom_eq {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X} {b : X}
    (hb : b ^ 3 = 1)
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hb₃ : L₃.map (MulAut.conj b).toMonoidHom = L₁)
    (hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a)
    (hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (hcomm23 : ∀ a ∈ L₂, ∀ c ∈ L₃, a * c = c * a)
    (hA : L₁ ⊓ (L₂ ⊔ L₃) = ⊥) (hBCbot : L₂ ⊓ L₃ = ⊥) {z : X}
    (hz : z ∈ Subgroup.centralizer ({b} : Set X) ⊓ (L₁ ⊔ L₂ ⊔ L₃)) :
    ∃ y : ↥L₁, diagHom hb₁ hb₂ hcomm12 hcomm13 hcomm23 y = z := by
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hzy⟩ :=
    exists_mul_mul_of_mem_sup hcomm12 hcomm13 hcomm23 hz.2
  have hcommbz : b * z * b⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hz.1
    calc b * z * b⁻¹ = z * b * b⁻¹ := by rw [← h]
      _ = z := by group
  have hz1 : b * y₃ * b⁻¹ ∈ L₁ := conj_mem_of_map_conj_eq hb₃ hy₃
  have hz2 : b * y₁ * b⁻¹ ∈ L₂ := conj_mem_of_map_conj_eq hb₁ hy₁
  have hz3 : b * y₂ * b⁻¹ ∈ L₃ := conj_mem_of_map_conj_eq hb₂ hy₂
  have hcyc := cyclic_conj_mul hcomm12 hcomm13 hz1 hz2 hz3
  have hinput : y₁ * y₂ * y₃ = (b * y₃ * b⁻¹) * (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) := by
    rw [← hzy]
    calc z = b * z * b⁻¹ := hcommbz.symm
      _ = (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) * (b * y₃ * b⁻¹) := by rw [hzy]; group
      _ = (b * y₃ * b⁻¹) * (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) := hcyc
  have huniq := eq_of_mul_mul_eq_mul_mul hcomm23 hA hBCbot hy₁ hy₂ hy₃ hz1 hz2 hz3 hinput
  have hy₃' : y₃ = b ^ 2 * y₁ * (b ^ 2)⁻¹ := by
    rw [huniq.2.2, huniq.2.1, pow_two]
    group
  refine ⟨⟨y₁, hy₁⟩, ?_⟩
  change y₁ * (b * y₁ * b⁻¹) * (b ^ 2 * y₁ * (b ^ 2)⁻¹) = z
  calc y₁ * (b * y₁ * b⁻¹) * (b ^ 2 * y₁ * (b ^ 2)⁻¹)
      = y₁ * y₂ * y₃ := by rw [huniq.2.1, hy₃']
    _ = z := hzy.symm

theorem nonempty_centralizer_inf_sup_mulEquiv {X : Type*} [Group X] {L₁ L₂ L₃ : Subgroup X}
    {b : X} (hb : b ^ 3 = 1)
    (h12 : L₁ ≤ Subgroup.centralizer (L₂ : Set X)) (h13 : L₁ ≤ Subgroup.centralizer (L₃ : Set X))
    (h23 : L₂ ≤ Subgroup.centralizer (L₃ : Set X))
    (hind₁ : L₁ ⊓ (L₂ ⊔ L₃) = ⊥) (hind₂ : L₂ ⊓ (L₁ ⊔ L₃) = ⊥) (hind₃ : L₃ ⊓ (L₁ ⊔ L₂) = ⊥)
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hb₃ : L₃.map (MulAut.conj b).toMonoidHom = L₁) :
    Nonempty (↥(Subgroup.centralizer ({b} : Set X) ⊓ (L₁ ⊔ L₂ ⊔ L₃)) ≃* ↥L₁) := by
  have hcomm12 : ∀ a ∈ L₁, ∀ c ∈ L₂, a * c = c * a := fun a ha c hc =>
    ((Subgroup.mem_centralizer_iff.mp (h12 ha)) c hc).symm
  have hcomm13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a := fun a ha c hc =>
    ((Subgroup.mem_centralizer_iff.mp (h13 ha)) c hc).symm
  have hcomm23 : ∀ a ∈ L₂, ∀ c ∈ L₃, a * c = c * a := fun a ha c hc =>
    ((Subgroup.mem_centralizer_iff.mp (h23 ha)) c hc).symm
  have hBCbot : L₂ ⊓ L₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ L₂ ⊓ (L₁ ⊔ L₃) := ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
    rw [hind₂] at hx'
    simpa using hx'
  let Φ : ↥L₁ →* ↥(Subgroup.centralizer ({b} : Set X) ⊓ (L₁ ⊔ L₂ ⊔ L₃)) :=
    (diagHom hb₁ hb₂ hcomm12 hcomm13 hcomm23).codRestrict _
      (fun y => diagHom_mem hb hb₁ hb₂ hcomm12 hcomm13 hcomm23 y)
  have hinj : Function.Injective Φ := by
    intro y z h
    exact diagHom_injective hb₁ hb₂ hcomm12 hcomm13 hcomm23 hind₁ hBCbot
      (congrArg Subtype.val h)
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨y, hy⟩ := exists_diagHom_eq hb hb₁ hb₂ hb₃ hcomm12 hcomm13 hcomm23 hind₁ hBCbot z.2
    exact ⟨y, Subtype.ext hy⟩
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

end CFSG.GroupTheory
