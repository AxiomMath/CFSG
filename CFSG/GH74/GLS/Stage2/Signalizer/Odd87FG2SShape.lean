module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SSL2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem exists_abelian_exponent_lift {G Y : Type*} [Group G] [Group Y] (φ : G →* Y) (κ : G)
    (hκc : ∀ g : G, κ * g = g * κ) (hκ2 : κ * κ = 1) (hφκ : φ κ = 1)
    (hker : ∀ g : G, φ g = 1 → g = 1 ∨ g = κ) {p : ℕ} (hp : Odd p) (A : Subgroup Y)
    (hAr : ∀ a ∈ A, a ∈ φ.range) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) :
    ∃ B : Subgroup G, (∀ b ∈ B, b ^ p = 1) ∧ (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) ∧
      (∀ b ∈ B, φ b ∈ A) ∧ ∀ a ∈ A, ∃ b ∈ B, φ b = a := by
  obtain ⟨r, rfl⟩ := hp
  have hκp : κ ^ (2 * r + 1) = κ := by
    rw [pow_succ, pow_mul, sq, hκ2, one_pow, one_mul]
  have hbc : ∀ b b' : G, φ b ∈ A → φ b' ∈ A → b ^ (2 * r + 1) = 1 → b' ^ (2 * r + 1) = 1 →
      b * b' = b' * b := by
    intro b b' hb hb' hbp hb'p
    have hc1 : φ (b * b' * b⁻¹ * b'⁻¹) = 1 := by
      have := hcomm _ hb _ hb'
      simp only [map_mul, map_inv]
      rw [this]
      group
    have hc : b * b' * b⁻¹ * b'⁻¹ = 1 := by
      rcases hker _ hc1 with h | h
      · exact h
      · have hbb : b * b' = κ * (b' * b) := by
          rw [← h]; group
        have hpow : ∀ n : ℕ, b ^ n * b' = κ ^ n * (b' * b ^ n) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            calc b ^ (n + 1) * b' = b ^ n * (b * b') := by rw [pow_succ, mul_assoc]
              _ = b ^ n * (κ * (b' * b)) := by rw [hbb]
              _ = κ * (b ^ n * (b' * b)) := by rw [← mul_assoc, (hκc (b ^ n)).symm, mul_assoc]
              _ = κ * ((b ^ n * b') * b) := by rw [mul_assoc]
              _ = κ * (κ ^ n * (b' * b ^ n) * b) := by rw [ih]
              _ = κ ^ (n + 1) * (b' * b ^ (n + 1)) := by rw [pow_succ', pow_succ]; group
        have h2 := hpow (2 * r + 1)
        rw [hbp, hκp, one_mul, mul_one] at h2
        have hκ1 : κ = 1 := by
          have : κ * b' = 1 * b' := by rw [one_mul]; exact h2.symm
          exact mul_right_cancel this
        rw [h, hκ1]
    calc b * b' = (b * b' * b⁻¹ * b'⁻¹) * (b' * b) := by group
      _ = b' * b := by rw [hc, one_mul]
  let B : Subgroup G :=
    { carrier := {b | φ b ∈ A ∧ b ^ (2 * r + 1) = 1}
      one_mem' := ⟨by rw [map_one]; exact A.one_mem, one_pow _⟩
      mul_mem' := by
        rintro b b' ⟨hb, hbp⟩ ⟨hb', hb'p⟩
        refine ⟨by rw [map_mul]; exact A.mul_mem hb hb', ?_⟩
        rw [(show Commute b b' from hbc b b' hb hb' hbp hb'p).mul_pow, hbp, hb'p, one_mul]
      inv_mem' := by
        rintro b ⟨hb, hbp⟩
        exact ⟨by rw [map_inv]; exact A.inv_mem hb, by rw [inv_pow, hbp, inv_one]⟩ }
  refine ⟨B, fun b hb => hb.2, fun b hb b' hb' => hbc b b' hb.1 hb'.1 hb.2 hb'.2,
    fun b hb => hb.1, ?_⟩
  intro a ha
  obtain ⟨g, rfl⟩ := hAr a ha
  have hg1 : φ (g ^ (2 * r + 1)) = 1 := by rw [map_pow]; exact hexp _ ha
  rcases hker _ hg1 with h | h
  · exact ⟨g, ⟨ha, h⟩, rfl⟩
  · refine ⟨g * κ, ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul, hφκ, mul_one]; exact ha
    · rw [(show Commute g κ from (hκc g).symm).mul_pow, h, hκp, hκ2]
    · rw [map_mul, hφκ, mul_one]

section ShapeFacts

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem shape_sq_mem_sup (y : Y) : y * y ∈ S.I₁ ⊔ S.I₂ := by
  have hM : (S.I₁ ⊔ S.I₂).Normal := by
    have := S.normal₁
    have := S.normal₂
    infer_instance
  have hy : y ∈ S.I₁ ⊔ S.I₂ ⊔ Subgroup.zpowers S.t := by rw [S.gen]; exact Subgroup.mem_top y
  obtain ⟨m, hm, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  rcases mem_zpowers_of_sq S.t_sq hk with rfl | rfl
  · rw [mul_one]; exact Subgroup.mul_mem _ hm hm
  · have : m * S.t * (m * S.t) = m * (S.t * m * S.t⁻¹) := by
      calc m * S.t * (m * S.t) = m * (S.t * m * S.t⁻¹) * (S.t * S.t) := by group
        _ = m * (S.t * m * S.t⁻¹) := by rw [S.t_sq, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ hm (hM.conj_mem m hm S.t)

theorem shape_mem_sup_of_pow_eq_one {p : ℕ} (hp : Odd p) {y : Y} (hy : y ^ p = 1) :
    y ∈ S.I₁ ⊔ S.I₂ := by
  obtain ⟨r, rfl⟩ := hp
  have h1 : (y * y) ^ r * y = 1 := by rw [← sq, ← pow_mul, ← pow_succ]; exact hy
  have h2 : y = ((y * y) ^ r)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (shape_sq_mem_sup S y) r)

theorem shape_mem_range_fnHom_of_pow_eq_one {p : ℕ} (hp : Odd p) {y : Y} (hy : y ^ p = 1) :
    y ∈ S.fnHom.range := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm (shape_mem_sup_of_pow_eq_one S hp hy)
  refine ⟨(S.e₁ ⟨a, ha⟩, S.e₂ ⟨b, hb⟩), ?_⟩
  rw [S.fnHom_apply]
  simp

theorem shape_fnHom_eq_one {x : SL(2, F₁) × SL(2, F₂)} (hx : S.fnHom x = 1) :
    x = 1 ∨ x = ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) := by
  obtain ⟨A, B⟩ := x
  rw [S.fnHom_apply] at hx
  have hab : ((S.e₁.symm A : ↥S.I₁) : Y) = (((S.e₂.symm B : ↥S.I₂) : Y))⁻¹ :=
    eq_inv_of_mul_eq_one_left hx
  have hmem : ((S.e₁.symm A : ↥S.I₁) : Y) ∈ Subgroup.zpowers S.z := by
    rw [← S.inter]
    refine ⟨(S.e₁.symm A).2, ?_⟩
    rw [hab]; exact S.I₂.inv_mem (S.e₂.symm B).2
  rcases mem_zpowers_of_sq S.z_sq hmem with h0 | h0
  · left
    have hA : A = 1 := by
      have h1 : S.e₁.symm A = 1 := Subtype.ext h0
      simpa using congrArg S.e₁ h1
    have hb0 : ((S.e₂.symm B : ↥S.I₂) : Y) = 1 := by
      rw [h0, one_mul] at hx; exact hx
    have hB : B = 1 := by
      have h1 : S.e₂.symm B = 1 := Subtype.ext hb0
      simpa using congrArg S.e₂ h1
    rw [hA, hB]; rfl
  · right
    have hA : A = -1 := by
      have h1 : S.e₁.symm A = ⟨S.z, S.z_mem₁⟩ := Subtype.ext h0
      have := congrArg S.e₁ h1
      rw [MulEquiv.apply_symm_apply, S.e₁_z] at this
      exact this
    have hb0 : ((S.e₂.symm B : ↥S.I₂) : Y) = S.z := by
      rw [h0] at hx
      exact (eq_inv_of_mul_eq_one_right hx).trans (inv_eq_of_mul_eq_one_right S.z_sq)
    have hB : B = -1 := by
      have h1 : S.e₂.symm B = ⟨S.z, S.z_mem₂⟩ := Subtype.ext hb0
      have := congrArg S.e₂ h1
      rw [MulEquiv.apply_symm_apply, S.e₂_z] at this
      exact this
    rw [hA, hB]

theorem shape_fnHom_neg_one : S.fnHom ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) = 1 := by
  rw [S.fnHom_apply, S.symm_neg_one₁, S.symm_neg_one₂]
  exact S.z_sq

end ShapeFacts

theorem shape_elemAb_card_le {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁))
    (h₂ : Odd (Nat.card F₂)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp₁ : ringChar F₁ ≠ p)
    (hp₂ : ringChar F₂ ≠ p) (A : Subgroup Y) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) : Nat.card ↥A ≤ p ^ 2 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hκc : ∀ g : SL(2, F₁) × SL(2, F₂),
      ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) * g = g * ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) := by
    intro g
    refine Prod.ext ?_ ?_
    · exact (Subgroup.mem_center_iff.mp neg_one_mem_center g.1).symm
    · exact (Subgroup.mem_center_iff.mp neg_one_mem_center g.2).symm
  have hκ2 : ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) * ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) = 1 := by
    refine Prod.ext ?_ ?_
    · simp
    · simp
  obtain ⟨B, hBp, hBc, hBA, hBsurj⟩ := exists_abelian_exponent_lift S.fnHom
    ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) hκc hκ2 (shape_fnHom_neg_one S)
    (fun g hg => shape_fnHom_eq_one S hg) hpodd A
    (fun a ha => shape_mem_range_fnHom_of_pow_eq_one S hpodd (hexp a ha)) hcomm hexp
  let P₁ : Subgroup SL(2, F₁) := B.map (MonoidHom.fst _ _)
  let P₂ : Subgroup SL(2, F₂) := B.map (MonoidHom.snd _ _)
  have hP₁ : Nat.card ↥P₁ ≤ p := by
    refine sl2_elemAb_card_le h₁ hp2 hp₁ P₁ ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      exact congrArg Prod.fst (hBc b hb b' hb')
    · rintro _ ⟨b, hb, rfl⟩
      exact congrArg Prod.fst (hBp b hb)
  have hP₂ : Nat.card ↥P₂ ≤ p := by
    refine sl2_elemAb_card_le h₂ hp2 hp₂ P₂ ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      exact congrArg Prod.snd (hBc b hb b' hb')
    · rintro _ ⟨b, hb, rfl⟩
      exact congrArg Prod.snd (hBp b hb)
  let f : ↥B → ↥A := fun b => ⟨S.fnHom b, hBA b b.2⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨b, hb, hba⟩ := hBsurj a a.2
    exact ⟨⟨b, hb⟩, Subtype.ext hba⟩
  let g : ↥B → ↥P₁ × ↥P₂ := fun b =>
    (⟨(b : SL(2, F₁) × SL(2, F₂)).1, b, b.2, rfl⟩, ⟨(b : SL(2, F₁) × SL(2, F₂)).2, b, b.2, rfl⟩)
  have hg : Function.Injective g := by
    intro b b' h
    have h1 := congrArg (fun x : ↥P₁ × ↥P₂ => ((x.1 : SL(2, F₁)), (x.2 : SL(2, F₂)))) h
    exact Subtype.ext h1
  calc Nat.card ↥A ≤ Nat.card ↥B := Nat.card_le_card_of_surjective f hf
    _ ≤ Nat.card (↥P₁ × ↥P₂) := Nat.card_le_card_of_injective g hg
    _ = Nat.card ↥P₁ * Nat.card ↥P₂ := Nat.card_prod _ _
    _ ≤ p * p := Nat.mul_le_mul hP₁ hP₂
    _ = p ^ 2 := (sq p).symm

theorem shape_natCard_eq_mul {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) :
    Nat.card Y = Nat.card SL(2, F₁) * Nat.card SL(2, F₂) := by
  have h₁ := S.sq_scalar₁
  have h₂ := S.sq_scalar₂
  have hsurj := S.psi_surjective S.g₁ S.g₂ h₁ h₂ rfl rfl
  have hker := S.ker_psi S.g₁ S.g₂ h₁ h₂ rfl rfl
  have hrange : (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl).range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have hk2 : Nat.card (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl).ker = 2 := by
    rw [hker, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · have hsq : ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) ^ 2 = 1 := by
        rw [pow_two]
        exact Prod.ext (by simp) (by simp)
      show (SemidirectProduct.inl ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) :
        Pgrp S.g₁ S.g₂ h₁ h₂) ^ 2 = 1
      rw [← map_pow, hsq, map_one]
    · intro h
      have h' : ((-1 : SL(2, F₁)), (-1 : SL(2, F₂))) = 1 :=
        SemidirectProduct.inl_injective (by rw [map_one]; exact h)
      have h1 : (-1 : SL(2, F₁)) = 1 := congrArg Prod.fst h'
      apply S.z_ne
      have h2 := S.symm_neg_one₁
      rw [h1, map_one] at h2
      exact (congrArg Subtype.val h2).symm
  have hcardP : Nat.card (Pgrp S.g₁ S.g₂ h₁ h₂) =
      Nat.card SL(2, F₁) * Nat.card SL(2, F₂) * 2 := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_prod]
    have : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨1, -1, by decide, Set.eq_univ_iff_forall.2 fun u => ?_⟩
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    rw [this]
  have h := Subgroup.card_ker_mul_card_range (S.psi S.g₁ S.g₂ h₁ h₂ rfl rfl)
  rw [hk2, hrange, Subgroup.card_top, hcardP] at h
  linarith

theorem shape_card {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] [Finite Y] (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁))
    (h₂ : Odd (Nat.card F₂)) :
    Nat.card Y = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) * (Nat.card F₂ * (Nat.card F₂ ^ 2 - 1)) := by
  have _ := h₁
  have _ := h₂
  rw [shape_natCard_eq_mul S, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
