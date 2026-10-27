module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lat1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem closure_comm_sq {s : Set P} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hs : ∀ a ∈ s, a * a = 1) :
    (∀ a ∈ closure s, ∀ b ∈ closure s, a * b = b * a) ∧ (∀ a ∈ closure s, a * a = 1) := by
  have hcomm : ∀ a ∈ closure s, ∀ b ∈ closure s, a * b = b * a := by
    intro a ha b hb
    have hle : closure s ≤ centralizer s := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc y hy x hx)
    have h1 : a ∈ centralizer s := hle ha
    have h2 : a ∈ centralizer (closure s : Set P) := by rwa [Subgroup.centralizer_closure]
    exact ((Subgroup.mem_centralizer_iff.1 h2) b hb).symm
  refine ⟨hcomm, ?_⟩
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y hx hy hx1 hy1 =>
    have hxy := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hx1, hy1, one_mul]
  | inv x hx hx1 =>
    have : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [this, hx1, inv_one]

theorem three_dvd_of_free {α : Type*} [Finite α] (f : Function.End α)
    (hf : ∀ x, f (f (f x)) = x) (hfree : ∀ x, f x ≠ x) : 3 ∣ Nat.card α := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := f) (p := 3) (n := 1) hf3
  have key : Fintype.card α ≡ 0 [MOD 3] := by
    convert hmod using 1
    exact (Fintype.card_eq_zero_iff.2 ⟨fun ⟨x, hx⟩ => hfree x hx⟩).symm
  rw [← Nat.card_eq_fintype_card] at key
  exact (Nat.modEq_zero_iff_dvd).1 key

theorem two_dvd_of_free {α : Type*} [Finite α] (f : Function.End α)
    (hf : ∀ x, f (f x) = x) (hfree : ∀ x, f x ≠ x) : 2 ∣ Nat.card α := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := f) (p := 2) (n := 1) hf2
  have key : Fintype.card α ≡ 0 [MOD 2] := by
    convert hmod using 1
    exact (Fintype.card_eq_zero_iff.2 ⟨fun ⟨x, hx⟩ => hfree x hx⟩).symm
  rw [← Nat.card_eq_fintype_card] at key
  exact (Nat.modEq_zero_iff_dvd).1 key

theorem perm3_normal_card_ne_two (M : Subgroup (Equiv.Perm (Fin 3))) [hM : M.Normal] :
    Nat.card ↥M ≠ 2 := by
  intro h2
  have hnt : ∃ τ ∈ M, τ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hcon x hx)
    rw [this] at h2
    simp at h2
  obtain ⟨τ, hτM, hτ1⟩ := hnt
  have hord : orderOf τ = 2 := by
    have hd : orderOf τ ∣ 2 := by
      have := orderOf_dvd_natCard (⟨τ, hτM⟩ : ↥M)
      rw [Subgroup.orderOf_mk, h2] at this
      exact this
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hτ1
    · exact h
  have hM2 : zpowers τ = M := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hτM)
    rw [Nat.card_zpowers, hord, h2]
  have hτsq : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hord, pow_two] at this
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → ∃ σ : Equiv.Perm (Fin 3), σ * τ * σ⁻¹ ≠ τ := by
    decide +kernel
  obtain ⟨σ, hσ⟩ := key τ hτ1
  apply hσ
  have hmem : σ * τ * σ⁻¹ ∈ M := hM.conj_mem _ hτM σ
  rw [← hM2] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk2 : τ ^ k = τ ^ (k % 2) := by
    have h := zpow_mod_orderOf τ k
    rw [hord] at h
    simpa using h.symm
  have hne : σ * τ * σ⁻¹ ≠ 1 := by
    intro h1
    apply hτ1
    have : τ = σ⁻¹ * (σ * τ * σ⁻¹) * σ := by group
    rw [this, h1]; simp
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · exfalso; apply hne; rw [← hk, hk2, h0]; simp
  · rw [← hk, hk2, h0]; simp

namespace BarShape.Spec

variable {zc : P} {W A B A₃ : Subgroup P} (hS : BarShape.Spec zc W A B A₃)
include hS

theorem exists_elems (hP : BarShape P zc) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, a₁ * a₁ = zc ∧ a₂ * a₂ = zc ∧ b₁ * b₁ = zc ∧
      b₂ * b₂ = zc ∧ a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = zc ∧ b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = zc ∧
      a₂ ≠ a₁ ∧ a₂ ≠ a₁ * zc := by
  obtain ⟨eA⟩ := hS.eA
  obtain ⟨eB⟩ := hS.eB
  have hzA := hS.zc_mem_A hP
  have hzB := hS.zc_mem_B hP
  have hzq : ∀ (C : Subgroup P) (e : ↥C ≃* QuaternionGroup 2) (hzC : zc ∈ C),
      e ⟨zc, hzC⟩ = QuaternionGroup.a 2 := by
    intro C e hzC
    apply q8_involution
    · intro h
      have := e.injective (h.trans (map_one e).symm)
      exact hP.ne_one (congrArg Subtype.val this)
    · rw [← map_mul]
      have : (⟨zc, hzC⟩ : ↥C) * ⟨zc, hzC⟩ = 1 := Subtype.ext hP.sq
      rw [this, map_one]
  let q₁ : QuaternionGroup 2 := QuaternionGroup.a 1
  let q₂ : QuaternionGroup 2 := QuaternionGroup.xa 0
  have hq1 : q₁ * q₁ = QuaternionGroup.a 2 := by decide
  have hq2 : q₂ * q₂ = QuaternionGroup.a 2 := by decide
  have hq12 : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ = QuaternionGroup.a 2 := by decide
  have hq3 : q₂ ≠ q₁ := by decide
  have hq4 : q₂ ≠ q₁ * QuaternionGroup.a 2 := by decide
  refine ⟨(eA.symm q₁ : P), (eA.symm q₁).2, (eA.symm q₂ : P), (eA.symm q₂).2,
    (eB.symm q₁ : P), (eB.symm q₁).2, (eB.symm q₂ : P), (eB.symm q₂).2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have h : eA (eA.symm q₁ * eA.symm q₁) = eA ⟨zc, hzA⟩ := by
      rw [map_mul, MulEquiv.apply_symm_apply, hq1, hzq A eA hzA]
    exact congrArg Subtype.val (eA.injective h)
  · have h : eA (eA.symm q₂ * eA.symm q₂) = eA ⟨zc, hzA⟩ := by
      rw [map_mul, MulEquiv.apply_symm_apply, hq2, hzq A eA hzA]
    exact congrArg Subtype.val (eA.injective h)
  · have h : eB (eB.symm q₁ * eB.symm q₁) = eB ⟨zc, hzB⟩ := by
      rw [map_mul, MulEquiv.apply_symm_apply, hq1, hzq B eB hzB]
    exact congrArg Subtype.val (eB.injective h)
  · have h : eB (eB.symm q₂ * eB.symm q₂) = eB ⟨zc, hzB⟩ := by
      rw [map_mul, MulEquiv.apply_symm_apply, hq2, hzq B eB hzB]
    exact congrArg Subtype.val (eB.injective h)
  · have h : eA (eA.symm q₁ * eA.symm q₂ * (eA.symm q₁)⁻¹ * (eA.symm q₂)⁻¹) = eA ⟨zc, hzA⟩ := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [hzq A eA hzA]; exact hq12
    exact congrArg Subtype.val (eA.injective h)
  · have h : eB (eB.symm q₁ * eB.symm q₂ * (eB.symm q₁)⁻¹ * (eB.symm q₂)⁻¹) = eB ⟨zc, hzB⟩ := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [hzq B eB hzB]; exact hq12
    exact congrArg Subtype.val (eB.injective h)
  · intro h
    have h' : eA.symm q₂ = eA.symm q₁ := Subtype.ext h
    exact hq3 (eA.symm.injective h')
  · intro h
    have h' : eA.symm q₂ = eA.symm q₁ * ⟨zc, hzA⟩ := Subtype.ext h
    apply hq4
    have h2 := congrArg eA h'
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hzq A eA hzA] at h2
    exact h2

theorem not_mem_B_of_sq (hP : BarShape P zc) {a : P} (ha : a ∈ A) (hsq : a * a = zc) : a ∉ B := by
  intro hB
  have : a ∈ zpowers zc := by
    rw [hS.zpowers_eq hP]; exact ⟨ha, hB⟩
  rcases (hS.mem_zpowers_zc_iff hP.ne_one hP.sq).1 this with h | h
  · rw [h, one_mul] at hsq; exact hP.ne_one hsq.symm
  · rw [h, hP.sq] at hsq; exact hP.ne_one hsq.symm

theorem exists_pair (hP : BarShape P zc) :
    ∃ e₁ e₂ : P, e₁ ∈ W ∧ e₂ ∈ W ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧
      e₁ ≠ 1 ∧ e₁ ≠ zc ∧ e₂ ≠ 1 ∧ e₂ ≠ zc ∧ e₂ ≠ e₁ ∧ e₂ ≠ e₁ * zc := by
  obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, h1, h2, h3, h4, hab, hbb, hne1, hne2⟩ :=
    hS.exists_elems hP
  have hAW := hS.A_le_W
  have hBW := hS.B_le_W
  have hzc := hP.central
  have hz2 := hP.sq
  have hAB := hS.comm_AB
  have hzB := hS.zc_mem_B hP
  have hzA := hS.zc_mem_A hP
  have hA21 : a₂ * a₁ = zc * (a₁ * a₂) := by
    have : a₁ * a₂ = zc * (a₂ * a₁) := by
      have := hab
      calc a₁ * a₂ = (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (a₂ * a₁) := by group
        _ = zc * (a₂ * a₁) := by rw [hab]
    calc a₂ * a₁ = (zc * zc) * (a₂ * a₁) := by rw [hz2, one_mul]
      _ = zc * (zc * (a₂ * a₁)) := by rw [mul_assoc]
      _ = zc * (a₁ * a₂) := by rw [← this]
  have hB21 : b₂ * b₁ = zc * (b₁ * b₂) := by
    have : b₁ * b₂ = zc * (b₂ * b₁) := by
      calc b₁ * b₂ = (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * (b₂ * b₁) := by group
        _ = zc * (b₂ * b₁) := by rw [hbb]
    calc b₂ * b₁ = (zc * zc) * (b₂ * b₁) := by rw [hz2, one_mul]
      _ = zc * (zc * (b₂ * b₁)) := by rw [mul_assoc]
      _ = zc * (b₁ * b₂) := by rw [← this]
  have hsq1 : a₁ * b₁ * (a₁ * b₁) = 1 := by
    calc a₁ * b₁ * (a₁ * b₁) = a₁ * (b₁ * a₁) * b₁ := by simp only [mul_assoc]
      _ = a₁ * (a₁ * b₁) * b₁ := by rw [← hAB a₁ ha₁ b₁ hb₁]
      _ = (a₁ * a₁) * (b₁ * b₁) := by simp only [mul_assoc]
      _ = 1 := by rw [h1, h3, hz2]
  have hsq2 : a₂ * b₂ * (a₂ * b₂) = 1 := by
    calc a₂ * b₂ * (a₂ * b₂) = a₂ * (b₂ * a₂) * b₂ := by simp only [mul_assoc]
      _ = a₂ * (a₂ * b₂) * b₂ := by rw [← hAB a₂ ha₂ b₂ hb₂]
      _ = (a₂ * a₂) * (b₂ * b₂) := by simp only [mul_assoc]
      _ = 1 := by rw [h2, h4, hz2]
  have hcomm : a₁ * b₁ * (a₂ * b₂) = a₂ * b₂ * (a₁ * b₁) := by
    have e1 : a₁ * b₁ * (a₂ * b₂) = a₁ * a₂ * (b₁ * b₂) := by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hAB a₂ ha₂ b₁ hb₁]
        _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
    have e2 : a₂ * b₂ * (a₁ * b₁) = a₂ * a₁ * (b₂ * b₁) := by
      calc a₂ * b₂ * (a₁ * b₁) = a₂ * (b₂ * a₁) * b₁ := by simp only [mul_assoc]
        _ = a₂ * (a₁ * b₂) * b₁ := by rw [← hAB a₁ ha₁ b₂ hb₂]
        _ = a₂ * a₁ * (b₂ * b₁) := by simp only [mul_assoc]
    have hmain : ∀ u v : P, zc * u * (zc * v) = u * v := by
      intro u v
      calc zc * u * (zc * v) = zc * (u * zc) * v := by simp only [mul_assoc]
        _ = zc * (zc * u) * v := by rw [hzc u]
        _ = (zc * zc) * u * v := by simp only [mul_assoc]
        _ = u * v := by rw [hz2, one_mul]
    rw [e1, e2, hA21, hB21]
    exact (hmain _ _).symm
  have hnot : ∀ a ∈ A, a * a = zc → ∀ b ∈ B, a * b ≠ 1 ∧ a * b ≠ zc := by
    intro a ha hasq b hb
    have haB : a ∉ B := hS.not_mem_B_of_sq hP ha hasq
    constructor
    · intro h
      apply haB
      have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]; exact B.inv_mem hb
    · intro h
      apply haB
      have : a = zc * b⁻¹ := by rw [← h]; group
      rw [this]; exact B.mul_mem hzB (B.inv_mem hb)
  refine ⟨a₁ * b₁, a₂ * b₂, W.mul_mem (hAW ha₁) (hBW hb₁), W.mul_mem (hAW ha₂) (hBW hb₂),
    hsq1, hsq2, hcomm, (hnot a₁ ha₁ h1 b₁ hb₁).1, (hnot a₁ ha₁ h1 b₁ hb₁).2,
    (hnot a₂ ha₂ h2 b₂ hb₂).1, (hnot a₂ ha₂ h2 b₂ hb₂).2, ?_, ?_⟩
  · intro h
    have hmemA : a₁⁻¹ * a₂ ∈ A := A.mul_mem (A.inv_mem ha₁) ha₂
    have hmemB : a₁⁻¹ * a₂ ∈ B := by
      have : a₁⁻¹ * a₂ = b₁ * b₂⁻¹ := by
        have hc2 : a₂ * b₂ = a₁ * b₁ := h
        calc a₁⁻¹ * a₂ = a₁⁻¹ * (a₂ * b₂) * b₂⁻¹ := by group
          _ = a₁⁻¹ * (a₁ * b₁) * b₂⁻¹ := by rw [hc2]
          _ = b₁ * b₂⁻¹ := by group
      rw [this]; exact B.mul_mem hb₁ (B.inv_mem hb₂)
    have hz : a₁⁻¹ * a₂ ∈ zpowers zc := by rw [hS.zpowers_eq hP]; exact ⟨hmemA, hmemB⟩
    rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 hz with h0 | h0
    · apply hne1
      calc a₂ = a₁ * (a₁⁻¹ * a₂) := by group
        _ = a₁ := by rw [h0, mul_one]
    · apply hne2
      calc a₂ = a₁ * (a₁⁻¹ * a₂) := by group
        _ = a₁ * zc := by rw [h0]
  · intro h
    have hmemA : a₁⁻¹ * a₂ ∈ A := A.mul_mem (A.inv_mem ha₁) ha₂
    have hmemB : a₁⁻¹ * a₂ ∈ B := by
      have : a₁⁻¹ * a₂ = b₁ * zc * b₂⁻¹ := by
        have hc2 : a₂ * b₂ = a₁ * b₁ * zc := h
        calc a₁⁻¹ * a₂ = a₁⁻¹ * (a₂ * b₂) * b₂⁻¹ := by group
          _ = a₁⁻¹ * (a₁ * b₁ * zc) * b₂⁻¹ := by rw [hc2]
          _ = b₁ * zc * b₂⁻¹ := by group
      rw [this]; exact B.mul_mem (B.mul_mem hb₁ hzB) (B.inv_mem hb₂)
    have hz : a₁⁻¹ * a₂ ∈ zpowers zc := by rw [hS.zpowers_eq hP]; exact ⟨hmemA, hmemB⟩
    rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 hz with h0 | h0
    · apply hne1
      calc a₂ = a₁ * (a₁⁻¹ * a₂) := by group
        _ = a₁ := by rw [h0, mul_one]
    · apply hne2
      calc a₂ = a₁ * (a₁⁻¹ * a₂) := by group
        _ = a₁ * zc := by rw [h0]

theorem six_dvd_card_of_free (hP : BarShape P zc) (N : Subgroup P) [hN : N.Normal] (hNW : N ≤ W)
    (hz : zc ∈ N) {g : P} (hgA : A₃ = zpowers g) (hg3 : orderOf g = 3) (S : Set ↥N)
    (hSne : ∀ m ∈ S, (m : P) ≠ 1 ∧ (m : P) ≠ zc)
    (hSg : ∀ m : ↥N, m ∈ S → (⟨g * m * g⁻¹, hN.conj_mem _ m.2 g⟩ : ↥N) ∈ S)
    (hSz : ∀ m : ↥N, m ∈ S → (⟨m * zc, N.mul_mem m.2 hz⟩ : ↥N) ∈ S) : 6 ∣ Nat.card ↥S := by
  classical
  have hg1 : g * g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg3] at this
    simpa [pow_succ, mul_assoc] using this
  have hzc := hP.central
  have hz2 := hP.sq
  let f₃ : Function.End ↥S := fun m => ⟨⟨g * (m : ↥N) * g⁻¹, hN.conj_mem _ (m : ↥N).2 g⟩, hSg m m.2⟩
  let f₂ : Function.End ↥S := fun m => ⟨⟨(m : ↥N) * zc, N.mul_mem (m : ↥N).2 hz⟩, hSz m m.2⟩
  have h3 : 3 ∣ Nat.card ↥S := by
    apply three_dvd_of_free f₃
    · intro m
      apply Subtype.ext; apply Subtype.ext
      show g * (g * (g * ((m : ↥N) : P) * g⁻¹) * g⁻¹) * g⁻¹ = ((m : ↥N) : P)
      have : g * (g * (g * ((m : ↥N) : P) * g⁻¹) * g⁻¹) * g⁻¹ =
          (g * g * g) * ((m : ↥N) : P) * (g * g * g)⁻¹ := by group
      rw [this, hg1]; simp
    · intro m hm
      have hfix : g * ((m : ↥N) : P) * g⁻¹ = ((m : ↥N) : P) := congrArg (fun x : ↥S => ((x : ↥N) : P)) hm
      have hcomm : g * ((m : ↥N) : P) = ((m : ↥N) : P) * g := by
        have := congrArg (· * g) hfix
        simpa [mul_assoc] using this
      have hmW : ((m : ↥N) : P) ∈ W := hNW (m : ↥N).2
      have hmem : ((m : ↥N) : P) ∈ zpowers zc := by
        apply hS.fix _ hmW
        intro a ha
        rw [hgA] at ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (show Commute g ((m : ↥N) : P) from hcomm) k).eq
      rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 hmem with h | h
      · exact (hSne m m.2).1 h
      · exact (hSne m m.2).2 h
  have h2 : 2 ∣ Nat.card ↥S := by
    apply two_dvd_of_free f₂
    · intro m
      apply Subtype.ext; apply Subtype.ext
      show ((m : ↥N) : P) * zc * zc = ((m : ↥N) : P)
      rw [mul_assoc, hz2, mul_one]
    · intro m hm
      have hfix : ((m : ↥N) : P) * zc = ((m : ↥N) : P) := congrArg (fun x : ↥S => ((x : ↥N) : P)) hm
      have : zc = 1 := by
        have := congrArg (fun x => ((m : ↥N) : P)⁻¹ * x) hfix
        simpa using this
      exact hP.ne_one this
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3

theorem elementary_of_card_eight (hP : BarShape P zc) (N : Subgroup P) [hN : N.Normal]
    (hNW : N ≤ W) (hz : zc ∈ N) (hcard : Nat.card ↥N = 8) {n : P} (hnN : n ∈ N)
    (hn2 : n * n = 1) (hn1 : n ≠ 1) (hnz : n ≠ zc) :
    (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ a ∈ N, a * a = 1) := by
  classical
  obtain ⟨g, hgA, hg3, hgz⟩ := hS.exists_gen₃
  have hz2 := hP.sq
  let S₁ : Set ↥N := {m | (m : P) * m = 1 ∧ (m : P) ≠ 1 ∧ (m : P) ≠ zc}
  let S₂ : Set ↥N := {m | (m : P) * m = zc}
  have hconj : ∀ m : ↥N, ((g * (m : P) * g⁻¹) * (g * (m : P) * g⁻¹)) = g * ((m : P) * m) * g⁻¹ := by
    intro m; group
  have hS1 : 6 ∣ Nat.card ↥S₁ := by
    apply hS.six_dvd_card_of_free hP N hNW hz hgz hg3 S₁
    · intro m hm; exact hm.2
    · intro m hm
      refine ⟨?_, ?_, ?_⟩
      · show g * (m : P) * g⁻¹ * (g * (m : P) * g⁻¹) = 1
        rw [hconj, hm.1]; simp
      · show g * (m : P) * g⁻¹ ≠ 1
        intro h
        apply hm.2.1
        have : (m : P) = g⁻¹ * (g * (m : P) * g⁻¹) * g := by group
        rw [this, h]; simp
      · show g * (m : P) * g⁻¹ ≠ zc
        intro h
        apply hm.2.2
        have : (m : P) = g⁻¹ * (g * (m : P) * g⁻¹) * g := by group
        rw [this, h, hP.central g⁻¹, mul_assoc]; simp
    · intro m hm
      have hzcm : zc * (m : P) = (m : P) * zc := (hP.central _).symm
      refine ⟨?_, ?_, ?_⟩
      · show (m : P) * zc * ((m : P) * zc) = 1
        calc (m : P) * zc * ((m : P) * zc) = (m : P) * (zc * (m : P)) * zc := by simp only [mul_assoc]
          _ = (m : P) * ((m : P) * zc) * zc := by rw [hzcm]
          _ = ((m : P) * m) * (zc * zc) := by simp only [mul_assoc]
          _ = 1 := by rw [hm.1, hz2, one_mul]
      · show (m : P) * zc ≠ 1
        intro h
        apply hm.2.2
        have := eq_inv_of_mul_eq_one_left h
        have h3 : zc⁻¹ = zc := by
          have : zc * zc = 1 := hz2
          exact (eq_inv_of_mul_eq_one_left this).symm
        rw [this, h3]
      · show (m : P) * zc ≠ zc
        intro h
        apply hm.2.1
        have := congrArg (fun x => x * zc⁻¹) h
        simpa using this
  have hS2 : 6 ∣ Nat.card ↥S₂ := by
    apply hS.six_dvd_card_of_free hP N hNW hz hgz hg3 S₂
    · intro m hm
      constructor
      · intro h
        have : (m : P) * m = 1 := by rw [h, mul_one]
        have h2 : zc = 1 := hm ▸ this
        exact hP.ne_one h2
      · intro h
        have : (m : P) * m = 1 := by rw [h]; exact hz2
        have h2 : zc = 1 := hm ▸ this
        exact hP.ne_one h2
    · intro m hm
      show g * (m : P) * g⁻¹ * (g * (m : P) * g⁻¹) = zc
      rw [hconj]
      have : (m : P) * m = zc := hm
      rw [this, hP.central g, mul_assoc]; simp
    · intro m hm
      have hzcm : zc * (m : P) = (m : P) * zc := (hP.central _).symm
      show (m : P) * zc * ((m : P) * zc) = zc
      calc (m : P) * zc * ((m : P) * zc) = (m : P) * (zc * (m : P)) * zc := by simp only [mul_assoc]
        _ = (m : P) * ((m : P) * zc) * zc := by rw [hzcm]
        _ = ((m : P) * m) * (zc * zc) := by simp only [mul_assoc]
        _ = zc := by rw [(hm : (m : P) * m = zc), hz2, mul_one]
  have hn' : (⟨n, hnN⟩ : ↥N) ∈ S₁ := ⟨hn2, hn1, hnz⟩
  have hpos : 0 < S₁.ncard := by
    rw [Set.ncard_pos]; exact ⟨_, hn'⟩
  have hdisj12 : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro m h1 h2
    have : (m : P) * m = 1 := h1.1
    have h3 : zc = 1 := (h2 : (m : P) * m = zc) ▸ this
    exact hP.ne_one h3
  let T : Set ↥N := {1, ⟨zc, hz⟩}
  have hdisjT : Disjoint (S₁ ∪ S₂) T := by
    rw [Set.disjoint_left]
    intro m hm hmT
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hmT
    rcases hmT with rfl | rfl
    · rcases hm with h | h
      · exact h.2.1 rfl
      · have : ((1 : ↥N) : P) * ((1 : ↥N) : P) = zc := h
        simp at this
        exact hP.ne_one this.symm
    · rcases hm with h | h
      · exact h.2.2 rfl
      · have : zc * zc = zc := h
        rw [hz2] at this
        exact hP.ne_one this.symm
  have hTcard : T.ncard = 2 := by
    apply Set.ncard_pair
    intro h
    have := congrArg (fun x : ↥N => (x : P)) h
    exact hP.ne_one (by simpa using this.symm)
  have hle : (S₁ ∪ S₂ ∪ T).ncard ≤ 8 := by
    have := Set.ncard_le_card (S₁ ∪ S₂ ∪ T)
    rwa [hcard] at this
  rw [Set.ncard_union_eq hdisjT, Set.ncard_union_eq hdisj12, hTcard] at hle
  have h1' : 6 ∣ S₁.ncard := by rwa [Nat.card_coe_set_eq] at hS1
  have h2' : 6 ∣ S₂.ncard := by rwa [Nat.card_coe_set_eq] at hS2
  have hS2z : S₂.ncard = 0 := by omega
  have hS2e : S₂ = ∅ := by
    rw [← Set.ncard_eq_zero]
    exact hS2z
  have hsq : ∀ m ∈ N, m * m = 1 := by
    intro m hm
    rcases hS.sq_W hP m (hNW hm) with h | h
    · exact h
    · exfalso
      have : (⟨m, hm⟩ : ↥N) ∈ S₂ := h
      rw [hS2e] at this
      exact this
  refine ⟨?_, hsq⟩
  intro a ha b hb
  have hab := hsq (a * b) (N.mul_mem ha hb)
  have haa := hsq a ha
  have hbb := hsq b hb
  have h1 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have ha' : a⁻¹ = a := (eq_inv_of_mul_eq_one_left haa).symm
  have hb' : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hbb).symm
  calc a * b = (a * b)⁻¹ := h1
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem exists_E8_W (hP : BarShape P zc) :
    ∃ E : Subgroup P, E ≤ W ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
      8 ≤ Nat.card ↥E := by
  classical
  obtain ⟨e₁, e₂, he₁W, he₂W, h1, h2, h12, hn1, hnz1, hn2, hnz2, hne, hnez⟩ := hS.exists_pair hP
  have hz2 := hP.sq
  have hzc := hP.central
  have hzW : zc ∈ W := hS.zc_mem
  let s : Set P := {zc, e₁, e₂}
  have hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    intro a ha b hb
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | rfl | exact hzc _ | exact (hzc _).symm | exact h12 | exact h12.symm
  have hs : ∀ a ∈ s, a * a = 1 := by
    intro a ha
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hz2
    · exact h1
    · exact h2
  obtain ⟨hcomm, hsq⟩ := closure_comm_sq hc hs
  have hsW : s ⊆ (W : Set P) := by
    intro a ha
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hzW
    · exact he₁W
    · exact he₂W
  have hordz : orderOf zc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hP.ne_one
  have hz1 : Nat.card ↥(zpowers zc) = 2 := by rw [Nat.card_zpowers, hordz]
  let S₂ : Subgroup P := closure ({zc, e₁} : Set P)
  have hS₂E : S₂ ≤ closure s := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hS₁S₂ : zpowers zc ≤ S₂ := zpowers_le.2 (subset_closure (by simp))
  have he₁S₂ : e₁ ∈ S₂ := subset_closure (by simp)
  have he₁S₁ : e₁ ∉ zpowers zc := by
    intro h
    rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 h with h | h
    · exact hn1 h
    · exact hnz1 h
  have hcard2 : 4 ≤ Nat.card ↥S₂ := by
    have hd : Nat.card ↥(zpowers zc) ∣ Nat.card ↥S₂ := Subgroup.card_dvd_of_le hS₁S₂
    have hne' : Nat.card ↥S₂ ≠ Nat.card ↥(zpowers zc) := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge hS₁S₂ (le_of_eq h)
      exact he₁S₁ (this ▸ he₁S₂)
    rw [hz1] at hd hne'
    have := Nat.card_pos (α := ↥S₂)
    omega
  have hze : zc * e₁ = e₁ * zc := (hzc e₁).symm
  have p1 : zc * (zc * e₁) = e₁ := by rw [← mul_assoc, hz2, one_mul]
  have p2 : e₁ * zc = zc * e₁ := hze.symm
  have p3 : e₁ * (zc * e₁) = zc := by rw [← mul_assoc, p2, mul_assoc, h1, mul_one]
  have p4 : zc * e₁ * zc = e₁ := by rw [mul_assoc, p2, p1]
  have p5 : zc * e₁ * e₁ = zc := by rw [mul_assoc, h1, mul_one]
  have p6 : zc * e₁ * (zc * e₁) = 1 := by rw [mul_assoc, p3, hz2]
  have zinv : zc⁻¹ = zc := (eq_inv_of_mul_eq_one_left hz2).symm
  have einv : e₁⁻¹ = e₁ := (eq_inv_of_mul_eq_one_left h1).symm
  have hdesc : ∀ x ∈ S₂, x = 1 ∨ x = zc ∨ x = e₁ ∨ x = zc * e₁ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
    | one => left; rfl
    | mul x y hx hy hx' hy' =>
      rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
        simp [hz2, h1, p1, p2, p3, p4, p5, p6]
    | inv x hx hx' =>
      rcases hx' with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, zinv, einv, p2]
  have he₂S₂ : e₂ ∉ S₂ := by
    intro h
    rcases hdesc e₂ h with h | h | h | h
    · exact hn2 h
    · exact hnz2 h
    · exact hne h
    · exact hnez (by rw [h, p2])
  have he₂E : e₂ ∈ closure s := subset_closure (by simp [s])
  have hd : Nat.card ↥S₂ ∣ Nat.card ↥(closure s) := Subgroup.card_dvd_of_le hS₂E
  have hne'' : Nat.card ↥(closure s) ≠ Nat.card ↥S₂ := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hS₂E (le_of_eq h)
    exact he₂S₂ (this ▸ he₂E)
  obtain ⟨k, hk⟩ := hd
  have hpos := Nat.card_pos (α := ↥(closure s))
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    simp at hk
    exact hne'' hk
  have hk2 : 2 ≤ k := by omega
  refine ⟨closure s, (Subgroup.closure_le W).2 hsW, hcomm, hsq, ?_⟩
  calc 8 ≤ Nat.card ↥S₂ * 2 := by omega
    _ ≤ Nat.card ↥S₂ * k := Nat.mul_le_mul_left _ hk2
    _ = Nat.card ↥(closure s) := hk.symm

theorem normal_cases (hP : BarShape P zc) (N : Subgroup P) [hN : N.Normal] (hz : zc ∈ N) :
    (Nat.card ↥N = 2 ∨ Nat.card ↥N = 8 ∨ Nat.card ↥N = 32 ∨ Nat.card ↥N = 96 ∨
      Nat.card ↥N = 192) ∧
    ((∀ n ∈ N, n * n = 1 → n = 1 ∨ n = zc) ∨
      ∃ E : Subgroup P, E ≤ N ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
        8 ≤ Nat.card ↥E) := by
  classical
  have hz2 := hP.sq
  by_cases hNW : N ≤ W
  · have hcard := hS.card_normal_le_W hP N hNW hz
    rcases hcard with h2 | h8 | h32
    · refine ⟨Or.inl h2, Or.inl ?_⟩
      have hordz : orderOf zc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hP.ne_one
      have hN2 : zpowers zc = N := by
        apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
        rw [Nat.card_zpowers, hordz, h2]
      intro n hn hn2
      rw [← hN2] at hn
      exact (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 hn
    · refine ⟨Or.inr (Or.inl h8), ?_⟩
      by_cases hex : ∃ n ∈ N, n * n = 1 ∧ n ≠ 1 ∧ n ≠ zc
      · obtain ⟨n, hnN, hn2, hn1, hnz⟩ := hex
        obtain ⟨hc, hs⟩ := hS.elementary_of_card_eight hP N hNW hz h8 hnN hn2 hn1 hnz
        exact Or.inr ⟨N, le_refl _, hc, hs, by rw [h8]⟩
      · left
        intro n hn hn2
        by_contra hcon
        push Not at hcon
        exact hex ⟨n, hn, hn2, hcon.1, hcon.2⟩
    · refine ⟨Or.inr (Or.inr (Or.inl h32)), Or.inr ?_⟩
      have hNeq : N = W := Subgroup.eq_of_le_of_card_ge hNW (by rw [hS.card_W, h32])
      obtain ⟨E, hEW, hEc, hEs, hE8⟩ := hS.exists_E8_W hP
      exact ⟨E, hNeq ▸ hEW, hEc, hEs, hE8⟩
  · have hWN : W ≤ N := hS.W_le_of_not_le hP N hNW
    have hWn := hS.normal_W
    refine ⟨?_, Or.inr ?_⟩
    ·
      set π := hS.piHom with hπ
      have hker : π.ker = W := by
        ext x; rw [MonoidHom.mem_ker, hπ, hS.piHom_ker]
      have hcm : Subgroup.comap π (Subgroup.map π N) = N :=
        Subgroup.comap_map_eq_self (by rw [hker]; exact hWN)
      have hMn : (Subgroup.map π N).Normal := hN.map π hS.piHom_surjective
      have hidx : N.index = (Subgroup.map π N).index := by
        conv_lhs => rw [← hcm]
        exact Subgroup.index_comap_of_surjective _ hS.piHom_surjective
      have h1 := Subgroup.card_mul_index N
      rw [hP.card_eq] at h1
      have hMc : Nat.card ↥(Subgroup.map π N) ≠ 2 := perm3_normal_card_ne_two _
      have h2 := Subgroup.card_mul_index (Subgroup.map π N)
      have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
      rw [h6, ← hidx] at h2
      have hMdvd : Nat.card ↥(Subgroup.map π N) ∣ 6 := ⟨N.index, h2.symm⟩
      have hNW32 : Nat.card ↥N ≠ 32 := by
        intro h32
        apply hNW
        have : N = W := (Subgroup.eq_of_le_of_card_ge hWN (by rw [hS.card_W, h32])).symm
        rw [this]
      have hNcard : 32 ∣ Nat.card ↥N := by
        have := Subgroup.card_dvd_of_le hWN
        rwa [hS.card_W] at this
      obtain ⟨k, hk⟩ := hNcard
      have hidxpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hk' : k * N.index = 6 := by
        have h3 : 32 * (k * N.index) = 32 * 6 := by
          calc 32 * (k * N.index) = (32 * k) * N.index := by ring
            _ = 192 := by rw [← hk]; exact h1
            _ = 32 * 6 := by norm_num
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
      have hkM : k = Nat.card ↥(Subgroup.map π N) := by
        apply Nat.eq_of_mul_eq_mul_right hidxpos
        rw [hk', h2]
      have hk6 : k ∣ 6 := by rw [hkM]; exact hMdvd
      have hk1 : k ≠ 1 := by
        rintro rfl
        apply hNW32
        omega
      have hk2 : k ≠ 2 := by
        rintro rfl
        exact hMc hkM.symm
      have hkle : k ≤ 6 := Nat.le_of_dvd (by norm_num) hk6
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk6 (by norm_num)
      interval_cases k <;> omega
    · obtain ⟨E, hEW, hEc, hEs, hE8⟩ := hS.exists_E8_W hP
      exact ⟨E, hEW.trans hWN, hEc, hEs, hE8⟩

end BarShape.Spec

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
