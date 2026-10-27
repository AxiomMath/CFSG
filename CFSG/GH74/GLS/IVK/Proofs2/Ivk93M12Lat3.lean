module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lat1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup

variable {P : Type} [Group P] [Finite P]

theorem elemAb_card_le_two {G : Type*} [Group G] [Finite G] {S : Subgroup G} {σ : G}
    (hσ : σ * σ = 1) (h : ∀ x ∈ S, x = 1 ∨ x = σ) : Nat.card ↥S ≤ 2 := by
  have hle : S ≤ zpowers σ := by
    intro x hx
    rcases h x hx with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσ)
  calc Nat.card ↥S ≤ Nat.card ↥(zpowers σ) := Subgroup.card_le_of_le hle
    _ = orderOf σ := Nat.card_zpowers σ
    _ ≤ 2 := Nat.le_of_dvd two_pos h2

theorem elemAb_perm3_card_le_two (S : Subgroup (Equiv.Perm (Fin 3)))
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h2 : ∀ a ∈ S, a * a = 1) : Nat.card ↥S ≤ 2 := by
  have key : ∀ σ x : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → x * x = 1 → σ * x = x * σ →
      x = 1 ∨ x = σ := by decide +kernel
  by_cases hex : ∃ σ ∈ S, σ ≠ 1
  · obtain ⟨σ, hσ, hσ1⟩ := hex
    exact elemAb_card_le_two (h2 σ hσ) fun x hx =>
      key σ x hσ1 (h2 σ hσ) (h2 x hx) (hc σ hσ x hx)
  · push Not at hex
    exact elemAb_card_le_two (σ := 1) (mul_one 1) fun x hx => Or.inl (hex x hx)

theorem elemAb_perm3_conj : ∀ σ τ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → τ ≠ 1 →
    τ * τ * τ = 1 → τ * (σ * τ * σ⁻¹) = 1 := by decide +kernel

theorem elemAb_card_le_eight {zc : P} {W A' D : Subgroup P} [A'.Normal]
    (hz1 : zc ≠ 1) (hz2 : zc * zc = 1) (hcases : ∀ a ∈ A', a = 1 ∨ a = zc ∨ a * a = zc)
    (hA : Nat.card ↥A' = 8) (hAW : A' ≤ W) (hW : Nat.card ↥W = 32) (hDW : D ≤ W)
    (hD2 : ∀ d ∈ D, d * d = 1) :
    Nat.card ↥D ≤ 8 ∧ (Nat.card ↥D = 8 → D ⊔ A' = W) := by
  have hmul := card_sup_mul_card_inf_of_normal' D A'
  have hinf : Nat.card ↥(D ⊓ A') ≤ 2 := by
    refine elemAb_card_le_two hz2 fun x hx => ?_
    rcases hcases x hx.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h.symm.trans (hD2 x hx.1)) hz1
  have hsup : Nat.card ↥(D ⊔ A') ≤ 32 :=
    (Subgroup.card_le_of_le (sup_le hDW hAW)).trans hW.le
  have hpos : 0 < Nat.card ↥(D ⊓ A') := Nat.card_pos
  rw [hA] at hmul
  have hle : Nat.card ↥(D ⊔ A') * Nat.card ↥(D ⊓ A') ≤ 32 * 2 := Nat.mul_le_mul hsup hinf
  refine ⟨by omega, fun hD => ?_⟩
  rw [hD] at hmul
  have h32 : Nat.card ↥(D ⊔ A') = 32 := by
    rcases (by omega : Nat.card ↥(D ⊓ A') = 1 ∨ Nat.card ↥(D ⊓ A') = 2) with h | h
    · rw [h] at hmul; omega
    · rw [h] at hmul; omega
  exact Subgroup.eq_of_le_of_card_ge (sup_le hDW hAW) (by rw [hW, h32])

omit [Finite P] in
theorem elemAb_conj_inf_mem {X Y D W : Subgroup P} [X.Normal] [Y.Normal] {t : P}
    (hXW : X ≤ W) (hDt : ∀ d ∈ D, t * d = d * t) (hDY : D ⊔ Y = W) :
    ∀ x ∈ X, x⁻¹ * (t * x * t⁻¹) ∈ X ⊓ Y := by
  intro x hx
  have hxW : x ∈ D ⊔ Y := by rw [hDY]; exact hXW hx
  obtain ⟨d, hd, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxW
  have h1 : (d * y)⁻¹ * (t * (d * y) * t⁻¹) = y⁻¹ * (t * y * t⁻¹) := by
    calc (d * y)⁻¹ * (t * (d * y) * t⁻¹) = y⁻¹ * (d⁻¹ * (t * d) * y * t⁻¹) := by group
      _ = y⁻¹ * (d⁻¹ * (d * t) * y * t⁻¹) := by rw [hDt d hd]
      _ = y⁻¹ * (t * y * t⁻¹) := by group
  refine ⟨?_, ?_⟩
  · exact X.mul_mem (X.inv_mem hx) ((inferInstance : X.Normal).conj_mem _ hx t)
  · rw [h1]
    exact Y.mul_mem (Y.inv_mem hy) ((inferInstance : Y.Normal).conj_mem _ hy t)

omit [Finite P] in
theorem elemAb_conj_abs {Q : Type*} [Group Q] {γ τ δ ω ω₁ ω₂ : Q}
    (hω₁ : ω₁ = γ * ω * γ⁻¹) (hω₂ : ω₂ = γ * ω₁ * γ⁻¹)
    (hu : τ * γ * τ⁻¹ = γ⁻¹ * δ) (hδ : δ * ω₁ = ω₁ * δ)
    (hτ₁ : τ * ω₁ = ω₁ * τ) (hτ₂ : τ * ω₂ = ω₂ * τ) : ω₂ = ω := by
  have h1 : τ⁻¹ * ω₁ * τ = ω₁ := by
    calc τ⁻¹ * ω₁ * τ = τ⁻¹ * (ω₁ * τ) := mul_assoc _ _ _
      _ = τ⁻¹ * (τ * ω₁) := by rw [hτ₁]
      _ = ω₁ := inv_mul_cancel_left _ _
  have e1 : (τ * γ * τ⁻¹) * ω₁ * (τ * γ * τ⁻¹)⁻¹ = ω₂ := by
    calc (τ * γ * τ⁻¹) * ω₁ * (τ * γ * τ⁻¹)⁻¹ = τ * γ * (τ⁻¹ * ω₁ * τ) * γ⁻¹ * τ⁻¹ := by group
      _ = τ * (γ * ω₁ * γ⁻¹) * τ⁻¹ := by rw [h1]; group
      _ = τ * ω₂ * τ⁻¹ := by rw [hω₂]
      _ = ω₂ := by rw [hτ₂]; group
  have e2 : (τ * γ * τ⁻¹) * ω₁ * (τ * γ * τ⁻¹)⁻¹ = ω := by
    calc (τ * γ * τ⁻¹) * ω₁ * (τ * γ * τ⁻¹)⁻¹ = (γ⁻¹ * δ) * ω₁ * (γ⁻¹ * δ)⁻¹ := by rw [hu]
      _ = γ⁻¹ * (δ * ω₁) * δ⁻¹ * γ := by group
      _ = γ⁻¹ * (ω₁ * δ) * δ⁻¹ * γ := by rw [hδ]
      _ = γ⁻¹ * ω₁ * γ := by group
      _ = ω := by rw [hω₁]; group
  exact e1.symm.trans e2

omit [Finite P] in
theorem elemAb_gen_comm {Q : Type*} [Group Q] {γ ω : Q} (hγ : γ * γ * γ = 1)
    (h : γ * (γ * ω * γ⁻¹) * γ⁻¹ = ω) : γ * ω * γ⁻¹ = ω := by
  have hinv : γ⁻¹ = γ * γ := (eq_inv_of_mul_eq_one_left hγ).symm
  have hinv2 : γ⁻¹ * γ⁻¹ = γ := by
    calc γ⁻¹ * γ⁻¹ = (γ * γ) * (γ * γ) := by rw [hinv]
      _ = γ * (γ * γ * γ) := by group
      _ = γ := by rw [hγ, mul_one]
  have h5 : γ⁻¹ * ω * γ = ω := by
    calc γ⁻¹ * ω * γ = (γ * γ) * ω * (γ⁻¹ * γ⁻¹) := by rw [hinv2, ← hinv]
      _ = γ * (γ * ω * γ⁻¹) * γ⁻¹ := by group
      _ = ω := h
  calc γ * ω * γ⁻¹ = γ * (γ⁻¹ * ω * γ) * γ⁻¹ := by rw [h5]
    _ = ω := by group

namespace BarShape.Spec

variable {zc : P} {W A B A₃ : Subgroup P} (hS : BarShape.Spec zc W A B A₃)
include hS

theorem elemAb_normal_B : B.Normal := by
  obtain ⟨eA⟩ := hS.eA
  have hAn := hS.normal_A
  have hWn := hS.normal_W
  obtain ⟨hAB, hcomm, hcard⟩ := hS.cp
  refine ⟨fun b hb x => ?_⟩
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := hS.exists_decomp _ (hWn.conj_mem b (hS.B_le_W hb) x)
  have hc : ∀ a ∈ A, a * a₁ = a₁ * a := by
    intro a ha
    have ha' : x⁻¹ * a * x ∈ A := by
      have := hAn.conj_mem a ha x⁻¹
      simpa using this
    have h1 := hcomm _ ha' b hb
    have h2 : a * (x * b * x⁻¹) = (x * b * x⁻¹) * a := by
      calc a * (x * b * x⁻¹) = x * ((x⁻¹ * a * x) * b) * x⁻¹ := by group
        _ = x * (b * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
        _ = (x * b * x⁻¹) * a := by group
    rw [hab] at h2
    have h3 : a * (a₁ * b₁) = (a * a₁) * b₁ := (mul_assoc a a₁ b₁).symm
    have h4 : (a₁ * b₁) * a = (a₁ * a) * b₁ := by
      rw [mul_assoc, ← hcomm a ha b₁ hb₁, ← mul_assoc]
    rw [h3, h4] at h2
    exact mul_right_cancel h2
  have ha₁B : a₁ ∈ A ⊓ B :=
    inf_eq_center_of_q8 hcomm hcard eA a₁ ha₁ fun a' ha' => (hc a' ha').symm
  rw [hab]
  exact B.mul_mem ha₁B.2 hb₁

theorem elemAb_comm_W (hP : BarShape P zc) :
    ∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ zpowers zc := by
  intro w₁ hw₁ w₂ hw₂
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hS.exists_decomp w₁ hw₁
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hS.exists_decomp w₂ hw₂
  have hAB := hS.comm_AB
  have e1 : b₁ * a₂ = a₂ * b₁ := (hAB a₂ ha₂ b₁ hb₁).symm
  have e2 : (b₁ * b₂ * b₁⁻¹) * a₁⁻¹ = a₁⁻¹ * (b₁ * b₂ * b₁⁻¹) :=
    (hAB a₁⁻¹ (A.inv_mem ha₁) _ (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁))).symm
  have e3 : (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹ = a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) :=
    (hAB a₂⁻¹ (A.inv_mem ha₂) _
      (B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂))).symm
  have key : a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹ =
      (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by
    calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
        = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [e1]
      _ = a₁ * a₂ * ((b₁ * b₂ * b₁⁻¹) * a₁⁻¹) * b₂⁻¹ * a₂⁻¹ := by group
      _ = a₁ * a₂ * (a₁⁻¹ * (b₁ * b₂ * b₁⁻¹)) * b₂⁻¹ * a₂⁻¹ := by rw [e2]
      _ = a₁ * a₂ * a₁⁻¹ * ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹) := by group
      _ = a₁ * a₂ * a₁⁻¹ * (a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)) := by rw [e3]
      _ = (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by group
  rw [key]
  have hz : ∀ x : P, x = 1 ∨ x = zc → x ∈ zpowers zc := by
    rintro x (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _
  exact (zpowers zc).mul_mem (hz _ (hS.comm_A hP a₁ ha₁ a₂ ha₂)) (hz _ (hS.comm_B hP b₁ hb₁ b₂ hb₂))

theorem elemAb_comm_of_sup (hP : BarShape P zc) {D : Subgroup P} {t : P}
    (hDt : ∀ d ∈ D, t * d = d * t) (hDA : D ⊔ A = W) (hDB : D ⊔ B = W) :
    ∀ w ∈ W, w⁻¹ * (t * w * t⁻¹) ∈ zpowers zc := by
  have := hS.normal_A
  have := hS.elemAb_normal_B
  have hZc : ∀ z ∈ zpowers zc, ∀ x : P, x * z = z * x := fun z hz x =>
    mem_center_iff.1 (zpowers_le.2 (mem_center_iff.2 hP.central) hz) x
  have hA' : ∀ a ∈ A, a⁻¹ * (t * a * t⁻¹) ∈ zpowers zc := by
    intro a ha
    rw [hS.zpowers_eq hP]
    exact elemAb_conj_inf_mem hS.A_le_W hDt hDB a ha
  have hB' : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ zpowers zc := by
    intro b hb
    rw [hS.zpowers_eq hP, inf_comm]
    exact elemAb_conj_inf_mem hS.B_le_W hDt hDA b hb
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hS.exists_decomp w hw
  have e : (a * b)⁻¹ * (t * (a * b) * t⁻¹) =
      (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by
    calc (a * b)⁻¹ * (t * (a * b) * t⁻¹) = b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = (a⁻¹ * (t * a * t⁻¹)) * b⁻¹ * (t * b * t⁻¹) := by rw [hZc _ (hA' a ha) b⁻¹]
      _ = (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by group
  rw [e]
  exact (zpowers zc).mul_mem (hA' a ha) (hB' b hb)

theorem elemAb_commutes_gen (hP : BarShape P zc) {g t w₀ : P} (hg3 : g * g * g = 1)
    (hw₀ : w₀ ∈ W) (hu : t * g * t⁻¹ = g⁻¹ * w₀)
    (ht : ∀ w ∈ W, w⁻¹ * (t * w * t⁻¹) ∈ zpowers zc) :
    ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ zpowers zc := by
  have hWn := hS.normal_W
  have hN : (zpowers zc).Normal :=
    Subgroup.normal_of_le_center (zpowers_le.2 (mem_center_iff.2 hP.central))
  let ρ : P →* P ⧸ zpowers zc := QuotientGroup.mk' _
  have hρ : ∀ x : P, ρ x = 1 ↔ x ∈ zpowers zc := fun x => QuotientGroup.eq_one_iff x
  have hρe : ∀ x y : P, ρ x = ρ y ↔ x⁻¹ * y ∈ zpowers zc := fun x y => QuotientGroup.eq
  have hτ : ∀ w ∈ W, ρ t * ρ w = ρ w * ρ t := by
    intro w hw
    have h1 : ρ w = ρ (t * w * t⁻¹) := (hρe _ _).2 (ht w hw)
    rw [map_mul, map_mul, map_inv] at h1
    calc ρ t * ρ w = (ρ t * ρ w * (ρ t)⁻¹) * ρ t := by group
      _ = ρ w * ρ t := by rw [← h1]
  have hV : ∀ w₁ ∈ W, ∀ w₂ ∈ W, ρ w₁ * ρ w₂ = ρ w₂ * ρ w₁ := by
    intro w₁ h₁ w₂ h₂
    have h := (hρ _).2 (hS.elemAb_comm_W hP w₁ h₁ w₂ h₂)
    simp only [map_mul, map_inv] at h
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
  intro w hw
  have hw₁ : g * w * g⁻¹ ∈ W := hWn.conj_mem w hw g
  have hw₂ : g * (g * w * g⁻¹) * g⁻¹ ∈ W := hWn.conj_mem _ hw₁ g
  have hu' : ρ t * ρ g * (ρ t)⁻¹ = (ρ g)⁻¹ * ρ w₀ := by
    simpa only [map_mul, map_inv] using congrArg ρ hu
  have key := elemAb_conj_abs (γ := ρ g) (τ := ρ t) (δ := ρ w₀) (ω := ρ w)
    (ω₁ := ρ (g * w * g⁻¹)) (ω₂ := ρ (g * (g * w * g⁻¹) * g⁻¹))
    (by simp only [map_mul, map_inv]) (by simp only [map_mul, map_inv]) hu'
    (hV w₀ hw₀ _ hw₁) (hτ _ hw₁) (hτ _ hw₂)
  simp only [map_mul, map_inv] at key
  have hg3' : ρ g * ρ g * ρ g = 1 := by
    simpa only [map_mul, map_one] using congrArg ρ hg3
  have h := elemAb_gen_comm hg3' key
  refine (hρ _).1 ?_
  simp only [map_mul, map_inv]
  rw [h]
  exact mul_inv_cancel _

theorem elemAb_false_of_frame (hP : BarShape P zc) {D : Subgroup P} {t : P} (htW : t ∉ W)
    (ht2 : t * t = 1) (hDt : ∀ d ∈ D, t * d = d * t) (hDA : D ⊔ A = W) (hDB : D ⊔ B = W) :
    False := by
  obtain ⟨g, -, hg3, hgz⟩ := hS.exists_gen₃
  have hg1 : g * g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg3] at this
    simpa [pow_succ, mul_assoc] using this
  have hgW : g ∉ W := by
    intro h
    have := orderOf_dvd_natCard (⟨g, h⟩ : ↥W)
    rw [Subgroup.orderOf_mk, hg3, hS.card_W] at this
    omega
  have hσ1 : hS.piHom t ≠ 1 := fun h => htW ((hS.piHom_ker t).1 h)
  have hσ2 : hS.piHom t * hS.piHom t = 1 := by rw [← map_mul, ht2, map_one]
  have hτ1 : hS.piHom g ≠ 1 := fun h => hgW ((hS.piHom_ker g).1 h)
  have hτ3 : hS.piHom g * hS.piHom g * hS.piHom g = 1 := by
    rw [← map_mul, ← map_mul, hg1, map_one]
  have hw₀ : g * (t * g * t⁻¹) ∈ W := by
    rw [← hS.piHom_ker]
    have := elemAb_perm3_conj _ _ hσ1 hσ2 hτ1 hτ3
    simpa only [map_mul, map_inv] using this
  have hcomm := hS.elemAb_commutes_gen hP hg1 hw₀ (by group)
    (hS.elemAb_comm_of_sup hP hDt hDA hDB)
  have hWle : W ≤ zpowers zc := fun w hw => hS.fix_gen hP hgz hg3 hw (hcomm w hw)
  have hcard := Subgroup.card_le_of_le hWle
  have hz2 : orderOf zc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hP.sq) hP.ne_one
  rw [hS.card_W, Nat.card_zpowers, hz2] at hcard
  omega

omit [Finite P] in
theorem elemAb_card_le_two_mul (E : Subgroup P) (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a * a = 1) : Nat.card ↥E ≤ 2 * Nat.card ↥(W ⊓ E) := by
  have hker : hS.piHom.ker = W := by
    ext x
    rw [MonoidHom.mem_ker, hS.piHom_ker]
  have h1 := Subgroup.relIndex_mul_card (H := W) (K := E)
  have h3 := Subgroup.relIndex_ker (K := E) hS.piHom
  rw [hker] at h3
  have h4 : Nat.card ↥(E.map hS.piHom) ≤ 2 := by
    refine elemAb_perm3_card_le_two _ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hc x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, h2 x hx, map_one]
  rw [← h1, h3]
  exact Nat.mul_le_mul_right _ h4

theorem card_elemAbelian_le (hP : BarShape P zc) (E : Subgroup P)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card ↥E ≤ 8 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨eA⟩ := hS.eA
  obtain ⟨eB⟩ := hS.eB
  have hAn := hS.normal_A
  have hBn := hS.elemAb_normal_B
  have hA8 : Nat.card ↥A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB8 : Nat.card ↥B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hD2 : ∀ d ∈ W ⊓ E, d * d = 1 := fun d hd => h2 d hd.2
  obtain ⟨hD8, hDA⟩ := elemAb_card_le_eight hP.ne_one hP.sq (hS.A_cases hP) hA8 hS.A_le_W
    hS.card_W (inf_le_left : W ⊓ E ≤ W) hD2
  obtain ⟨-, hDB⟩ := elemAb_card_le_eight hP.ne_one hP.sq (hS.B_cases hP) hB8 hS.B_le_W
    hS.card_W (inf_le_left : W ⊓ E ≤ W) hD2
  have h1 := hS.elemAb_card_le_two_mul E hc h2
  have hD5 : 5 ≤ Nat.card ↥(W ⊓ E) := by omega
  have hDdvd : Nat.card ↥(W ⊓ E) ∣ 32 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : W ⊓ E ≤ W)
    rwa [hS.card_W] at this
  have hDcard : Nat.card ↥(W ⊓ E) = 8 := by
    generalize Nat.card ↥(W ⊓ E) = n at hD8 hD5 hDdvd ⊢
    interval_cases n <;> omega
  obtain ⟨t, htE, htW⟩ : ∃ t ∈ E, t ∉ W := by
    by_contra hne
    push Not at hne
    have hEW : E ≤ W := fun x hx => hne x hx
    rw [inf_eq_right.2 hEW] at hD8
    omega
  exact hS.elemAb_false_of_frame hP htW (h2 t htE)
    (fun d hd => hc t htE d ((inf_le_right : W ⊓ E ≤ E) hd)) (hDA hDcard) (hDB hDcard)

end BarShape.Spec

theorem BarShape.card_elemAbelian_le {zc : P} (hP : BarShape P zc) (E : Subgroup P)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card ↥E ≤ 8 := by
  obtain ⟨W, A, B, A₃, hS⟩ := hP.exists_spec
  exact hS.card_elemAbelian_le hP E hc h2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
