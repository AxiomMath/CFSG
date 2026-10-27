module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingComm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiY

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3EndingPencilInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s : G), U3EndingData G L f t T R₂ U₁ s →
      (∃ Z J : Subgroup G, (∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) ∧
        (∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
          k ∈ normalizer (Z : Set G)) ∧
        J ≤ U₁ ∧ (∀ x ∈ J, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (2 ^ f) ^ 4 ≤ Nat.card J) ∨
      ∃ X : Subgroup G, R₂ ≤ X ∧ X ≤ U₁ ∧ (∀ x ∈ X, x ^ 2 = 1) ∧ (2 ^ f) ^ 4 ≤ Nat.card X ∧
        (∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂) ∧
        ∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ U₁ → (∀ y ∈ Y, y ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card Y →
          Y = X ∨ Y = X.map (MulAut.conj t).toMonoidHom

@[expose] def U3EndingNonsplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
    ∀ X : Subgroup G, R₂ ≤ X → X ≤ U₁ → (∀ x ∈ X, x ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card X →
      (∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂) →
      (∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ U₁ → (∀ y ∈ Y, y ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card Y →
        Y = X ∨ Y = X.map (MulAut.conj t).toMonoidHom) →
      v ∉ normalizer (X : Set G)

private theorem pencil_map_conj_map_conj {G : Type*} [Group G] (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem pencil_map_conj_one {G : Type*} [Group G] (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp

theorem u3EndingRadicalInput_of_pencil_of_nonsplit (hp : U3EndingPencilInput)
    (hn : U3EndingNonsplitInput) : U3EndingRadicalInput := by
  intro G _ _ L f t T R₂ U₁ s v hD hvT hv2 hvS hsv
  rcases hp G L f t T R₂ U₁ s hD with hsplit | ⟨X, hRX, hXU, hX2, hXcard, hXt, huniq⟩
  · exact hsplit
  exfalso
  refine hn G L f t T R₂ U₁ s v hD hvT hv2 hvS hsv X hRX hXU hX2 hXcard hXt huniq ?_
  have hU := hD.u1
  have hR := hD.r2
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have htR : t ∈ normalizer (R₂ : Set G) := by
    refine mem_normalizer_iff.mpr fun r => ⟨fun hr => hR.tN r hr, fun hr => ?_⟩
    have h1 := hR.tN _ hr
    have e : t * (t * r * t⁻¹) * t⁻¹ = (t * t) * r * (t * t)⁻¹ := by group
    rwa [e, htt, one_mul, inv_one, mul_one] at h1
  have key : ∀ g ∈ normalizer (U₁ : Set G), g ∈ normalizer (R₂ : Set G) →
      X.map (MulAut.conj g).toMonoidHom = X ∨
        X.map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj t).toMonoidHom := by
    intro g hgU hgR
    refine huniq _ (fun r hr => ?_) ?_ ?_ ?_
    · refine ⟨g⁻¹ * r * g, hRX ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hgR) r).mp hr
      rwa [inv_inv] at this
    · rintro _ ⟨x, hx, rfl⟩
      simpa [mul_assoc] using (mem_normalizer_iff.mp hgU x).mp (hXU hx)
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := hX2 x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [sq] at h1 ⊢
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hXcard
  have hne : X.map (MulAut.conj t).toMonoidHom ≠ X := by
    intro heq
    have hle : X ≤ R₂ := fun x hx => hXt x hx (by
      rw [← heq]
      exact ⟨x, hx, by simp⟩)
    have h1 : Nat.card X ≤ Nat.card R₂ := Subgroup.card_le_of_le hle
    rw [hR.card] at h1
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := hD.start.two_le; omega)
    have h2 : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hsU := hD.s_mem_normalizer_U₁
  have hsR := hD.s_mem_normalizer_R₂
  have hv : v = t⁻¹ * (s * (t * s⁻¹)) := by
    calc v = t⁻¹ * (t * v) := by group
      _ = t⁻¹ * (s * t * s⁻¹) := by rw [hsv]
      _ = t⁻¹ * (s * (t * s⁻¹)) := by group
  apply mem_normalizer_of_map_conj_eq
  rw [hv, ← pencil_map_conj_map_conj, ← pencil_map_conj_map_conj, ← pencil_map_conj_map_conj]
  rcases key s⁻¹ (inv_mem hsU) (inv_mem hsR) with hA | hB
  ·
    rw [hA, pencil_map_conj_map_conj X s t]
    rcases key (s * t) (mul_mem hsU htU) (mul_mem hsR htR) with h1 | h1
    · exfalso
      apply hne
      calc X.map (MulAut.conj t).toMonoidHom = X.map (MulAut.conj (s⁻¹ * (s * t))).toMonoidHom := by
            rw [inv_mul_cancel_left]
        _ = (X.map (MulAut.conj (s * t)).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom :=
            (pencil_map_conj_map_conj _ _ _).symm
        _ = X := by rw [h1, hA]
    · rw [h1, pencil_map_conj_map_conj, inv_mul_cancel, pencil_map_conj_one]
  ·
    rw [hB, pencil_map_conj_map_conj X t t, htt, pencil_map_conj_one]
    rcases key s hsU hsR with h1 | h1
    · exfalso
      apply hne
      calc X.map (MulAut.conj t).toMonoidHom = X.map (MulAut.conj s⁻¹).toMonoidHom := hB.symm
        _ = X.map (MulAut.conj (s⁻¹ * s)).toMonoidHom := by rw [← pencil_map_conj_map_conj, h1, hB]
        _ = X := by rw [inv_mul_cancel, pencil_map_conj_one]
    · rw [h1, pencil_map_conj_map_conj, inv_mul_cancel, pencil_map_conj_one]

section Certificates

theorem u3EndingInput_of_pencil_of_nonsplit (hp : U3EndingPencilInput)
    (hn : U3EndingNonsplitInput) (hsyl : U3EndingSylowInput) : U3EndingInput :=
  u3EndingInput_of_radical (u3EndingRadicalInput_of_pencil_of_nonsplit hp hn) hsyl

end Certificates

end CFSG.SeitzReduction.RankOne
