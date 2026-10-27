module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Stroth77.Section47Core

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))

theorem prod4_mem {H' : Subgroup G} {x₁ x₂ y₃ y₄ : G} (hx₁ : x₁ ∈ H') (hx₂ : x₂ ∈ H')
    (hy₃ : y₃ ∈ H') (hy₄ : y₄ ∈ H') (w : (Bool × Bool) × (Bool × Bool)) :
    prod4 x₁ x₂ y₃ y₄ w ∈ H' := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
  simp only [prod4]
  refine mul_mem (mul_mem ?_ ?_) (mul_mem ?_ ?_)
  · cases a <;> simp [bpow, hx₁]
  · cases b <;> simp [bpow, hx₂]
  · cases c <;> simp [bpow, hy₃]
  · cases d <;> simp [bpow, hy₄]

theorem elab16_prod4_inj {H : Subgroup G} {x₁ x₂ y₃ y₄ : G}
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : y₃ * y₃ = 1) (h₄ : y₄ * y₄ = 1)
    (h₁₂ : x₁ * x₂ = x₂ * x₁) (h₁₃ : x₁ * y₃ = y₃ * x₁) (h₁₄ : x₁ * y₄ = y₄ * x₁)
    (h₂₃ : x₂ * y₃ = y₃ * x₂) (h₂₄ : x₂ * y₄ = y₄ * x₂) (h₃₄ : y₃ * y₄ = y₄ * y₃)
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H) (hx₁1 : x₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hx₁₂ : x₁ ≠ x₂)
    (hy₃ : y₃ ∉ H) (hy₄ : y₄ ∉ H) (hy₃₄ : y₃ * y₄ ∉ H) :
    Function.Injective (prod4 x₁ x₂ y₃ y₄) := by
  have hmul := prod4_mul_prod4 h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  have hsq : ∀ w, prod4 x₁ x₂ y₃ y₄ w * prod4 x₁ x₂ y₃ y₄ w = 1 := fun w => by
    rw [hmul, xor4_self, prod4_zero]
  have hind : ∀ w, prod4 x₁ x₂ y₃ y₄ w = 1 → w = ((false, false), (false, false)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [prod4] at h
    have hPH : bpow x₁ a * bpow x₂ b ∈ H := by
      cases a <;> cases b <;> simp [bpow, hx₁, hx₂, mul_mem]
    have hQ : bpow y₃ c * bpow y₄ d ∈ H := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact H.inv_mem hPH
    have hcd : c = false ∧ d = false := by
      cases c <;> cases d
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [bpow] using hQ) hy₄
      · exact absurd (by simpa [bpow] using hQ) hy₃
      · exact absurd (by simpa [bpow] using hQ) hy₃₄
    obtain ⟨rfl, rfl⟩ := hcd
    have h' : bpow x₁ a * bpow x₂ b = 1 := by simpa [bpow] using h
    have hab : a = false ∧ b = false := by
      cases a <;> cases b
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [bpow] using h') hx₂1
      · exact absurd (by simpa [bpow] using h') hx₁1
      · have h12 : x₁ * x₂ = 1 := by simpa [bpow] using h'
        exact absurd ((eq_inv_of_mul_eq_one_left h12).trans (inv_eq_of_mul_eq_one_right h₂))
          hx₁₂
    obtain ⟨rfl, rfl⟩ := hab
    rfl
  intro w w' h
  have h1' : prod4 x₁ x₂ y₃ y₄ (xor4 w w') = 1 := by rw [← hmul, h, hsq]
  have h2' := hind _ h1'
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := w'
  simp only [xor4, Prod.mk.injEq] at h2'
  obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := h2'
  revert ha hb hc hd
  cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> cases d <;>
    cases d' <;> decide

theorem elab16_closure [Finite G] {H : Subgroup G} {x₁ x₂ y₃ y₄ : G}
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : y₃ * y₃ = 1) (h₄ : y₄ * y₄ = 1)
    (h₁₂ : x₁ * x₂ = x₂ * x₁) (h₁₃ : x₁ * y₃ = y₃ * x₁) (h₁₄ : x₁ * y₄ = y₄ * x₁)
    (h₂₃ : x₂ * y₃ = y₃ * x₂) (h₂₄ : x₂ * y₄ = y₄ * x₂) (h₃₄ : y₃ * y₄ = y₄ * y₃)
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H) (hx₁1 : x₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hx₁₂ : x₁ ≠ x₂)
    (hy₃ : y₃ ∉ H) (hy₄ : y₄ ∉ H) (hy₃₄ : y₃ * y₄ ∉ H) :
    (∀ x ∈ Subgroup.closure {x₁, x₂, y₃, y₄}, x * x = 1) ∧
      Nat.card (Subgroup.closure {x₁, x₂, y₃, y₄}) = 16 := by
  have hmul := prod4_mul_prod4 h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  have hsq : ∀ w, prod4 x₁ x₂ y₃ y₄ w * prod4 x₁ x₂ y₃ y₄ w = 1 := fun w => by
    rw [hmul, xor4_self, prod4_zero]
  have hinj := elab16_prod4_inj h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hx₁ hx₂ hx₁1 hx₂1 hx₁₂
    hy₃ hy₄ hy₃₄
  let E : Subgroup G :=
    { carrier := Set.range (prod4 x₁ x₂ y₃ y₄)
      mul_mem' := by
        rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
        exact ⟨_, (hmul w w').symm⟩
      one_mem' := ⟨_, prod4_zero x₁ x₂ y₃ y₄⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨w, (inv_eq_of_mul_eq_one_right (hsq w)).symm⟩ }
  have hclosure_eq : Subgroup.closure ({x₁, x₂, y₃, y₄} : Set G) = E := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨((true, false), (false, false)), by simp [prod4, bpow]⟩
      · exact ⟨((false, true), (false, false)), by simp [prod4, bpow]⟩
      · exact ⟨((false, false), (true, false)), by simp [prod4, bpow]⟩
      · exact ⟨((false, false), (false, true)), by simp [prod4, bpow]⟩
    · rintro z ⟨w, rfl⟩
      exact prod4_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) w
  constructor
  · intro x hx
    rw [hclosure_eq] at hx
    rcases hx with ⟨w, rfl⟩
    exact hsq w
  · rw [hclosure_eq]
    change Nat.card (Set.range (prod4 x₁ x₂ y₃ y₄)) = 16
    rw [Nat.card_range_of_injective hinj]
    simp

theorem t200_a₁_comm_d8_uv (hm : 1 ≤ m) (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus (om200 m ![0, 1, 0]) * (dD.ofTorus v * dD.d8 true false false) =
      dD.ofTorus v * dD.d8 true false false * dD.ofTorus (om200 m ![0, 1, 0]) := by
  refine dD.t200_om_comm ?_
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φuv_om hm]
  exact (om200_eq_iff hm _ _).mpr (by decide)

theorem t200_b₁_comm_d8_uv (hm : 1 ≤ m) (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus (om200 m ![0, 0, 1]) * (dD.ofTorus v * dD.d8 true false false) =
      dD.ofTorus v * dD.d8 true false false * dD.ofTorus (om200 m ![0, 0, 1]) := by
  refine dD.t200_om_comm ?_
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φuv_om hm]
  exact (om200_eq_iff hm _ _).mpr (by decide)

theorem t200_a₁_comm_d8_t (hm : 1 ≤ m) (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus (om200 m ![0, 1, 0]) * (dD.ofTorus v * dD.d8 false true false) =
      dD.ofTorus v * dD.d8 false true false * dD.ofTorus (om200 m ![0, 1, 0]) := by
  refine dD.t200_om_comm ?_
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φt_om hm]
  exact (om200_eq_iff hm _ _).mpr (by decide)

theorem t200_b₁_comm_d8_t (hm : 1 ≤ m) (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.ofTorus (om200 m ![0, 0, 1]) * (dD.ofTorus v * dD.d8 false true false) =
      dD.ofTorus v * dD.d8 false true false * dD.ofTorus (om200 m ![0, 0, 1]) := by
  refine dD.t200_om_comm ?_
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_φt_om hm]
  exact (om200_eq_iff hm _ _).mpr (by decide)

theorem t200_a₁b₁_facts (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) ∈ D ∧ (dD.b : G) ^ 2 ^ (m + 1) ∈ D ∧
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) = 1 ∧
      (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) =
        (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 ∧ (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
  have hx₁D : (dD.a : G) ^ 2 ^ (m + 1) ∈ D := by
    rw [dD.t200_a_pow]
    exact dD.ofTorus_mem _
  have hx₂D : (dD.b : G) ^ 2 ^ (m + 1) ∈ D := by
    rw [dD.t200_b_pow]
    exact dD.ofTorus_mem _
  have h₁ : (dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) = 1 := by
    rw [dD.t200_a_pow, dD.ofTorus_mul_self, om200_add_self hm, dD.ofTorus_zero]
  have h₂ : (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 := by
    rw [dD.t200_b_pow, dD.ofTorus_mul_self, om200_add_self hm, dD.ofTorus_zero]
  have h₁₂ : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) =
      (dD.b : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_a_pow, dD.t200_b_pow]
    exact dD.ofTorus_comm _ _
  have hx₁1 : (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 := by
    rw [dD.t200_a_pow, Ne, dD.ofTorus_eq_one_iff, ← om200_zero, om200_eq_iff hm]
    decide
  have hx₂1 : (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 := by
    rw [dD.t200_b_pow, Ne, dD.ofTorus_eq_one_iff, ← om200_zero, om200_eq_iff hm]
    decide
  have hx₁₂ : (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
    intro h
    rw [dD.t200_a_pow, dD.t200_b_pow, dD.ofTorus_inj.eq_iff, om200_eq_iff hm] at h
    exact absurd (h 1) (by decide)
  exact ⟨hx₁D, hx₂D, h₁, h₂, h₁₂, hx₁1, hx₂1, hx₁₂⟩

theorem t200_elab16 [Finite G] (hm : 1 ≤ m) {y₃ y₄ : G} (hy₃ : y₃ * dD.uv ∈ D)
    (hy₄ : y₄ * dD.t ∈ D) (h₃ : y₃ * y₃ = 1) (h₄ : y₄ * y₄ = 1) (h₃₄ : y₃ * y₄ = y₄ * y₃) :
    (∀ x ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), y₃, y₄},
        x * x = 1) ∧
      Nat.card (Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), y₃, y₄}) =
        16 := by
  obtain ⟨v₃, hv₃⟩ := dD.exists_ofTorus hy₃
  obtain ⟨v₄, hv₄⟩ := dD.exists_ofTorus hy₄
  have hy₃eq : y₃ = dD.ofTorus v₃ * dD.d8 true false false := by
    rw [dD.d8_tff, ← hv₃, mul_assoc, dD.uv_sq, mul_one]
  have hy₄eq : y₄ = dD.ofTorus v₄ * dD.d8 false true false := by
    rw [dD.d8_ftf, ← hv₄, mul_assoc, dD.t_sq, mul_one]
  obtain ⟨hx₁D, hx₂D, h₁, h₂, h₁₂, hx₁1, hx₂1, hx₁₂⟩ := t200_a₁b₁_facts dD hm
  have h₁₃ : (dD.a : G) ^ 2 ^ (m + 1) * y₃ = y₃ * (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_a_pow, hy₃eq]
    exact t200_a₁_comm_d8_uv dD hm v₃
  have h₁₄ : (dD.a : G) ^ 2 ^ (m + 1) * y₄ = y₄ * (dD.a : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_a_pow, hy₄eq]
    exact t200_a₁_comm_d8_t dD hm v₄
  have h₂₃ : (dD.b : G) ^ 2 ^ (m + 1) * y₃ = y₃ * (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_b_pow, hy₃eq]
    exact t200_b₁_comm_d8_uv dD hm v₃
  have h₂₄ : (dD.b : G) ^ 2 ^ (m + 1) * y₄ = y₄ * (dD.b : G) ^ 2 ^ (m + 1) := by
    rw [dD.t200_b_pow, hy₄eq]
    exact t200_b₁_comm_d8_t dD hm v₄
  have hy₃D : y₃ ∉ D := by
    rw [hy₃eq]
    exact dD.d8_not_mem (t200_faithful hm) (by decide) _
  have hy₄D : y₄ ∉ D := by
    rw [hy₄eq]
    exact dD.d8_not_mem (t200_faithful hm) (by decide) _
  have hy₃₄D : y₃ * y₄ ∉ D := by
    rw [hy₃eq, hy₄eq, dD.nf_mul_nf]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    exact dD.d8_not_mem (t200_faithful hm) (by decide) _
  exact elab16_closure h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hx₁D hx₂D hx₁1 hx₂1 hx₁₂
    hy₃D hy₄D hy₃₄D

theorem t200_yF_facts :
    dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv * dD.uv ∈ D ∧
      dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t * dD.t ∈ D ∧
      dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv *
          (dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv) = 1 ∧
      dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t *
          (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t) = 1 ∧
      dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv *
          (dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t) =
        dD.ofTorus (Torus.ofInt _ ![0, 2 ^ m - 1, 0]) * dD.t *
          (dD.ofTorus (Torus.ofInt _ ![1, 1 - 2 ^ m, 1 - 2 ^ m]) * dD.uv) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, dD.uv_sq, mul_one]
    exact dD.ofTorus_mem _
  · rw [mul_assoc, dD.t_sq, mul_one]
    exact dD.ofTorus_mem _
  · rw [← dD.d8_tff, dD.nf_mul_self, Bool.false_and, dD.d8_fff, mul_one,
      dD.ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_vec, t200_add_vec]
    rw [t200_ofInt_eq_zero_iff]
    refine ⟨⟨-2, by simp; ring⟩, ⟨-1, by simp [pow_add]; ring⟩,
      ⟨-1, by simp [pow_add]; ring⟩⟩
  · rw [← dD.d8_ftf, dD.nf_mul_self, Bool.false_and, dD.d8_fff, mul_one,
      dD.ofTorus_eq_one_iff]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φt_vec, t200_add_vec]
    rw [t200_ofInt_eq_zero_iff]
    refine ⟨⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩⟩
  · rw [← dD.d8_tff, ← dD.d8_ftf, dD.nf_mul_nf, dD.nf_mul_nf]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    congr 1
    rw [t200_φuv_vec, t200_φt_vec, t200_add_vec, t200_add_vec]
    congr 1
    rw [t200_ofInt_eq_iff]
    refine ⟨⟨0, by simp⟩, ⟨1, by simp [pow_add]; ring⟩, ⟨0, by simp; ring⟩⟩

theorem t200_closure_le_S₁ {y₃ y₄ : G} (hy₃ : y₃ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (hy₄ : y₄ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) :
    Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), y₃, y₄} ≤
      D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [dD.t200_a_pow]
    exact Subgroup.mem_sup_left (dD.ofTorus_mem _)
  · rw [dD.t200_b_pow]
    exact Subgroup.mem_sup_left (dD.ofTorus_mem _)
  · exact hy₃
  · exact hy₄

end Stroth47Core

end CFSG.CGT.Stroth77
