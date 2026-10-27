module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Q1Sq

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

def Tma (a : X) (W : Subgroup X) (hW : W ≤ C.E₀) : Subgroup X where
  carrier := {p | (∀ e ∈ C.E₀, p * e * p⁻¹ = e) ∧ a⁻¹ * (p * a * p⁻¹) ∈ W}
  mul_mem' := by
    rintro p q ⟨hp, hpa⟩ ⟨hq, hqa⟩
    refine ⟨fun e he => ?_, ?_⟩
    · calc p * q * e * (p * q)⁻¹ = p * (q * e * q⁻¹) * p⁻¹ := by group
        _ = e := by rw [hq e he, hp e he]
    · have h1 : p * q * a * (p * q)⁻¹ = (p * a * p⁻¹) *
          (p * (a⁻¹ * (q * a * q⁻¹)) * p⁻¹) := by group
      rw [h1, hp _ (hW hqa)]
      rw [show a⁻¹ * (p * a * p⁻¹ * (a⁻¹ * (q * a * q⁻¹))) =
        (a⁻¹ * (p * a * p⁻¹)) * (a⁻¹ * (q * a * q⁻¹)) by group]
      exact mul_mem hpa hqa
  one_mem' := by
    refine ⟨fun e _ => by group, ?_⟩
    rw [show a⁻¹ * (1 * a * 1⁻¹) = 1 by group]
    exact one_mem _
  inv_mem' := by
    rintro p ⟨hp, hpa⟩
    have hp' : ∀ e ∈ C.E₀, p⁻¹ * e * p⁻¹⁻¹ = e := fun e he => by
      calc p⁻¹ * e * p⁻¹⁻¹ = p⁻¹ * (p * e * p⁻¹) * p := by rw [hp e he, inv_inv]
        _ = e := by group
    refine ⟨hp', ?_⟩
    have h1 := hp' _ (hW hpa)
    have : a⁻¹ * (p⁻¹ * a * p⁻¹⁻¹) = (p⁻¹ * (a⁻¹ * (p * a * p⁻¹)) * p⁻¹⁻¹)⁻¹ := by group
    rw [this, h1]
    exact inv_mem hpa

theorem mem_Tma {a : X} {W : Subgroup X} {hW : W ≤ C.E₀} {p : X} :
    p ∈ C.Tma a W hW ↔ (∀ e ∈ C.E₀, p * e * p⁻¹ = e) ∧ a⁻¹ * (p * a * p⁻¹) ∈ W := Iff.rfl

theorem tma_mul {a p q : X} (hp : p ∈ C.Tma a C.E₀ le_rfl) (hq : q ∈ C.Tma a C.E₀ le_rfl) :
    a⁻¹ * (p * q * a * (p * q)⁻¹) = (a⁻¹ * (p * a * p⁻¹)) * (a⁻¹ * (q * a * q⁻¹)) := by
  have h1 : p * q * a * (p * q)⁻¹ = (p * a * p⁻¹) * (p * (a⁻¹ * (q * a * q⁻¹)) * p⁻¹) := by
    group
  rw [h1, (C.mem_Tma.mp hp).1 _ (C.mem_Tma.mp hq).2]
  group

theorem tma_inv {a p : X} (hp : p ∈ C.Tma a C.E₀ le_rfl) :
    a⁻¹ * (p⁻¹ * a * p⁻¹⁻¹) = (a⁻¹ * (p * a * p⁻¹))⁻¹ := by
  have h1 := (C.mem_Tma.mp hp).1 _ (C.mem_Tma.mp hp).2
  have h2 : ∀ e ∈ C.E₀, p⁻¹ * e * p = e := fun e he => by
    calc p⁻¹ * e * p = p⁻¹ * (p * e * p⁻¹) * p := by rw [(C.mem_Tma.mp hp).1 e he]
      _ = e := by group
  have : a⁻¹ * (p⁻¹ * a * p⁻¹⁻¹) = (p⁻¹ * (a⁻¹ * (p * a * p⁻¹)) * p)⁻¹ := by group
  rw [this, h2 _ (C.mem_Tma.mp hp).2]

theorem comm_comm_of_tma {a p q : X} (hp : p ∈ C.Tma a C.E₀ le_rfl)
    (hq : q ∈ C.Tma a C.E₀ le_rfl) : (p * q * p⁻¹ * q⁻¹) * a = a * (p * q * p⁻¹ * q⁻¹) := by
  have hpE := (C.mem_Tma.mp hp).2
  have hqE := (C.mem_Tma.mp hq).2
  have hm : a⁻¹ * (p * q * p⁻¹ * q⁻¹ * a * (p * q * p⁻¹ * q⁻¹)⁻¹) = 1 := by
    rw [show p * q * p⁻¹ * q⁻¹ = (p * q) * (p⁻¹ * q⁻¹) by group,
      C.tma_mul (mul_mem hp hq) (mul_mem (inv_mem hp) (inv_mem hq)), C.tma_mul hp hq,
      C.tma_mul (inv_mem hp) (inv_mem hq), C.tma_inv hp, C.tma_inv hq, C.comm_E0 hpE hqE]
    group
  calc p * q * p⁻¹ * q⁻¹ * a = a * (a⁻¹ * (p * q * p⁻¹ * q⁻¹ * a * (p * q * p⁻¹ * q⁻¹)⁻¹)) *
        (p * q * p⁻¹ * q⁻¹) := by group
    _ = a * (p * q * p⁻¹ * q⁻¹) := by rw [hm, mul_one]

theorem Q₁_le_Tma_t : C.D₁.Q₁ ≤ C.Tma S.t C.E₀ le_rfl := by
  rw [C.Q₁_eq]
  intro x hx
  exact C.mem_Tma.mpr (C.mem_Tm.mp (C.Q₁'_le_Tm hx))

theorem Q₁_le_Tma_v' : C.D₁.Q₁ ≤ C.Tma C.v' C.E₀ le_rfl := by
  have hE : C.E₀ ≤ C.Tma C.v' C.E₀ le_rfl := fun e he =>
    ⟨fun f hf => conj_eq_of_comm (C.comm_E0 he hf), by
      rw [conj_eq_of_comm (C.comm_v'_E0 he).symm, inv_mul_cancel]; exact one_mem _⟩
  have hv : C.v' ∈ C.Tma C.v' C.E₀ le_rfl :=
    ⟨fun e he => C.v'_E0 he, by rw [mul_inv_cancel_right, inv_mul_cancel]; exact one_mem _⟩
  have ht : S.t ∈ C.Tma C.v' C.E₀ le_rfl := by
    refine ⟨fun e he => conj_eq_of_comm (C.t_comm_E0 he), ?_⟩
    rw [C.t_v', ← C.comm_v'_E0 C.k_mem_E0, inv_mul_cancel_left]
    exact C.k_mem_E0
  have hw₁ : C.w₁' ∈ C.Tma C.v' C.E₀ le_rfl := by
    refine ⟨fun e he => C.w₁'_E0 he, ?_⟩
    rw [show C.w₁' * C.v' * C.w₁'⁻¹ = (C.w₁' * C.v' * C.w₁'⁻¹ * C.v'⁻¹) * C.v' by group,
      ← C.comm_v'_E0 C.c₁_mem, inv_mul_cancel_left]
    exact C.c₁_mem
  have hw₂ : C.D₁.w₂ ∈ C.Tma C.v' C.E₀ le_rfl := by
    refine ⟨fun e he => C.w₂_E0 he, ?_⟩
    rw [show C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ = (C.D₁.w₂ * C.v' * C.D₁.w₂⁻¹ * C.v'⁻¹) * C.v' by
      group, ← C.comm_v'_E0 C.c₂_mem, inv_mul_cancel_left]
    exact C.c₂_mem
  rw [C.Q₁_eq]
  refine sup_le (sup_le (sup_le ?_ (zpowers_le.mpr hv)) (zpowers_le.mpr hw₁))
    (zpowers_le.mpr hw₂)
  rw [C.E₁_eq]
  exact sup_le hE (zpowers_le.mpr ht)

theorem comm_mem_E0 {a b : X} (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁) :
    a * b * a⁻¹ * b⁻¹ ∈ C.E₀ := by
  have hx : a * b * a⁻¹ * b⁻¹ ∈ C.D₁.Q₁ :=
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  exact C.mem_E0_of_comm_v' (C.mem_E₁_of_comm_t hx
    (C.comm_comm_of_tma (C.Q₁_le_Tma_t ha) (C.Q₁_le_Tma_t hb)))
    (C.comm_comm_of_tma (C.Q₁_le_Tma_v' ha) (C.Q₁_le_Tma_v' hb))

omit [Finite X] in
theorem conjTo_conj {a b h : X} (hb : ConjTo a b) : ConjTo a (h * b * h⁻¹) := by
  obtain ⟨g, hg⟩ := hb
  exact ⟨h * g, by rw [← hg]; group⟩

theorem conjTo_of_mem_E₁ {b : X} (hb : b ∈ C.E₁) (hb0 : b ∉ C.E₀) : ConjTo S.t b := by
  rcases C.isRefl_y.mem_E0_or C.isK_k hb with h | h
  · exact absurd h hb0
  · have h1 := conjTo_t_mul_any C.D₁ C.isRefl_y C.isK_k h
    have hbt : b * S.t = S.t * b := C.isRefl_y.elemAbelianTwo_E.comm b hb S.t C.t_mem_E₁
    rwa [hbt, ← mul_assoc, tt S, one_mul] at h1

theorem not_conjTo_of_mem_E0 {e : X} (he : e ∈ C.E₀) : ¬ ConjTo S.t e :=
  not_conjTo_of_mem_E0_any C.D₁ C.isRefl_y C.isK_k he

theorem map_E0_eq {h : X} (hA : C.E₀ ≤ C.E₁.map (MulAut.conj h).toMonoidHom) :
    C.E₀.map (MulAut.conj h).toMonoidHom = C.E₀ := by
  have hle : C.E₀ ≤ C.E₀.map (MulAut.conj h).toMonoidHom := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := hA he
    by_cases hb0 : b ∈ C.E₀
    · exact ⟨b, hb0, rfl⟩
    · exact absurd (conjTo_conj (h := h) (C.conjTo_of_mem_E₁ hb hb0))
        (C.not_conjTo_of_mem_E0 he)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj h).injective])).symm

theorem conjTo_of_mem_map {h a : X} (hA : C.E₀ ≤ C.E₁.map (MulAut.conj h).toMonoidHom)
    (ha : a ∈ C.E₁.map (MulAut.conj h).toMonoidHom) (ha0 : a ∉ C.E₀) : ConjTo S.t a := by
  obtain ⟨b, hb, rfl⟩ := ha
  by_cases hb0 : b ∈ C.E₀
  · exact absurd (C.map_E0_eq hA ▸ ⟨b, hb0, rfl⟩) ha0
  · exact conjTo_conj (h := h) (C.conjTo_of_mem_E₁ hb hb0)

theorem v'_not_mem_E0 : C.v' ∉ C.E₀ := fun h => C.v'_not_mem_E₁ (C.E0_le_E₁ h)

theorem map_ne_Fv (h : X) : C.E₁.map (MulAut.conj h).toMonoidHom ≠ C.Fv := by
  intro hA
  have hE0 : C.E₀ ≤ C.E₁.map (MulAut.conj h).toMonoidHom := hA ▸ le_sup_left
  have hmem : C.v' * C.F.yF ∈ C.E₁.map (MulAut.conj h).toMonoidHom := by
    rw [hA]; exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left C.y_mem_E0)
  have hnot : C.v' * C.F.yF ∉ C.E₀ := fun h' => C.v'_not_mem_E0 (by
    have := mul_mem h' (inv_mem C.y_mem_E0)
    rwa [mul_inv_cancel_right] at this)
  exact C.not_conjTo_v'y (C.conjTo_of_mem_map hE0 hmem hnot)

theorem tv'_not_mem_E0 : S.t * C.v' ∉ C.E₀ := fun h => C.v'_not_mem_E₁ (by
  rw [show C.v' = S.t⁻¹ * (S.t * C.v') by group]
  exact mul_mem (inv_mem C.t_mem_E₁) (C.E0_le_E₁ h))

theorem tv'_E0 {e : X} (he : e ∈ C.E₀) : (S.t * C.v') * e * (S.t * C.v')⁻¹ = e := by
  rw [show S.t * C.v' * e * (S.t * C.v')⁻¹ = S.t * (C.v' * e * C.v'⁻¹) * S.t⁻¹ by group,
    C.v'_E0 he, conj_eq_of_comm (C.t_comm_E0 he)]

theorem map_ne_G₁ (hq : C.D₁.q0 = .e4q8) (h : X) : C.E₁.map (MulAut.conj h).toMonoidHom ≠ C.G₁ := by
  intro hA
  set g := C.F.yF * (S.t * C.v' * C.w₁') with hg
  have hc₁ : C.w₁' * C.v' * C.w₁'⁻¹ = S.z * C.v' := by
    rw [← C.comm_w₁'_v'_e4q8 hq]; group
  have hv'w : C.v' * C.w₁' * C.v'⁻¹ = S.z * C.w₁' := by
    have h1 : C.w₁' * C.v' = S.z * C.v' * C.w₁' := by rw [← hc₁]; group
    calc C.v' * C.w₁' * C.v'⁻¹ = C.v' * (C.w₁' * C.v') * (C.v'⁻¹ * C.v'⁻¹) := by group
      _ = C.v' * (S.z * C.v' * C.w₁') * (C.v'⁻¹ * C.v'⁻¹) := by rw [h1]
      _ = (C.v' * S.z) * C.v' * C.w₁' * (C.v' * C.v')⁻¹ := by group
      _ = S.z * C.w₁' := by
        rw [C.comm_v'_E0 C.z_mem_E0, mul_assoc S.z C.v' C.v', C.v'v', mul_one, inv_one,
          mul_one]
  have huw : C.D₁.u * C.w₁' * C.D₁.u⁻¹ = C.F.kF * C.w₁' := by
    have := C.u_w₁'
    calc C.D₁.u * C.w₁' * C.D₁.u⁻¹ = (C.D₁.u * C.w₁' * C.D₁.u⁻¹ * C.w₁'⁻¹) * C.w₁' := by group
      _ = C.F.kF * C.w₁' := by rw [this]
  have hut : C.D₁.u * S.t * C.D₁.u⁻¹ = S.t := conj_eq_of_comm (C.u_comm_B t_mem_B)
  have huv : C.D₁.u * C.v' * C.D₁.u⁻¹ = C.v' := conj_eq_of_comm C.u_comm_v'
  have huz : C.D₁.u * S.z * C.D₁.u⁻¹ = S.z := conj_eq_of_comm (C.u_comm_B z_mem_B)
  have huk : C.D₁.u * C.F.kF * C.D₁.u⁻¹ = C.F.kF := conj_eq_of_comm (C.u_comm_B (kF_mem_B C.F))
  set W₁ : Subgroup X := C.E₀ ⊔ zpowers (S.t * C.v') with hW₁
  set W : Subgroup X := W₁ ⊔ zpowers C.w₁' with hW
  set Q : Subgroup X := W ⊔ zpowers (C.D₁.u * C.v') with hQ
  have htv_norm : S.t * C.v' ∈ normalizer (C.E₀ : Set X) := mem_normalizer_of_map_le (by
    rintro _ ⟨e, he, rfl⟩; show S.t * C.v' * e * (S.t * C.v')⁻¹ ∈ C.E₀; rw [C.tv'_E0 he]
    exact he)
  have hcard1 : Nat.card W₁ = 16 := by
    rw [hW₁, card_sup_zpowers_eq htv_norm (by rw [C.sq_tv']; exact C.k_mem_E0)
      C.tv'_not_mem_E0, C.isRefl_y.card_E0 C.isK_k]
  have hW₁Tm : W₁ ≤ C.Tm (zpowers C.F.kF) C.kpow_le_E0 := by
    refine sup_le (C.E0_le_Tm _ _) (zpowers_le.mpr (C.mem_Tm.mpr ⟨fun e he => C.tv'_E0 he, ?_⟩))
    have htk : S.t * (S.t * C.F.kF) * S.t⁻¹ = S.t * C.F.kF :=
      conj_eq_of_comm (C.isRefl_y.elemAbelianTwo_E.comm _ C.t_mem_E₁ _
        (mul_mem C.t_mem_E₁ (C.E0_le_E₁ C.k_mem_E0)))
    rw [show S.t * C.v' * S.t * (S.t * C.v')⁻¹ = S.t * (C.v' * S.t * C.v'⁻¹) * S.t⁻¹ by group,
      C.v'_t, htk, inv_mul_cancel_left]
    exact mem_zpowers _
  have hw_not : C.w₁' ∉ W₁ := by
    intro h'
    have := (C.mem_Tm.mp (hW₁Tm h')).2
    rw [C.w₁'_t, inv_mul_cancel_left] at this
    rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq this with h1 | h1
    · exact S.z_ne_one h1
    · exact C.k_not_mem_zpowers_z (h1 ▸ mem_zpowers _)
  have hw_norm : C.w₁' ∈ normalizer (W₁ : Set X) := mem_normalizer_of_map_le
    (map_conj_sup_le (fun e he => by rw [C.w₁'_E0 he]; exact mem_sup_left he)
      (conj_zpowers_mem (by
        rw [conj_mul_eq, C.w₁'_t, hc₁, show S.t * S.z * (S.z * C.v') = S.t * C.v' by
          rw [mul_assoc S.t, ← mul_assoc S.z, zz S, one_mul]]
        exact mem_sup_right (mem_zpowers _))))
  have hcard2 : Nat.card W = 32 := by
    rw [hW, card_sup_zpowers_eq hw_norm (mem_sup_left C.w₁'_sq_mem_E0) hw_not, hcard1]
  have hWQ₁ : W ≤ C.D₁.Q₁ :=
    sup_le (sup_le C.E0_le_Q₁ (zpowers_le.mpr (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁)))
      (zpowers_le.mpr C.w₁'_mem_Q₁)
  have huv_not : C.D₁.u * C.v' ∉ W := fun h' => u_not_mem_Q₁ C.isRefl_y C.D₁ (by
    rw [show C.D₁.u = C.D₁.u * C.v' * C.v'⁻¹ by group]
    exact mul_mem (hWQ₁ h') (inv_mem C.v'_mem_Q₁))
  have huv_sq : (C.D₁.u * C.v') ^ 2 ∈ W := by
    rw [pow_two, show C.D₁.u * C.v' * (C.D₁.u * C.v') = C.D₁.u * (C.v' * C.D₁.u) * C.v' by
      group, ← C.u_comm_v', show C.D₁.u * (C.D₁.u * C.v') * C.v' =
        (C.D₁.u * C.D₁.u) * (C.v' * C.v') by group, C.u_mul_u, C.v'v', one_mul]
    exact one_mem _
  have huv_norm : C.D₁.u * C.v' ∈ normalizer (W : Set X) := by
    have hv'W : C.v' ∈ normalizer (W : Set X) := mem_normalizer_of_map_le
      (map_conj_sup_le (fun a ha => ?_) (conj_zpowers_mem ?_))
    · have huW : C.D₁.u ∈ normalizer (W : Set X) := mem_normalizer_of_map_le
        (map_conj_sup_le (fun a ha => ?_) (conj_zpowers_mem ?_))
      · exact mul_mem huW hv'W
      · have hle : W₁.map (MulAut.conj C.D₁.u).toMonoidHom ≤ W :=
          map_conj_sup_le (fun e he => mem_sup_left (mem_sup_left (C.u_conj_E0 he)))
            (conj_zpowers_mem (by
              rw [conj_mul_eq, hut, huv]; exact mem_sup_left (mem_sup_right (mem_zpowers _))))
        exact hle ⟨a, ha, rfl⟩
      · rw [huw]; exact mul_mem (mem_sup_left (mem_sup_left C.k_mem_E0)) (mem_sup_right
          (mem_zpowers _))
    · have hle : W₁.map (MulAut.conj C.v').toMonoidHom ≤ W :=
        map_conj_sup_le (fun e he => by rw [C.v'_E0 he]; exact mem_sup_left (mem_sup_left he))
          (conj_zpowers_mem (by
            rw [show C.v' * (S.t * C.v') * C.v'⁻¹ = (C.v' * S.t * C.v'⁻¹) * C.v' by group,
              C.v'_t, mul_assoc, ← C.comm_v'_E0 C.k_mem_E0, ← mul_assoc]
            exact mul_mem (mem_sup_left (mem_sup_right (mem_zpowers _)))
              (mem_sup_left (mem_sup_left C.k_mem_E0))))
      exact hle ⟨a, ha, rfl⟩
    · rw [hv'w]; exact mul_mem (mem_sup_left (mem_sup_left C.z_mem_E0)) (mem_sup_right
        (mem_zpowers _))
  have hcard3 : Nat.card Q = 64 := by
    rw [hQ, card_sup_zpowers_eq huv_norm huv_sq huv_not, hcard2]
  set r := S.t * C.v' * C.w₁' with hr
  have hrQ : r ∈ C.D₁.Q₁ := mul_mem (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₁'_mem_Q₁
  have hcomm : ∀ {e : X}, e ∈ C.E₀ → e * r = r * e := fun he => C.comm_E0_Q₁ he hrQ
  have htw : S.t * C.w₁' * S.t⁻¹ = S.z * C.w₁' := by
    have h1 : C.w₁'⁻¹ * S.t * C.w₁' = S.t * S.z :=
      conj_inv_eq_of C.w₁'_t (C.w₁'_E0 C.z_mem_E0) (zz S)
    calc S.t * C.w₁' * S.t⁻¹ = C.w₁' * (C.w₁'⁻¹ * S.t * C.w₁') * S.t⁻¹ := by group
      _ = C.w₁' * (S.t * S.z * S.t⁻¹) := by rw [h1]; group
      _ = S.z * C.w₁' := by
        rw [conj_eq_of_comm (C.t_comm_E0 C.z_mem_E0), ← C.w₁'_comm_E0 C.z_mem_E0]
  have htk : S.t * (S.t * C.F.kF) * S.t⁻¹ = S.t * C.F.kF :=
    conj_eq_of_comm (C.isRefl_y.elemAbelianTwo_E.comm _ C.t_mem_E₁ _
      (mul_mem C.t_mem_E₁ (C.E0_le_E₁ C.k_mem_E0)))
  have hzt : S.z * S.t = S.t * S.z := (C.t_comm_E0 C.z_mem_E0).symm
  have hkt : C.F.kF * S.t = S.t * C.F.kF := (C.t_comm_E0 C.k_mem_E0).symm
  have hzv : S.z * C.v' = C.v' * S.z := (C.comm_v'_E0 C.z_mem_E0).symm
  have hkv : C.F.kF * C.v' = C.v' * C.F.kF := (C.comm_v'_E0 C.k_mem_E0).symm
  have hr_w : C.w₁' * r * C.w₁'⁻¹ = r := by
    rw [hr, conj_mul_eq, conj_mul_eq, C.w₁'_t, hc₁, mul_inv_cancel_right]
    rw [show S.t * S.z * (S.z * C.v') = S.t * C.v' by
      rw [mul_assoc S.t, ← mul_assoc S.z, zz S, one_mul]]
  have hr_tv : (S.t * C.v') * r * (S.t * C.v')⁻¹ = r := by
    have e1 : (S.t * C.v') * S.t * (S.t * C.v')⁻¹ = S.t * C.F.kF := by
      rw [show S.t * C.v' * S.t * (S.t * C.v')⁻¹ = S.t * (C.v' * S.t * C.v'⁻¹) * S.t⁻¹ by group,
        C.v'_t, htk]
    have e2 : (S.t * C.v') * C.v' * (S.t * C.v')⁻¹ = C.F.kF * C.v' := by
      rw [show S.t * C.v' * C.v' * (S.t * C.v')⁻¹ = S.t * C.v' * S.t⁻¹ by group, C.t_v']
    have e3 : (S.t * C.v') * C.w₁' * (S.t * C.v')⁻¹ = C.w₁' := by
      rw [show S.t * C.v' * C.w₁' * (S.t * C.v')⁻¹ = S.t * (C.v' * C.w₁' * C.v'⁻¹) * S.t⁻¹ by
        group, hv'w, conj_mul_eq, conj_eq_of_comm (C.t_comm_E0 C.z_mem_E0), htw, ← mul_assoc,
        zz S, one_mul]
    rw [hr, conj_mul_eq, conj_mul_eq, e1, e2, e3]
    rw [show S.t * C.F.kF * (C.F.kF * C.v') = S.t * (C.F.kF * C.F.kF) * C.v' by group, C.kk,
      mul_one]
  have hr_v : C.v' * r * C.v'⁻¹ = r * (C.F.kF * S.z) := by
    rw [hr, conj_mul_eq, conj_mul_eq, C.v'_t, mul_inv_cancel_right, hv'w]
    calc S.t * C.F.kF * C.v' * (S.z * C.w₁') = S.t * (C.F.kF * C.v') * (S.z * C.w₁') := by group
      _ = S.t * C.v' * (C.F.kF * (S.z * C.w₁')) := by rw [hkv]; group
      _ = S.t * C.v' * (C.w₁' * (C.F.kF * S.z)) := by
        rw [show C.F.kF * (S.z * C.w₁') = (C.F.kF * S.z) * C.w₁' by group,
          ← C.w₁'_comm_E0 (mul_mem C.k_mem_E0 C.z_mem_E0)]
      _ = S.t * C.v' * C.w₁' * (C.F.kF * S.z) := by group
  have hr_u : C.D₁.u * r * C.D₁.u⁻¹ = r * C.F.kF := by
    rw [hr, conj_mul_eq, conj_mul_eq, hut, huv, huw]
    rw [show S.t * C.v' * (C.F.kF * C.w₁') = S.t * C.v' * C.F.kF * C.w₁' by group,
      mul_assoc (S.t * C.v'), C.w₁'_comm_E0 C.k_mem_E0 |>.symm, ← mul_assoc]
  have hgy : g = C.F.yF * r := rfl
  have hQC : Q ≤ centralizer ({g} : Set X) := by
    have hc : ∀ a : X, a * g * a⁻¹ = g → a ∈ centralizer ({g} : Set X) := fun a ha => by
      rw [mem_centralizer_singleton_iff]
      calc a * g = a * g * a⁻¹ * a := by group
        _ = g * a := by rw [ha]
    refine sup_le (sup_le (sup_le (fun e he => hc e ?_) (zpowers_le.mpr (hc _ ?_)))
      (zpowers_le.mpr (hc _ ?_))) (zpowers_le.mpr (hc _ ?_))
    · exact conj_eq_of_comm (C.comm_E0_Q₁ he (mul_mem (C.E0_le_Q₁ C.y_mem_E0) hrQ))
    · rw [hgy, conj_mul_eq, C.tv'_E0 C.y_mem_E0, hr_tv]
    · rw [hgy, conj_mul_eq, C.w₁'_E0 C.y_mem_E0, hr_w]
    · rw [hgy, show C.D₁.u * C.v' * (C.F.yF * r) * (C.D₁.u * C.v')⁻¹ =
        C.D₁.u * ((C.v' * C.F.yF * C.v'⁻¹) * (C.v' * r * C.v'⁻¹)) * C.D₁.u⁻¹ by group,
        C.v'_E0 C.y_mem_E0, hr_v, conj_mul_eq, C.u_y, conj_mul_eq, hr_u, conj_mul_eq, huk, huz]
      rw [mul_assoc r C.F.kF, ← mul_assoc C.F.kF C.F.kF S.z, C.kk, one_mul,
        ← hcomm C.z_mem_E0, ← C.yz, mul_assoc C.F.yF, ← mul_assoc S.z S.z, zz S, one_mul]
  have hQ2 : IsPGroup 2 Q := by
    refine C.D₁.isPGroup_S₁.to_le (sup_le ((hWQ₁.trans ?_)) (zpowers_le.mpr ?_))
    · rw [C.D₁.Q₁_eq]; exact inf_le_left
    · have huS : C.D₁.u ∈ C.D₁.S₁ := by rw [C.D₁.S₁_eq]; exact mem_sup_right (mem_zpowers _)
      have hvS : C.v' ∈ C.D₁.S₁ := by
        have := C.v'_mem_Q₁
        rw [C.D₁.Q₁_eq] at this
        exact this.1
      exact mul_mem huS hvS
  have hgA : g ∈ C.E₁.map (MulAut.conj h).toMonoidHom := by
    rw [hA]; exact mul_mem (mem_sup_left C.y_mem_E0) (mem_sup_right (mem_zpowers _))
  have hr0 : r ∉ C.E₀ := by
    intro h'
    have h1 : r * S.t * r⁻¹ = S.t := conj_eq_of_comm (C.t_comm_E0 h').symm
    have i1 : C.v' * (S.t * S.z) * C.v'⁻¹ = S.t * C.F.kF * S.z := by
      rw [conj_mul_eq, C.v'_t, C.v'_E0 C.z_mem_E0]
    have i2 : S.t * (S.t * C.F.kF * S.z) * S.t⁻¹ = S.t * (C.F.kF * S.z) := by
      rw [conj_eq_of_comm (C.isRefl_y.elemAbelianTwo_E.comm _ C.t_mem_E₁ _
        (mul_mem (mul_mem C.t_mem_E₁ (C.E0_le_E₁ C.k_mem_E0)) (C.E0_le_E₁ C.z_mem_E0))),
        mul_assoc]
    have h2 : r * S.t * r⁻¹ = S.t * (C.F.kF * S.z) := by
      calc r * S.t * r⁻¹ = S.t * (C.v' * (C.w₁' * S.t * C.w₁'⁻¹) * C.v'⁻¹) * S.t⁻¹ := by
            rw [hr]; group
        _ = S.t * (S.t * C.F.kF * S.z) * S.t⁻¹ := by rw [C.w₁'_t, i1]
        _ = S.t * (C.F.kF * S.z) := i2
    rw [h1] at h2
    have : C.F.kF * S.z = 1 := by simpa using h2.symm
    exact C.k_not_mem_zpowers_z (by
      rw [eq_inv_of_mul_eq_one_left this]; exact inv_mem (mem_zpowers _))
  have hg0 : g ∉ C.E₀ := fun h' => hr0 (by
    have := mul_mem (inv_mem C.y_mem_E0) h'
    rwa [hgy, inv_mul_cancel_left] at this)
  exact not_conjTo_of_card hQ2 hQC (by rw [hcard3]; norm_num)
    (C.conjTo_of_mem_map (hA ▸ le_sup_left) hgA hg0)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
