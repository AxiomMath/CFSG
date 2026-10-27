module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Orbit
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Omega
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Syl

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

def alpha (S : A7Base X) (x : X) : X := S.t⁻¹ * (x * S.t * x⁻¹)

theorem alpha_def (S : A7Base X) (x : X) : alpha S x = S.t⁻¹ * (x * S.t * x⁻¹) := by
  unfold alpha; rfl

theorem alpha_t (S : A7Base X) : alpha S S.t = 1 := by
  rw [alpha, mul_inv_cancel_right, inv_mul_cancel]

theorem alpha_conj (S : A7Base X) {g x : X} (hg : g * S.t * g⁻¹ = S.t) :
    alpha S (g * x * g⁻¹) = g * alpha S x * g⁻¹ := by
  have hg' : g⁻¹ * S.t * g = S.t := by
    calc g⁻¹ * S.t * g = g⁻¹ * (g * S.t * g⁻¹) * g := by rw [hg]
      _ = S.t := by group
  unfold alpha
  calc S.t⁻¹ * (g * x * g⁻¹ * S.t * (g * x * g⁻¹)⁻¹) =
        S.t⁻¹ * (g * x * (g⁻¹ * S.t * g) * x⁻¹ * g⁻¹) := by group
    _ = g * (S.t⁻¹ * (x * S.t * x⁻¹)) * g⁻¹ := by
      rw [hg']
      calc S.t⁻¹ * (g * x * S.t * x⁻¹ * g⁻¹) = (g * S.t * g⁻¹)⁻¹ * (g * x * S.t * x⁻¹ * g⁻¹) := by
            rw [hg]
        _ = g * (S.t⁻¹ * (x * S.t * x⁻¹)) * g⁻¹ := by group

omit [Finite X] in
theorem conj_sq_one {n x : X} (hx : x ^ 2 = 1) : (n * x * n⁻¹) ^ 2 = 1 := by
  rw [pow_two, show n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ by group, ← pow_two, hx]
  group

omit [Finite X] in
theorem map_conj_inj {δ : X} {A B : Subgroup X}
    (h : A.map (MulAut.conj δ).toMonoidHom = B.map (MulAut.conj δ).toMonoidHom) : A = B :=
  Subgroup.map_injective (MulAut.conj δ).injective h

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem alpha_mul {x y : X} (hx : x ∈ C.D₁.Q₁) (hy : y ∈ C.D₁.Q₁) :
    alpha S (x * y) = alpha S x * alpha S y :=
  C.tma_mul (C.Q₁_le_Tma_t hx) (C.Q₁_le_Tma_t hy)

theorem alpha_inv {x : X} (hx : x ∈ C.D₁.Q₁) : alpha S x⁻¹ = (alpha S x)⁻¹ :=
  C.tma_inv (C.Q₁_le_Tma_t hx)

theorem alpha_mem {x : X} (hx : x ∈ C.D₁.Q₁) : alpha S x ∈ C.E₀ :=
  (C.mem_Tma.mp (C.Q₁_le_Tma_t hx)).2

theorem alpha_of_mem_E0 {e : X} (he : e ∈ C.E₀) : alpha S e = 1 := by
  rw [alpha, conj_eq_of_comm (C.t_comm_E0 he).symm, inv_mul_cancel]

theorem alpha_v' : alpha S C.v' = C.F.kF := by rw [alpha, C.v'_t, inv_mul_cancel_left]

theorem alpha_w₁' : alpha S C.w₁' = S.z := by rw [alpha, C.w₁'_t, inv_mul_cancel_left]

theorem alpha_w₂ : alpha S C.D₁.w₂ = C.F.yF := by rw [alpha, C.w₂_t, inv_mul_cancel_left]

theorem alpha_eq_of_coset {a b : X} (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁)
    (h : a * b⁻¹ ∈ C.E₀) : alpha S a = alpha S b := by
  have h1 := C.alpha_mul (mul_mem ha (inv_mem hb)) hb
  rw [inv_mul_cancel_right, C.alpha_of_mem_E0 h, one_mul] at h1
  exact h1

theorem alpha_eq_of_sup_eq {a b : X} (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁) (ha0 : a ∉ C.E₀)
    (hb2 : b ^ 2 ∈ C.E₀) (h : C.E₀ ⊔ zpowers a = C.E₀ ⊔ zpowers b) :
    alpha S a = alpha S b := by
  have hbN : b ∈ normalizer (C.E₀ : Set X) := mem_normalizer_of_map_le (by
    rintro _ ⟨e, he, rfl⟩
    show b * e * b⁻¹ ∈ C.E₀
    rw [C.conj_eq_of_mem_Q₁ hb he]; exact he)
  have haS : a ∈ C.E₀ ⊔ zpowers b := h ▸ mem_sup_right (mem_zpowers a)
  rcases mem_or_of_mem_sup_zpowers hbN hb2 haS with h1 | h1
  · exact absurd h1 ha0
  · exact C.alpha_eq_of_coset ha hb h1

theorem alpha_r₁ : alpha S (S.t * C.v' * C.w₁') = C.F.kF * S.z := by
  rw [C.alpha_mul (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₁'_mem_Q₁,
    C.alpha_mul C.t_mem_Q₁ C.v'_mem_Q₁, alpha_t S, C.alpha_v', C.alpha_w₁', one_mul]

theorem alpha_r₂ : alpha S (S.t * C.v' * C.D₁.w₂) = C.F.kF * C.F.yF := by
  rw [C.alpha_mul (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₂_mem_Q₁,
    C.alpha_mul C.t_mem_Q₁ C.v'_mem_Q₁, alpha_t S, C.alpha_v', C.alpha_w₂, one_mul]

theorem alpha_r₃ : alpha S (S.t * C.v' * C.w₁' * C.D₁.w₂) = C.F.kF * S.z * C.F.yF := by
  rw [C.alpha_mul (mul_mem (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₁'_mem_Q₁) C.w₂_mem_Q₁,
    C.alpha_r₁, C.alpha_w₂]

theorem r₁_mem : S.t * C.v' * C.w₁' ∈ C.D₁.Q₁ :=
  mul_mem (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₁'_mem_Q₁

theorem r₂_mem : S.t * C.v' * C.D₁.w₂ ∈ C.D₁.Q₁ :=
  mul_mem (mul_mem C.t_mem_Q₁ C.v'_mem_Q₁) C.w₂_mem_Q₁

theorem r₃_mem : S.t * C.v' * C.w₁' * C.D₁.w₂ ∈ C.D₁.Q₁ := mul_mem C.r₁_mem C.w₂_mem_Q₁

theorem not_mem_E0_of_alpha {x : X} (h : alpha S x ≠ 1) : x ∉ C.E₀ := fun hx =>
  h (C.alpha_of_mem_E0 hx)

theorem sq_t_mul_eq {m : X} (hm : m ∈ C.D₁.Q₁) :
    (S.t * m) ^ 2 = alpha S m * m ^ 2 := by
  rw [C.sq_t_mul hm]
  congr 1
  have h1 : S.t * alpha S m = alpha S m * S.t := C.t_comm_E0 (C.alpha_mem hm)
  unfold alpha at h1 ⊢
  calc m * S.t * m⁻¹ * S.t⁻¹ = S.t * (S.t⁻¹ * (m * S.t * m⁻¹)) * S.t⁻¹ := by group
    _ = S.t⁻¹ * (m * S.t * m⁻¹) := by rw [h1, mul_inv_cancel_right]

theorem r₁_sq : (S.t * C.v' * C.w₁') ^ 2 = 1 := by
  rw [mul_assoc, C.sq_t_mul_eq (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁),
    C.alpha_mul C.v'_mem_Q₁ C.w₁'_mem_Q₁, C.alpha_v', C.alpha_w₁', C.sq_v'w₁',
    mul_assoc, ← mul_assoc S.z, zz S, one_mul, C.kk]

theorem r₂_sq : (S.t * C.v' * C.D₁.w₂) ^ 2 = 1 := by
  rw [mul_assoc, C.sq_t_mul_eq (mul_mem C.v'_mem_Q₁ C.w₂_mem_Q₁),
    C.alpha_mul C.v'_mem_Q₁ C.w₂_mem_Q₁, C.alpha_v', C.alpha_w₂, C.sq_v'w₂,
    mul_assoc, ← mul_assoc C.F.yF, C.yy, one_mul, C.kk]

theorem r₃_sq : (S.t * C.v' * C.w₁' * C.D₁.w₂) ^ 2 = 1 := by
  have hm : C.v' * C.w₁' * C.D₁.w₂ ∈ C.D₁.Q₁ :=
    mul_mem (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) C.w₂_mem_Q₁
  rw [show S.t * C.v' * C.w₁' * C.D₁.w₂ = S.t * (C.v' * C.w₁' * C.D₁.w₂) by group,
    C.sq_t_mul_eq hm, C.alpha_mul (mul_mem C.v'_mem_Q₁ C.w₁'_mem_Q₁) C.w₂_mem_Q₁,
    C.alpha_mul C.v'_mem_Q₁ C.w₁'_mem_Q₁, C.alpha_v', C.alpha_w₁', C.alpha_w₂, C.sq_v'w₁'w₂]
  rw [show C.F.kF * S.z * C.F.yF * (S.z * C.F.yF * C.F.kF) =
    C.F.kF * (S.z * (C.F.yF * (S.z * C.F.yF))) * C.F.kF by group,
    show C.F.yF * (S.z * C.F.yF) = S.z * (C.F.yF * C.F.yF) by rw [← mul_assoc, C.yz, mul_assoc],
    C.yy, mul_one, zz S, mul_one, C.kk]

theorem C_le_Tm : C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) ≤
    C.Tm (zpowers C.F.kF) C.kpow_le_E0 :=
  C.C_le.trans (sup_le (sup_le (zpowers_le.mpr (C.E0_le_Tm _ _ C.k_mem_E0))
    (zpowers_le.mpr (C.v'_mem_Tm (mem_zpowers _)))) (zpowers_le.mpr (C.t_mem_Tm _ _)))

theorem D₁₁_le_normalizer {δ : X} (hδ : δ ∈ C.D₁.D₁₁) : δ ∈ normalizer (C.D₁.Q₁ : Set X) :=
  (C.D₁.D₁₁_le hδ).1.2

theorem normalizes_E0_of_mem_Q₁ {r : X} (hr : r ∈ C.D₁.Q₁) :
    r ∈ normalizer (C.E₀ : Set X) := mem_normalizer_of_map_le (by
  rintro _ ⟨e, he, rfl⟩
  show r * e * r⁻¹ ∈ C.E₀
  rw [C.conj_eq_of_mem_Q₁ hr he]; exact he)

theorem exists_D₁₁_moves {r : X} (hrQ : r ∈ C.D₁.Q₁) (hr2 : r ^ 2 = 1)
    (hrα : alpha S r ∉ zpowers C.F.kF) : ∃ δ ∈ C.D₁.D₁₁,
      (C.E₀ ⊔ zpowers r).map (MulAut.conj δ).toMonoidHom ≠ C.E₀ ⊔ zpowers r := by
  by_contra hall
  push Not at hall
  have hr0 : r ∉ C.E₀ := fun h => hrα (by rw [C.alpha_of_mem_E0 h]; exact one_mem _)
  have hinv : ∀ δ ∈ C.D₁.D₁₁, ∀ x : X, x * r⁻¹ ∈ C.E₀ → δ * x * δ⁻¹ * r⁻¹ ∈ C.E₀ := by
    intro δ hδ x hx
    have hδr : δ * r * δ⁻¹ ∈ C.E₀ ⊔ zpowers r := by
      rw [← hall δ hδ]; exact ⟨r, mem_sup_right (mem_zpowers r), rfl⟩
    have hδr0 : δ * r * δ⁻¹ ∉ C.E₀ := fun h => hr0 (by
      have := C.conj_E0_of_mem_normalizer (inv_mem (C.D₁₁_le_normalizer hδ)) h
      rwa [show δ⁻¹ * (δ * r * δ⁻¹) * δ⁻¹⁻¹ = r by group] at this)
    rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ hrQ)
      (by rw [hr2]; exact one_mem _) hδr with h | h
    · exact absurd h hδr0
    · rw [show δ * x * δ⁻¹ * r⁻¹ = (δ * (x * r⁻¹) * δ⁻¹) * (δ * r * δ⁻¹ * r⁻¹) by group]
      exact mul_mem (C.conj_E0_of_mem_normalizer (C.D₁₁_le_normalizer hδ) hx) h
  let M : Set X := {x | x * r⁻¹ ∈ C.E₀}
  let _ : MulAction C.D₁.D₁₁ M :=
    { smul := fun δ x => ⟨(δ : X) * x * (δ : X)⁻¹, hinv δ δ.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : C.D₁.D₁₁) : X) * x * ((1 : C.D₁.D₁₁) : X)⁻¹ = x
        simp)
      mul_smul := fun δ₁ δ₂ x => Subtype.ext (by
        show ((δ₁ * δ₂ : C.D₁.D₁₁) : X) * x * ((δ₁ * δ₂ : C.D₁.D₁₁) : X)⁻¹ =
          (δ₁ : X) * ((δ₂ : X) * x * (δ₂ : X)⁻¹) * (δ₁ : X)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardM : Nat.card M = 8 := by
    rw [← C.isRefl_y.card_E0 C.isK_k]
    exact Nat.card_congr
      { toFun := fun x => ⟨(x : X) * r⁻¹, x.2⟩
        invFun := fun e => ⟨(e : X) * r, by
          show (e : X) * r * r⁻¹ ∈ C.E₀
          rw [mul_inv_cancel_right]; exact e.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun e => Subtype.ext (by simp) }
  have hmod := C.D₁.isPGroup_D₁₁.card_modEq_card_fixedPoints M
  rw [hcardM] at hmod
  have hne : Nat.card (MulAction.fixedPoints C.D₁.D₁₁ M) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hxQ : (x : X) ∈ C.D₁.Q₁ := by
    rw [show (x : X) = ((x : X) * r⁻¹) * r by group]
    exact mul_mem (C.E0_le_Q₁ x.2) hrQ
  have hxC : (x : X) ∈ C.D₁.Q₁ ⊓ centralizer (C.D₁.D₁₁ : Set X) := by
    refine ⟨hxQ, mem_centralizer_iff.mpr fun δ hδ => ?_⟩
    have h1 : (δ : X) * x * δ⁻¹ = x := congrArg Subtype.val (hx ⟨δ, hδ⟩)
    calc δ * (x : X) = δ * x * δ⁻¹ * δ := by group
      _ = x * δ := by rw [h1]
  have hα : alpha S (x : X) ∈ zpowers C.F.kF := (C.mem_Tm.mp (C.C_le_Tm hxC)).2
  rw [C.alpha_eq_of_coset hxQ hrQ x.2] at hα
  exact hrα hα

def Conj₁ (A : Subgroup X) : Prop :=
  ∃ n ∈ normalizer (C.D₁.Q₁ : Set X), C.E₁.map (MulAut.conj n).toMonoidHom = A

theorem conj₁_def {A : Subgroup X} : C.Conj₁ A ↔
    ∃ n ∈ normalizer (C.D₁.Q₁ : Set X), C.E₁.map (MulAut.conj n).toMonoidHom = A := by
  unfold Conj₁; rfl

theorem conj₁_map {A : Subgroup X} (hA : C.Conj₁ A) {n : X}
    (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) : C.Conj₁ (A.map (MulAut.conj n).toMonoidHom) := by
  obtain ⟨m, hm, rfl⟩ := hA
  exact ⟨n * m, mul_mem hn hm, by rw [map_conj_map]⟩

theorem map_sup_zpowers {n : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (r : X) :
    (C.E₀ ⊔ zpowers r).map (MulAut.conj n).toMonoidHom = C.E₀ ⊔ zpowers (n * r * n⁻¹) := by
  rw [Subgroup.map_sup, C.map_E0_of_mem_normalizer hn, MonoidHom.map_zpowers]
  rfl

theorem sup_cases {x : X} (hx : x ∈ C.D₁.Q₁) (hx2 : x ^ 2 = 1) (hx0 : x ∉ C.E₀) :
    C.E₀ ⊔ zpowers x = C.E₀ ⊔ zpowers S.t ∨ C.E₀ ⊔ zpowers x = C.Fv ∨
      C.E₀ ⊔ zpowers x = C.G₁ ∨ C.E₀ ⊔ zpowers x = C.G₂ ∨ C.E₀ ⊔ zpowers x = C.G₃ := by
  rcases C.inv_cases hx hx2 with h | h | h | h | h | h
  · exact absurd h hx0
  · exact Or.inl (C.sup_zpowers_eq_of_coset h)
  · exact Or.inr (Or.inl (C.sup_zpowers_eq_of_coset h))
  · exact Or.inr (Or.inr (Or.inl (C.sup_zpowers_eq_of_coset h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (C.sup_zpowers_eq_of_coset h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (C.sup_zpowers_eq_of_coset h))))

theorem t_sq_mem : S.t ^ 2 ∈ C.E₀ := by rw [S.t_sq]; exact one_mem _

theorem v'_sq_mem_E0 : C.v' ^ 2 ∈ C.E₀ := by rw [C.v'_sq]; exact one_mem _

theorem sup_eq_of_alpha {x : X} (hx : x ∈ C.D₁.Q₁) (hx2 : x ^ 2 = 1) (hx0 : x ∉ C.E₀)
    (h1 : alpha S x ≠ 1) (hk : alpha S x ≠ C.F.kF) :
    C.E₀ ⊔ zpowers x = C.G₁ ∧ alpha S x = C.F.kF * S.z ∨
      C.E₀ ⊔ zpowers x = C.G₂ ∧ alpha S x = C.F.kF * C.F.yF ∨
      C.E₀ ⊔ zpowers x = C.G₃ ∧ alpha S x = C.F.kF * S.z * C.F.yF := by
  rcases C.sup_cases hx hx2 hx0 with h | h | h | h | h
  · exact absurd ((C.alpha_eq_of_sup_eq hx C.t_mem_Q₁ hx0 C.t_sq_mem h).trans (alpha_t S)) h1
  · exact absurd ((C.alpha_eq_of_sup_eq hx C.v'_mem_Q₁ hx0 C.v'_sq_mem_E0 h).trans C.alpha_v')
      hk
  · exact Or.inl ⟨h, (C.alpha_eq_of_sup_eq hx C.r₁_mem hx0 (by rw [C.r₁_sq]; exact one_mem _)
      h).trans C.alpha_r₁⟩
  · exact Or.inr (Or.inl ⟨h, (C.alpha_eq_of_sup_eq hx C.r₂_mem hx0
      (by rw [C.r₂_sq]; exact one_mem _) h).trans C.alpha_r₂⟩)
  · exact Or.inr (Or.inr ⟨h, (C.alpha_eq_of_sup_eq hx C.r₃_mem hx0
      (by rw [C.r₃_sq]; exact one_mem _) h).trans C.alpha_r₃⟩)

theorem kz_ne_one : C.F.kF * S.z ≠ 1 := fun h => C.k_not_mem_zpowers_z (by
  rw [eq_inv_of_mul_eq_one_left h]; exact inv_mem (mem_zpowers _))

theorem ky_ne_one : C.F.kF * C.F.yF ≠ 1 := fun h => C.isRefl_y.not_mem_B (by
  rw [eq_inv_of_mul_eq_one_right h]; exact inv_mem (kF_mem_B C.F))

theorem kzy_ne_one : C.F.kF * S.z * C.F.yF ≠ 1 := fun h => C.isRefl_y.not_mem_B (by
  rw [eq_inv_of_mul_eq_one_right h]; exact inv_mem (mul_mem (kF_mem_B C.F) z_mem_B))

theorem kz_ne_k : C.F.kF * S.z ≠ C.F.kF := fun h => S.z_ne_one (by simpa using h)

theorem ky_ne_k : C.F.kF * C.F.yF ≠ C.F.kF := fun h => C.y_ne_one (by simpa using h)

theorem kzy_ne_k : C.F.kF * S.z * C.F.yF ≠ C.F.kF := fun h => C.zy_ne_one (by
  rw [mul_assoc] at h; exact mul_left_cancel (h.trans (mul_one _).symm))

theorem kz_ne_ky : C.F.kF * S.z ≠ C.F.kF * C.F.yF := fun h => C.isRefl_y.not_mem_B (by
  rw [← mul_left_cancel h]; exact z_mem_B)

theorem kz_ne_kzy : C.F.kF * S.z ≠ C.F.kF * S.z * C.F.yF := fun h => C.y_ne_one
  (mul_left_cancel (h.symm.trans (mul_one _).symm))

theorem ky_ne_kzy : C.F.kF * C.F.yF ≠ C.F.kF * S.z * C.F.yF := fun h => S.z_ne_one (by
  rw [mul_assoc] at h
  have := mul_left_cancel h
  have := congrArg (· * C.F.yF⁻¹) this
  simpa using this.symm)

theorem G₁_ne_G₂ : C.G₁ ≠ C.G₂ := fun h => C.kz_ne_ky (by
  have := C.alpha_eq_of_sup_eq C.r₁_mem C.r₂_mem
    (C.not_mem_E0_of_alpha (by rw [C.alpha_r₁]; exact C.kz_ne_one))
    (by rw [C.r₂_sq]; exact one_mem _) h
  rwa [C.alpha_r₁, C.alpha_r₂] at this)

theorem G₁_ne_G₃ : C.G₁ ≠ C.G₃ := fun h => C.kz_ne_kzy (by
  have := C.alpha_eq_of_sup_eq C.r₁_mem C.r₃_mem
    (C.not_mem_E0_of_alpha (by rw [C.alpha_r₁]; exact C.kz_ne_one))
    (by rw [C.r₃_sq]; exact one_mem _) h
  rwa [C.alpha_r₁, C.alpha_r₃] at this)

theorem G₂_ne_G₃ : C.G₂ ≠ C.G₃ := fun h => C.ky_ne_kzy (by
  have := C.alpha_eq_of_sup_eq C.r₂_mem C.r₃_mem
    (C.not_mem_E0_of_alpha (by rw [C.alpha_r₂]; exact C.ky_ne_one))
    (by rw [C.r₃_sq]; exact one_mem _) h
  rwa [C.alpha_r₂, C.alpha_r₃] at this)

theorem u_normalizes : C.D₁.u ∈ normalizer (C.D₁.Q₁ : Set X) :=
  C.S₁_le_normalizer_Q₁ C.u_mem_S₁

theorem conj_mem_Q₁ {n x : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X)) (hx : x ∈ C.D₁.Q₁) :
    n * x * n⁻¹ ∈ C.D₁.Q₁ := (mem_normalizer_iff.mp hn x).mp hx

theorem u_G₂ : C.G₂.map (MulAut.conj C.D₁.u).toMonoidHom = C.G₃ := by
  rw [C.map_sup_zpowers C.u_normalizes]
  have hut : C.D₁.u * S.t * C.D₁.u⁻¹ = S.t := conj_eq_of_comm (C.u_comm_B t_mem_B)
  have hxQ := C.conj_mem_Q₁ C.u_normalizes C.r₂_mem
  have hx2 := conj_sq_one (n := C.D₁.u) C.r₂_sq
  have hα : alpha S (C.D₁.u * (S.t * C.v' * C.D₁.w₂) * C.D₁.u⁻¹) =
      C.F.kF * S.z * C.F.yF := by
    rw [alpha_conj S hut, C.alpha_r₂, conj_mul_eq, conj_eq_of_comm (C.u_comm_B (kF_mem_B C.F)),
      C.u_y, mul_assoc]
  have hx0 := C.not_mem_E0_of_alpha (by rw [hα]; exact C.kzy_ne_one)
  rcases C.sup_eq_of_alpha hxQ hx2 hx0 (by rw [hα]; exact C.kzy_ne_one)
    (by rw [hα]; exact C.kzy_ne_k) with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd (hα.symm.trans h) (Ne.symm C.kz_ne_kzy)
  · exact absurd (hα.symm.trans h) (Ne.symm C.ky_ne_kzy)
  · exact h

theorem u_G₃ : C.G₃.map (MulAut.conj C.D₁.u).toMonoidHom = C.G₂ := by
  rw [← C.u_G₂, map_conj_map, C.u_mul_u]
  ext x
  simp

theorem D₁₁_maps {δ : X} (hδ : δ ∈ C.D₁.D₁₁) {r : X} (hrQ : r ∈ C.D₁.Q₁) (hr2 : r ^ 2 = 1)
    (hr1 : alpha S r ≠ 1) (hrk : alpha S r ≠ C.F.kF) :
    (C.E₀ ⊔ zpowers r).map (MulAut.conj δ).toMonoidHom = C.G₁ ∨
      (C.E₀ ⊔ zpowers r).map (MulAut.conj δ).toMonoidHom = C.G₂ ∨
      (C.E₀ ⊔ zpowers r).map (MulAut.conj δ).toMonoidHom = C.G₃ := by
  have hN := C.D₁₁_le_normalizer hδ
  rw [C.map_sup_zpowers hN]
  have hδt : δ * S.t * δ⁻¹ = S.t := by
    have := mem_centralizer_singleton_iff.mp (C.D₁.D₁₁_le hδ).2
    rw [this, mul_inv_cancel_right]
  have hδE : δ ∈ normalizer (C.E₁ : Set X) := (C.D₁.D₁₁_le hδ).1.1
  have hα := alpha_conj S (x := r) hδt
  have h1 : alpha S (δ * r * δ⁻¹) ≠ 1 := by
    rw [hα]; intro h; apply hr1
    calc alpha S r = δ⁻¹ * (δ * alpha S r * δ⁻¹) * δ := by group
      _ = 1 := by rw [h]; group
  have hk : alpha S (δ * r * δ⁻¹) ≠ C.F.kF := by
    rw [hα]; intro h; apply hrk
    have hk' := C.D₁.k_fixed _ (inv_mem hδE)
    calc alpha S r = δ⁻¹ * (δ * alpha S r * δ⁻¹) * δ⁻¹⁻¹ := by group
      _ = C.F.kF := by rw [h, hk']
  rcases C.sup_eq_of_alpha (C.conj_mem_Q₁ hN hrQ) (conj_sq_one hr2)
    (C.not_mem_E0_of_alpha h1) h1 hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem conj₁_cases : (C.Conj₁ C.G₁ ∧ C.Conj₁ C.G₂ ∧ C.Conj₁ C.G₃) ∨
    (¬ C.Conj₁ C.G₁ ∧ ¬ C.Conj₁ C.G₂ ∧ ¬ C.Conj₁ C.G₃) := by
  have h23 : C.Conj₁ C.G₂ ↔ C.Conj₁ C.G₃ :=
    ⟨fun h => C.u_G₂ ▸ C.conj₁_map h C.u_normalizes,
      fun h => C.u_G₃ ▸ C.conj₁_map h C.u_normalizes⟩
  have hα1 : alpha S (S.t * C.v' * C.w₁') ∉ zpowers C.F.kF := by
    rw [C.alpha_r₁]
    intro h
    rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq h with h' | h'
    · exact C.kz_ne_one h'
    · exact C.kz_ne_k h'
  obtain ⟨δ, hδ, hmove⟩ := C.exists_D₁₁_moves C.r₁_mem C.r₁_sq hα1
  have hN := C.D₁₁_le_normalizer hδ
  have hτ₁ := C.D₁₁_maps hδ C.r₁_mem C.r₁_sq (by rw [C.alpha_r₁]; exact C.kz_ne_one)
    (by rw [C.alpha_r₁]; exact C.kz_ne_k)
  have hτ₂ := C.D₁₁_maps hδ C.r₂_mem C.r₂_sq (by rw [C.alpha_r₂]; exact C.ky_ne_one)
    (by rw [C.alpha_r₂]; exact C.ky_ne_k)
  have hτ₃ := C.D₁₁_maps hδ C.r₃_mem C.r₃_sq (by rw [C.alpha_r₃]; exact C.kzy_ne_one)
    (by rw [C.alpha_r₃]; exact C.kzy_ne_k)
  by_cases h1 : C.Conj₁ C.G₁ <;> by_cases h2 : C.Conj₁ C.G₂
  · exact Or.inl ⟨h1, h2, h23.mp h2⟩
  · exfalso
    have h3 : ¬ C.Conj₁ C.G₃ := fun h => h2 (h23.mpr h)
    have hc := C.conj₁_map h1 hN
    rcases hτ₁ with h | h | h
    · exact hmove h
    · exact h2 (h ▸ hc)
    · exact h3 (h ▸ hc)
  · exfalso
    have h3 := h23.mp h2
    have hc₂ := C.conj₁_map h2 hN
    have hc₃ := C.conj₁_map h3 hN
    rcases hτ₁ with e1 | e1 | e1
    · exact hmove e1
    · rcases hτ₂ with e2 | e2 | e2
      · exact h1 (e2 ▸ hc₂)
      · exact C.G₁_ne_G₂ (map_conj_inj (e1.trans e2.symm))
      · rcases hτ₃ with e3 | e3 | e3
        · exact h1 (e3 ▸ hc₃)
        · exact C.G₁_ne_G₃ (map_conj_inj (e1.trans e3.symm))
        · exact C.G₂_ne_G₃ (map_conj_inj (e2.trans e3.symm))
    · rcases hτ₂ with e2 | e2 | e2
      · exact h1 (e2 ▸ hc₂)
      · rcases hτ₃ with e3 | e3 | e3
        · exact h1 (e3 ▸ hc₃)
        · exact C.G₂_ne_G₃ (map_conj_inj (e2.trans e3.symm))
        · exact C.G₁_ne_G₃ (map_conj_inj (e1.trans e3.symm))
      · exact C.G₁_ne_G₂ (map_conj_inj (e1.trans e2.symm))
  · exact Or.inr ⟨h1, h2, fun h => h2 (h23.mpr h)⟩

theorem conj₁_all : C.Conj₁ C.G₁ ∧ C.Conj₁ C.G₂ ∧ C.Conj₁ C.G₃ := by
  rcases C.conj₁_cases with h | ⟨h1, h2, h3⟩
  · exact h
  · exfalso
    refine C.false_of_normalizer_le fun n hn => ?_
    rcases C.conj_E₁_cases hn with h | h | h | h | h
    · exact mem_normalizer_of_map_eq h
    · exact absurd h (C.map_ne_Fv n)
    · exact absurd ⟨n, hn, h⟩ h1
    · exact absurd ⟨n, hn, h⟩ h2
    · exact absurd ⟨n, hn, h⟩ h3

theorem false_of_e4q8 (hq : C.D₁.q0 = .e4q8) : False := by
  obtain ⟨n, -, hn⟩ := C.conj₁_all.1
  exact C.map_ne_G₁ hq n hn

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
