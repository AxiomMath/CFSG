module

public import CFSG.GH74.GLS.Stage4.T2Steps
public import CFSG.GH74.GLS.Stage4.T2Torus
public import CFSG.GH74.GLS.Stage4.T2SL2C
public import CFSG.GH74.GLS.Stage4.T2Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.T2
open scoped Pointwise commutatorElement

structure P51Coord {G : Type} [Group G] (z t u : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
    [Field F₂] where
  φ₁ : SL2 F₁ →* G
  φ₂ : SL2 F₂ →* G
  inj₁ : Function.Injective φ₁
  inj₂ : Function.Injective φ₂
  range₁ : φ₁.range = K₁
  range₂ : φ₂.range = K₂
  z₁ : φ₁ (negOne F₁) = z
  z₂ : φ₂ (negOne F₂) = z
  τ₁ : GL (Fin 2) F₁
  τ₂ : GL (Fin 2) F₂
  hτ₁ : ∀ x, t * φ₁ x * t⁻¹ = φ₁ (slConj τ₁ x)
  hτ₂ : ∀ x, t * φ₂ x * t⁻¹ = φ₂ (slConj τ₂ x)
  ns₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det τ₁ : F₁ˣ) : F₁)
  ns₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det τ₂ : F₂ˣ) : F₂)
  hu₁ : ∀ x, u * φ₁ x * u⁻¹ = φ₁ (slConj (dNeg F₁) x)
  hu₂ : ∀ x, u * φ₂ x * u⁻¹ = φ₂ (slConj (dNeg F₂) x)
  hu2 : u * u = 1
  hcase : (∃ x₁ ∈ tSub F₁, ∃ x₂ ∈ tSub F₂, u = φ₁ x₁ * φ₂ x₂) ∨
    (u = t ∧ τ₁ = dNeg F₁ ∧ τ₂ = dNeg F₂)

section Coord

variable {G : Type} [Group G] {z t u : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem P51Coord.comm (C : P51Coord z t u K₁ K₂ F₁ F₂) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (a : SL2 F₁) (b : SL2 F₂) : C.φ₁ a * C.φ₂ b = C.φ₂ b * C.φ₁ a := by
  have h₁ : C.φ₁ a ∈ K₁ := C.range₁.le ⟨a, rfl⟩
  have h₂ : C.φ₂ b ∈ K₂ := C.range₂.le ⟨b, rfl⟩
  exact hcomm _ h₁ _ h₂

theorem P51Coord.slConj_sq₁ (C : P51Coord z t u K₁ K₂ F₁ F₂) (htt : t * t = 1) (x : SL2 F₁) :
    slConj (C.τ₁ * C.τ₁) x = x := by
  apply C.inj₁
  have h1 := C.hτ₁ (slConj C.τ₁ x)
  have h2 := C.hτ₁ x
  rw [slConj_mul, ← h1, ← h2]
  have : t * (t * C.φ₁ x * t⁻¹) * t⁻¹ = (t * t) * C.φ₁ x * (t * t)⁻¹ := by group
  rw [this, htt]; group

theorem P51Coord.slConj_sq₂ (C : P51Coord z t u K₁ K₂ F₁ F₂) (htt : t * t = 1) (x : SL2 F₂) :
    slConj (C.τ₂ * C.τ₂) x = x := by
  apply C.inj₂
  have h1 := C.hτ₂ (slConj C.τ₂ x)
  have h2 := C.hτ₂ x
  rw [slConj_mul, ← h1, ← h2]
  have : t * (t * C.φ₂ x * t⁻¹) * t⁻¹ = (t * t) * C.φ₂ x * (t * t)⁻¹ := by group
  rw [this, htt]; group

@[expose] def P51Coord.k (C : P51Coord z t u K₁ K₂ F₁ F₂) : G :=
  C.φ₁ (adjSL C.τ₁) * C.φ₂ (adjSL C.τ₂)

@[expose] def P51Coord.s (C : P51Coord z t u K₁ K₂ F₁ F₂) : G := C.k * t

theorem zpowers_eq_one_or_self {g : G} (hzz : z * z = 1) (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have key : z ^ n = (z * z) ^ (n / 2) * z ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2]
    rw [zpow_add, zpow_mul, zpow_two]
  rw [key, hzz, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem P51Coord.conj_k_φ₁ (C : P51Coord z t u K₁ K₂ F₁ F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (y : SL2 F₁) :
    C.k * C.φ₁ y * C.k⁻¹ = C.φ₁ (adjSL C.τ₁ * y * (adjSL C.τ₁)⁻¹) := by
  have hc : C.φ₂ (adjSL C.τ₂) * C.φ₁ y * (C.φ₂ (adjSL C.τ₂))⁻¹ = C.φ₁ y := by
    rw [← C.comm hcomm y (adjSL C.τ₂)]; group
  calc C.k * C.φ₁ y * C.k⁻¹
      = C.φ₁ (adjSL C.τ₁) * (C.φ₂ (adjSL C.τ₂) * C.φ₁ y * (C.φ₂ (adjSL C.τ₂))⁻¹) *
          (C.φ₁ (adjSL C.τ₁))⁻¹ := by simp only [P51Coord.k]; group
    _ = C.φ₁ (adjSL C.τ₁ * y * (adjSL C.τ₁)⁻¹) := by
        rw [hc]; simp [map_mul, map_inv, mul_assoc]

theorem P51Coord.conj_k_φ₂ (C : P51Coord z t u K₁ K₂ F₁ F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (y : SL2 F₂) :
    C.k * C.φ₂ y * C.k⁻¹ = C.φ₂ (adjSL C.τ₂ * y * (adjSL C.τ₂)⁻¹) := by
  have h1 : C.k * C.φ₂ y * C.k⁻¹ =
      C.φ₁ (adjSL C.τ₁) * C.φ₂ (adjSL C.τ₂ * y * (adjSL C.τ₂)⁻¹) * (C.φ₁ (adjSL C.τ₁))⁻¹ := by
    simp only [P51Coord.k, map_mul, map_inv]; group
  have h2 : C.φ₁ (adjSL C.τ₁) * C.φ₂ (adjSL C.τ₂ * y * (adjSL C.τ₂)⁻¹) *
      (C.φ₁ (adjSL C.τ₁))⁻¹ = C.φ₂ (adjSL C.τ₂ * y * (adjSL C.τ₂)⁻¹) := by
    rw [C.comm hcomm]; group
  rw [h1, h2]

theorem P51Coord.conj_t_k (C : P51Coord z t u K₁ K₂ F₁ F₂) :
    t * C.k * t⁻¹ = C.φ₁ (slConj C.τ₁ (adjSL C.τ₁)) * C.φ₂ (slConj C.τ₂ (adjSL C.τ₂)) := by
  have : t * C.k * t⁻¹ = (t * C.φ₁ (adjSL C.τ₁) * t⁻¹) * (t * C.φ₂ (adjSL C.τ₂) * t⁻¹) := by
    simp only [P51Coord.k]; group
  rw [this, C.hτ₁, C.hτ₂]

theorem P51Coord.torusData (C : P51Coord z t u K₁ K₂ F₁ F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z)
    (hzz : z * z = 1) (htt : t * t = 1) :
    TorusData C.φ₁ C.φ₂ C.s (Matrix.GeneralLinearGroup.det C.τ₁)
      (Matrix.GeneralLinearGroup.det C.τ₂) := by
  have hτ₁sq := sq_eq_neg_det_of_slConj_sq C.τ₁ C.ns₁ (C.slConj_sq₁ htt)
  have hτ₂sq := sq_eq_neg_det_of_slConj_sq C.τ₂ C.ns₂ (C.slConj_sq₂ htt)
  refine ⟨C.inj₁, C.inj₂, C.comm hcomm, by rw [C.z₁, C.z₂], ?_, ?_, ?_, ?_, C.ns₁⟩
  · intro g hg₁ hg₂
    rcases zpowers_eq_one_or_self hzz (hinter ⟨C.range₁.le hg₁, C.range₂.le hg₂⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [C.z₁]; exact h)
  · intro x
    have e : C.s * C.φ₁ x * C.s⁻¹ = C.k * (t * C.φ₁ x * t⁻¹) * C.k⁻¹ := by
      simp only [P51Coord.s]; group
    rw [e, C.hτ₁, C.conj_k_φ₁ hcomm, adjSL_conj]
  · intro x
    have e : C.s * C.φ₂ x * C.s⁻¹ = C.k * (t * C.φ₂ x * t⁻¹) * C.k⁻¹ := by
      simp only [P51Coord.s]; group
    rw [e, C.hτ₂, C.conj_k_φ₂ hcomm, adjSL_conj]
  · have e : C.s * C.s = C.k * (t * C.k * t⁻¹) * (t * t) := by
      simp only [P51Coord.s]; group
    rw [e, htt, mul_one, C.conj_t_k]
    have hc : C.φ₂ (adjSL C.τ₂) * C.φ₁ (slConj C.τ₁ (adjSL C.τ₁)) =
        C.φ₁ (slConj C.τ₁ (adjSL C.τ₁)) * C.φ₂ (adjSL C.τ₂) :=
      (C.comm hcomm _ _).symm
    calc C.k * (C.φ₁ (slConj C.τ₁ (adjSL C.τ₁)) * C.φ₂ (slConj C.τ₂ (adjSL C.τ₂)))
        = C.φ₁ (adjSL C.τ₁) * (C.φ₂ (adjSL C.τ₂) * C.φ₁ (slConj C.τ₁ (adjSL C.τ₁))) *
            C.φ₂ (slConj C.τ₂ (adjSL C.τ₂)) := by simp only [P51Coord.k]; group
      _ = C.φ₁ (adjSL C.τ₁) * (C.φ₁ (slConj C.τ₁ (adjSL C.τ₁)) * C.φ₂ (adjSL C.τ₂)) *
            C.φ₂ (slConj C.τ₂ (adjSL C.τ₂)) := by rw [hc]
      _ = C.φ₁ (adjSL C.τ₁ * slConj C.τ₁ (adjSL C.τ₁)) *
            C.φ₂ (adjSL C.τ₂ * slConj C.τ₂ (adjSL C.τ₂)) := by simp [map_mul, mul_assoc]
      _ = _ := by rw [adjSL_mul_conj_self _ hτ₁sq, adjSL_mul_conj_self _ hτ₂sq]

theorem P51Coord.torus_mem (C : P51Coord z t u K₁ K₂ F₁ F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z)
    (hzz : z * z = 1) (htt : t * t = 1)
    (hC₁ : K₁ ⊔ K₂ ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (ht : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G))) :
    ∃ s : G, TorusData C.φ₁ C.φ₂ s (Matrix.GeneralLinearGroup.det C.τ₁)
        (Matrix.GeneralLinearGroup.det C.τ₂) ∧
      u ∈ Hm C.φ₁ C.φ₂ ⊔ Subgroup.zpowers s ∧
      s ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
  refine ⟨C.s, C.torusData hcomm hinter hzz htt, ?_, ?_⟩
  swap
  · show C.k * t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G))
    refine Subgroup.mul_mem _ (hC₁ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right ?_))) ht
    · exact C.range₁.le ⟨_, rfl⟩
    · exact C.range₂.le ⟨_, rfl⟩
  rcases C.hcase with ⟨x₁, hx₁, x₂, hx₂, hu⟩ | ⟨hut, h₁, h₂⟩
  · have T := C.torusData hcomm hinter hzz htt
    refine Subgroup.mem_sup_left ?_
    rw [T.mem_Hm]
    exact ⟨x₁, hx₁, x₂, hx₂, hu⟩
  · have hk : C.k = 1 := by
      simp only [P51Coord.k]
      rw [h₁, h₂, adjSL_dNeg, adjSL_dNeg]
      simp
    have hs : C.s = t := by simp [P51Coord.s, hk]
    have h' : t ∈ Hm C.φ₁ C.φ₂ ⊔ Subgroup.zpowers C.s := by
      rw [hs]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have e := congrArg (fun v => v ∈ Hm C.φ₁ C.φ₂ ⊔ Subgroup.zpowers C.s) hut
    exact Eq.mpr e h'

end Coord

section Core

variable {G : Type} [Group G]

theorem map_conj_mem {F : Type} [Field F] {A B : Subgroup (SL2 F)} (φ : SL2 F →* G) (g : G)
    (f : SL2 F → SL2 F) (hg : ∀ x, g * φ x * g⁻¹ = φ (f x)) (hf : ∀ x ∈ A, f x ∈ B) :
    ∀ x ∈ A.map φ, g * x * g⁻¹ ∈ B.map φ := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨f a, hf a ha, (hg a).symm⟩

theorem map_conj_inv {F : Type} [Field F] {A : Subgroup (SL2 F)} (φ : SL2 F →* G) (g : G)
    (f : SL2 F → SL2 F) (hg : ∀ x, g * φ x * g⁻¹ = φ (f x)) (hf : ∀ x ∈ A, f x = x⁻¹) :
    ∀ x ∈ A.map φ, g * x * g⁻¹ = x⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rw [hg, hf a ha, map_inv]

theorem map_comm_of {F : Type} [Field F] {A : Subgroup (SL2 F)} (φ : SL2 F →* G)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : ∀ x ∈ A.map φ, ∀ y ∈ A.map φ, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hA a ha b hb]

theorem map_pow_eq_one {F : Type} [Field F] {A : Subgroup (SL2 F)} (φ : SL2 F →* G) (n : ℕ)
    (hA : ∀ a ∈ A, a ^ n = 1) : ∀ x ∈ A.map φ, x ^ n = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hA a ha, map_one]

theorem card_map_eq {F : Type} [Field F] (A : Subgroup (SL2 F)) (φ : SL2 F →* G)
    (hφ : Function.Injective φ) : Nat.card ↥(A.map φ) = Nat.card ↥A :=
  Subgroup.card_map_of_injective hφ

end Core

section Loc5Core

variable {G : Type} [Group G] [Finite G]

theorem loc5_core {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (φ₁ : SL2 F₁ →* G) (φ₂ : SL2 F₂ →* G) (s u : G) (d₁ : F₁ˣ) (d₂ : F₂ˣ)
    (hSet : Ch6Setup G Gs q₁ q₂ (φ₁ (negOne F₁)) φ₁.range φ₂.range F₁ F₂)
    (T : TorusData φ₁ φ₂ s d₁ d₂)
    (hu₁ : ∀ x, u * φ₁ x * u⁻¹ = φ₁ (slConj (dNeg F₁) x))
    (hu₂ : ∀ x, u * φ₂ x * u⁻¹ = φ₂ (slConj (dNeg F₂) x))
    (hu2 : u * u = 1) (hu_mem : u ∈ Hm φ₁ φ₂ ⊔ Subgroup.zpowers s)
    (hsC : s ∈ oPrimeResidualOf 2 (centralizer ({φ₁ (negOne F₁)} : Set G))) :
    ∃ N : T2N1 G, N.z = φ₁ (negOne F₁) ∧ N.K₁ = φ₁.range ∧ N.K₂ = φ₂.range ∧ N.q₁ = q₁ ∧
      N.q₂ = q₂ ∧ Ch6Loc5 N u ∧ Ch6Coord N := by
  have := hSet.finite₁
  have := hSet.finite₂
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card (by rw [hSet.card₁]; exact hSet.odd₁)
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card (by rw [hSet.card₂]; exact hSet.odd₂)
  have hzz : φ₁ (negOne F₁) * φ₁ (negOne F₁) = 1 := TorusData.z_mul_z
  have hzc : ∀ x : SL2 F₁, φ₁ (negOne F₁) * φ₁ x = φ₁ x * φ₁ (negOne F₁) := TorusData.z_comm_φ₁
  have hu_nc : ¬ (u * φ₁ (sl2U 1) = φ₁ (sl2U 1) * u) := by
    intro hc
    have h1 := hu₁ (sl2U 1)
    have h2 : u * φ₁ (sl2U 1) * u⁻¹ = φ₁ (sl2U 1) := by rw [hc]; group
    rw [h2] at h1
    exact slConj_dNeg_sl2U_ne h2₁ (T.inj₁ h1.symm)
  have hu_ne_one : u ≠ 1 := fun h => hu_nc (by rw [h]; simp)
  have hu_ne_z : u ≠ φ₁ (negOne F₁) := fun h => hu_nc (by rw [h]; exact hzc _)
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu_ne_one
  have huz : u * φ₁ (negOne F₁) = φ₁ (negOne F₁) * u := by
    have h1 := hu₁ (negOne F₁)
    rw [slConj_negOne] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hcentr₁ : ∀ y : SL2 F₁, u * φ₁ y = φ₁ y * u ↔ y ∈ tSub F₁ := by
    intro y
    constructor
    · intro hc
      have h1 := hu₁ y
      have h2 : u * φ₁ y * u⁻¹ = φ₁ y := by rw [hc]; group
      rw [h2] at h1
      exact centralizer_dNeg h2₁ y (T.inj₁ h1.symm)
    · intro hy
      have h1 := hu₁ y
      have h3 : slConj (dNeg F₁) y = y := slConj_diag_tSub 1 (-1) y hy
      rw [h3] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
  have hcentr₂ : ∀ y : SL2 F₂, u * φ₂ y = φ₂ y * u ↔ y ∈ tSub F₂ := by
    intro y
    constructor
    · intro hc
      have h1 := hu₂ y
      have h2 : u * φ₂ y * u⁻¹ = φ₂ y := by rw [hc]; group
      rw [h2] at h1
      exact centralizer_dNeg h2₂ y (T.inj₂ h1.symm)
    · intro hy
      have h1 := hu₂ y
      have h3 : slConj (dNeg F₂) y = y := slConj_diag_tSub 1 (-1) y hy
      rw [h3] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
  have hw₁u : u * φ₁ (sl2W F₁) * u⁻¹ = (φ₁ (sl2W F₁))⁻¹ := by
    rw [hu₁, slConj_dNeg_W, map_inv]
  have hw₂u : u * φ₂ (sl2W F₂) * u⁻¹ = (φ₂ (sl2W F₂))⁻¹ := by
    rw [hu₂, slConj_dNeg_W, map_inv]
  have hz₂ : φ₁ (negOne F₁) = φ₂ (negOne F₂) := T.zeq
  have hwwu : ∀ (w z : G), w * w = z → z * z = 1 → z * w = w * z → z * u = u * z →
      u * w * u⁻¹ = w⁻¹ → w * u * w⁻¹ = u * z := by
    intro w z hww hzz' hzw hzu hwu
    have hwinv : w⁻¹ = w * z := by
      apply inv_eq_of_mul_eq_one_right
      calc w * (w * z) = (w * w) * z := by group
        _ = z * z := by rw [hww]
        _ = 1 := hzz'
    have e1 : u * w = w * z * u := by
      rw [← hwinv]; exact mul_inv_eq_iff_eq_mul.1 hwu
    have e2 : w * u * w = u := by
      calc w * u * w = w * (u * w) := by group
        _ = w * (w * z * u) := by rw [e1]
        _ = (w * w) * z * u := by group
        _ = z * z * u := by rw [hww]
        _ = u := by rw [hzz', one_mul]
    rw [hwinv]
    calc w * u * (w * z) = (w * u * w) * z := by group
      _ = u * z := by rw [e2]
  have hzw₁ : φ₁ (negOne F₁) * φ₁ (sl2W F₁) = φ₁ (sl2W F₁) * φ₁ (negOne F₁) := hzc _
  have hzw₂ : φ₁ (negOne F₁) * φ₂ (sl2W F₂) = φ₂ (sl2W F₂) * φ₁ (negOne F₁) :=
    TorusData.z_comm_φ₂ T _
  have hzu : φ₁ (negOne F₁) * u = u * φ₁ (negOne F₁) := huz.symm
  have hww₁ : φ₁ (sl2W F₁) * φ₁ (sl2W F₁) = φ₁ (negOne F₁) := TorusData.w₁_sq
  have hww₂ : φ₂ (sl2W F₂) * φ₂ (sl2W F₂) = φ₁ (negOne F₁) := T.w₂_sq
  have hcomm₁₂ : φ₁ (sl2W F₁) * φ₂ (sl2W F₂) = φ₂ (sl2W F₂) * φ₁ (sl2W F₁) := T.comm _ _
  have hw₀sq : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) = 1 := by
    calc (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))
        = φ₁ (sl2W F₁) * (φ₂ (sl2W F₂) * φ₁ (sl2W F₁)) * φ₂ (sl2W F₂) := by group
      _ = φ₁ (sl2W F₁) * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * φ₂ (sl2W F₂) := by rw [hcomm₁₂]
      _ = (φ₁ (sl2W F₁) * φ₁ (sl2W F₁)) * (φ₂ (sl2W F₂) * φ₂ (sl2W F₂)) := by group
      _ = 1 := by rw [hww₁, hww₂, hzz]
  have hwconj₁ : ∀ x : SL2 F₁, φ₁ (sl2W F₁) * φ₁ x * (φ₁ (sl2W F₁))⁻¹ =
      φ₁ (sl2W F₁ * x * (sl2W F₁)⁻¹) := fun x => by simp [map_mul, map_inv]
  have hwconj₂ : ∀ x : SL2 F₂, φ₂ (sl2W F₂) * φ₂ x * (φ₂ (sl2W F₂))⁻¹ =
      φ₂ (sl2W F₂ * x * (sl2W F₂)⁻¹) := fun x => by simp [map_mul, map_inv]
  have hKs₁ : ∀ x : G, x ∈ (uSub F₁).map φ₁ → x ∈ φ₁.range := fun x hx =>
    Subgroup.map_le_range _ _ hx
  have hAp : IsPGroup 2 ↥(Subgroup.closure
      ({φ₁ (negOne F₁), u, φ₁ (sl2W F₁), φ₂ (sl2W F₂)} : Set G)) :=
    t2S_isPGroup_closure hzz hu2 hww₁ hww₂ hzw₁ hzw₂ hcomm₁₂ hzu hw₁u hw₂u
  have hAz : ∀ a ∈ Subgroup.closure
      ({φ₁ (negOne F₁), u, φ₁ (sl2W F₁), φ₂ (sl2W F₂)} : Set G),
      a * φ₁ (negOne F₁) = φ₁ (negOne F₁) * a := by
    have hle : Subgroup.closure ({φ₁ (negOne F₁), u, φ₁ (sl2W F₁), φ₂ (sl2W F₂)} : Set G) ≤
        centralizer ({φ₁ (negOne F₁)} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with rfl | rfl | rfl | rfl
      · rfl
      · exact huz
      · exact hzw₁.symm
      · exact hzw₂.symm
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  obtain ⟨S, hSp, hSidx, hAS, hSz⟩ := exists_sylow_two_contains hSet.central _ hAp hAz
  have hzS : φ₁ (negOne F₁) ∈ S := hAS (Subgroup.subset_closure (by simp))
  have huS : u ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hw₁S : φ₁ (sl2W F₁) ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hw₂S : φ₂ (sl2W F₂) ∈ S := hAS (Subgroup.subset_closure (by simp))
  have hSC : S ≤ oPrimeResidualOf 2 (centralizer ({φ₁ (negOne F₁)} : Set G)) :=
    le_oPrimeResidualOf_centralizer hSp hSz
  have hSidx2 : (S ⊓ (φ₁.range ⊔ φ₂.range)).relIndex S = 2 :=
    relIndex_inf_sylow_of_index_two hSet.le_residual hSet.index_two hSC hSidx
  have hKS : φ₁.range ⊔ φ₂.range ⊔ S = oPrimeResidualOf 2 (centralizer ({φ₁ (negOne F₁)} : Set G)) := by
    refine sup_eq_of_relIndex_two le_sup_left (sup_le hSet.le_residual hSC) hSet.index_two ?_
    intro hle
    have hSK : S ≤ φ₁.range ⊔ φ₂.range := le_trans le_sup_right hle
    have h1 : (S ⊓ (φ₁.range ⊔ φ₂.range)).relIndex S = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact fun x hx => ⟨hx, hSK hx⟩
    rw [h1] at hSidx2
    exact absurd hSidx2 (by norm_num)
  refine ⟨⟨q₁, q₂, φ₁ (negOne F₁), S, φ₁.range, φ₂.range, Hm φ₁ φ₂ ⊔ Subgroup.zpowers s,
    (uSub F₁).map φ₁, (lSub F₁).map φ₁, (uSub F₂).map φ₂, (lSub F₂).map φ₂,
    φ₁ (sl2W F₁), φ₂ (sl2W F₂)⟩, rfl, rfl, rfl, rfl, rfl, ?loc, ?coord⟩
  case coord =>
    exact
      { coord₁ := ⟨F₁, inferInstance, hSet.finite₁, φ₁, hSet.card₁, T.inj₁, rfl, rfl, rfl, rfl, rfl,
          T.Hg_inf_K₁⟩
        coord₂ := ⟨F₂, inferInstance, hSet.finite₂, φ₂, hSet.card₂, T.inj₂, rfl, T.zeq.symm, rfl,
          rfl, rfl, T.Hg_inf_K₂⟩ }
  exact
    { q₁_odd := hSet.odd₁
      q₂_odd := hSet.odd₂
      q₂_le := hSet.le
      q₁_ge := hSet.five
      q₂_ge := by
        have h1 : 1 < Nat.card F₂ := Finite.one_lt_card
        rw [hSet.card₂] at h1
        obtain ⟨k, hk⟩ := hSet.odd₂
        show 3 ≤ q₂
        omega
      q₁_pp := by
        have : Fintype F₁ := Fintype.ofFinite F₁
        obtain ⟨n, hp, hn⟩ := FiniteField.card F₁ (ringChar F₁)
        exact ⟨ringChar F₁, n, hp, by rw [← hSet.card₁, Nat.card_eq_fintype_card, hn]⟩
      q₂_pp := by
        have : Fintype F₂ := Fintype.ofFinite F₂
        obtain ⟨n, hp, hn⟩ := FiniteField.card F₂ (ringChar F₂)
        exact ⟨ringChar F₂, n, hp, by rw [← hSet.card₂, Nat.card_eq_fintype_card, hn]⟩
      z_ord := hSet.central.1
      one_class := hSet.one_class
      O2prime := hSet.O2prime
      K_comm := hSet.comm
      iso₁ := ⟨F₁, inferInstance, hSet.finite₁, hSet.card₁, hSet.iso₁⟩
      iso₂ := ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂, hSet.iso₂⟩
      z_mem_K₁ := hSet.z_mem₁
      z_mem_K₂ := hSet.z_mem₂
      K_inter := hSet.inter_eq.le
      u_ord := hu_ord
      u_ne := hu_ne_z
      u_comm := huz
      S_pGroup := hSp
      S_sylow := hSidx
      z_mem_S := hzS
      z_cent_S := hSz
      u_mem_S := huS
      S_idx := hSidx2
      w₁_memS := hw₁S
      w₂_memS := hw₂S
      K₁_eq := by
        show φ₁.range = (uSub F₁).map φ₁ ⊔ (lSub F₁).map φ₁
        rw [MonoidHom.range_eq_map, ← Subgroup.map_sup, uSub_sup_lSub]
      K₂_eq := by
        show φ₂.range = (uSub F₂).map φ₂ ⊔ (lSub F₂).map φ₂
        rw [MonoidHom.range_eq_map, ← Subgroup.map_sup, uSub_sup_lSub]
      card_X₁ := (card_map_eq _ φ₁ T.inj₁).trans (card_uSub.trans hSet.card₁)
      card_X₁' := (card_map_eq _ φ₁ T.inj₁).trans (card_lSub.trans hSet.card₁)
      card_X₂ := (card_map_eq _ φ₂ T.inj₂).trans (card_uSub.trans hSet.card₂)
      card_X₂' := (card_map_eq _ φ₂ T.inj₂).trans (card_lSub.trans hSet.card₂)
      X₁_comm := map_comm_of φ₁ uSub_comm
      X₁'_comm := map_comm_of φ₁ lSub_comm
      X₂_comm := map_comm_of φ₂ uSub_comm
      X₂'_comm := map_comm_of φ₂ lSub_comm
      X₁_exp := by
        have hp : q₁.minFac = ringChar F₁ := by rw [← hSet.card₁]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₁ _ (fun a ha => by rw [hp]; exact pow_char_uSub _ a ha)
      X₁'_exp := by
        have hp : q₁.minFac = ringChar F₁ := by rw [← hSet.card₁]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₁ _ (fun a ha => by rw [hp]; exact pow_char_lSub _ a ha)
      X₂_exp := by
        have hp : q₂.minFac = ringChar F₂ := by rw [← hSet.card₂]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₂ _ (fun a ha => by rw [hp]; exact pow_char_uSub _ a ha)
      X₂'_exp := by
        have hp : q₂.minFac = ringChar F₂ := by rw [← hSet.card₂]; exact minFac_card_eq_ringChar
        exact map_pow_eq_one φ₂ _ (fun a ha => by rw [hp]; exact pow_char_lSub _ a ha)
      X₁_ne := fun h => uSub_ne_lSub (Subgroup.map_injective T.inj₁ h)
      X₂_ne := fun h => uSub_ne_lSub (Subgroup.map_injective T.inj₂ h)
      H_comm := T.Hg_comm
      z_mem_H := Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨negOne F₁, negOne_mem_tSub, rfl⟩)
      u_mem_H := hu_mem
      H₁_eq := by
        show (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range = centralizer ({u} : Set G) ⊓ φ₁.range
        ext x
        constructor
        · intro hx
          have hx' := hx
          rw [T.Hg_inf_K₁] at hx'
          obtain ⟨a, ha, rfl⟩ := hx'
          refine ⟨Subgroup.mem_centralizer_iff.2 (fun h hh => ?_), hx.2⟩
          rw [Set.mem_singleton_iff.1 hh]
          exact (hcentr₁ a).2 ha
        · rintro ⟨hxc, y, rfl⟩
          have hy : y ∈ tSub F₁ := (hcentr₁ y).1 (Subgroup.mem_centralizer_iff.1 hxc u rfl)
          rw [T.Hg_inf_K₁]
          exact ⟨y, hy, rfl⟩
      H₂_eq := by
        show (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range = centralizer ({u} : Set G) ⊓ φ₂.range
        ext x
        constructor
        · intro hx
          have hx' := hx
          rw [T.Hg_inf_K₂] at hx'
          obtain ⟨a, ha, rfl⟩ := hx'
          refine ⟨Subgroup.mem_centralizer_iff.2 (fun h hh => ?_), hx.2⟩
          rw [Set.mem_singleton_iff.1 hh]
          exact (hcentr₂ a).2 ha
        · rintro ⟨hxc, y, rfl⟩
          have hy : y ∈ tSub F₂ := (hcentr₂ y).1 (Subgroup.mem_centralizer_iff.1 hxc u rfl)
          rw [T.Hg_inf_K₂]
          exact ⟨y, hy, rfl⟩
      H₁_cyc := by
        show IsCyclic ↥((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range)
        rw [T.Hg_inf_K₁]
        exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ T.inj₁)).1 isCyclic_tSub
      H₂_cyc := by
        show IsCyclic ↥((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range)
        rw [T.Hg_inf_K₂]
        exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ T.inj₂)).1 isCyclic_tSub
      card_H_K₁ := by
        show Nat.card ↥((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range) = q₁ - 1
        rw [T.Hg_inf_K₁, card_map_eq _ φ₁ T.inj₁, card_tSub, hSet.card₁]
      card_H_K₂ := by
        show Nat.card ↥((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range) = q₂ - 1
        rw [T.Hg_inf_K₂, card_map_eq _ φ₂ T.inj₂, card_tSub, hSet.card₂]
      H_idx := by
        show (((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range) ⊔
          ((Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range)).relIndex
            (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) = 2
        rw [T.Hg_inf_K₁, T.Hg_inf_K₂]
        exact T.Hm_relIndex
      H_le := by
        show Hm φ₁ φ₂ ⊔ Subgroup.zpowers s ≤ φ₁.range ⊔ φ₂.range ⊔ S
        refine sup_le (le_trans TorusData.Hm_le_K le_sup_left) ?_
        rw [Subgroup.zpowers_le, hKS]
        exact hsC
      H_not_le_K := fun hle => T.s_not_mem (hle TorusData.s_mem_Hg)
      H_norm_X₁ := T.conj_Hg_map₁ (uSub F₁) tSub_normalizes_uSub (slConj_diag_uSub 1 d₁)
      H_norm_X₁' := T.conj_Hg_map₁ (lSub F₁) tSub_normalizes_lSub (slConj_diag_lSub 1 d₁)
      H_norm_X₂ := T.conj_Hg_map₂ (uSub F₂) tSub_normalizes_uSub (slConj_diag_uSub 1 d₂)
      H_norm_X₂' := T.conj_Hg_map₂ (lSub F₂) tSub_normalizes_lSub (slConj_diag_lSub 1 d₂)
      H_fpf₁ := fun h hh hz => T.fpf₁ h hh hz
      H_fpf₁' := fun h hh hz => T.fpf₁' h hh hz
      H_fpf₂ := fun h hh hz => T.fpf₂ h hh hz
      H_fpf₂' := fun h hh hz => T.fpf₂' h hh hz
      w₁_mem := ⟨_, rfl⟩
      w₂_mem := ⟨_, rfl⟩
      w₁_sq := hww₁
      w₂_sq := hww₂
      w₁_swap := map_conj_mem φ₁ _ _ hwconj₁ (fun x hx => sl2W_conj_uSub x hx)
      w₁_swap' := map_conj_mem φ₁ _ _ hwconj₁ (fun x hx => sl2W_conj_lSub x hx)
      w₂_swap := map_conj_mem φ₂ _ _ hwconj₂ (fun x hx => sl2W_conj_uSub x hx)
      w₂_swap' := map_conj_mem φ₂ _ _ hwconj₂ (fun x hx => sl2W_conj_lSub x hx)
      w₁_inv := fun h hh => by
        have hh' : h ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₁.range := hh
        rw [T.Hg_inf_K₁] at hh'
        exact map_conj_inv φ₁ _ (fun x => sl2W F₁ * x * (sl2W F₁)⁻¹) hwconj₁
          sl2W_inv_tSub h hh'
      w₂_inv := fun h hh => by
        have hh' : h ∈ (Hm φ₁ φ₂ ⊔ Subgroup.zpowers s) ⊓ φ₂.range := hh
        rw [T.Hg_inf_K₂] at hh'
        exact map_conj_inv φ₂ _ (fun x => sl2W F₂ * x * (sl2W F₂)⁻¹) hwconj₂
          sl2W_inv_tSub h hh'
      w₁_u := hwwu _ _ hww₁ hzz hzw₁ hzu hw₁u
      w₂_u := hwwu _ _ hww₂ hzz hzw₂ hzu hw₂u
      w₁_normH := T.w₁_mem_normalizer
      w₂_normH := T.w₂_mem_normalizer
      w₀_inv := T.w₀_conj_Hg
      w₀_cent := by
        have h0 : u * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * u⁻¹ =
            (φ₁ (sl2W F₁))⁻¹ * (φ₂ (sl2W F₂))⁻¹ := by
          calc u * (φ₁ (sl2W F₁) * φ₂ (sl2W F₂)) * u⁻¹
              = (u * φ₁ (sl2W F₁) * u⁻¹) * (u * φ₂ (sl2W F₂) * u⁻¹) := by group
            _ = _ := by rw [hw₁u, hw₂u]
        have hc : Commute (φ₁ (sl2W F₁)) (φ₂ (sl2W F₂)) := hcomm₁₂
        have hinv : (φ₁ (sl2W F₁) * φ₂ (sl2W F₂))⁻¹ = φ₁ (sl2W F₁) * φ₂ (sl2W F₂) :=
          inv_eq_of_mul_eq_one_right hw₀sq
        have h1 : (φ₁ (sl2W F₁))⁻¹ * (φ₂ (sl2W F₂))⁻¹ = φ₁ (sl2W F₁) * φ₂ (sl2W F₂) := by
          rw [hc.inv_inv.eq, ← mul_inv_rev, hinv]
        exact (mul_inv_eq_iff_eq_mul.1 (h0.trans h1)).symm
      u_inv_X₁ := map_conj_inv φ₁ u _ hu₁ slConj_dNeg_uSub
      u_inv_X₁' := map_conj_inv φ₁ u _ hu₁ slConj_dNeg_lSub
      u_inv_X₂ := map_conj_inv φ₂ u _ hu₂ slConj_dNeg_uSub
      u_inv_X₂' := map_conj_inv φ₂ u _ hu₂ slConj_dNeg_lSub }

end Loc5Core

section Existence

variable {G : Type} [Group G]

theorem exists_coords0 {z t : G} {K : Subgroup G} {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (hz : orderOf z = 2) (hzK : z ∈ K) (htt : t * t = 1) (e : ↥K ≃* SL2 F) (g : GL (Fin 2) F)
    (hact : ActsAsConj t K e g) :
    ∃ φ : SL2 F →* G, Function.Injective φ ∧ φ.range = K ∧ φ (negOne F) = z ∧
      (∀ x, t * φ x * t⁻¹ = φ (slConj g x)) ∧ (∀ x, slConj (g * g) x = x) := by
  let φ : SL2 F →* G := (Subgroup.subtype K).comp e.symm.toMonoidHom
  have hφ : ∀ x, φ x = ((e.symm x : ↥K) : G) := fun x => rfl
  have hinj : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = K := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [hφ]⟩
  have hτ : ∀ x, t * φ x * t⁻¹ = φ (slConj g x) := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hact (e.symm x)
    have hy : y = e.symm (slConj g x) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hy2, MulEquiv.apply_symm_apply]
      rfl
    rw [hφ, hφ, ← hy, hy1]
  have hsq : ∀ x, slConj (g * g) x = x := by
    intro x
    apply hinj
    rw [slConj_mul, ← hτ, ← hτ]
    have : t * (t * φ x * t⁻¹) * t⁻¹ = (t * t) * φ x * (t * t)⁻¹ := by group
    rw [this, htt]; group
  have hzφ : φ (negOne F) = z := by
    obtain ⟨y, hy⟩ : ∃ y : SL2 F, φ y = z := ⟨e ⟨z, hzK⟩, by simp [hφ]⟩
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz, sq] at this; exact this
    have hyy : y * y = 1 := by
      apply hinj
      rw [map_mul, hy, hzz, map_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [map_one] at hy
      rw [← hy, orderOf_one] at hz
      omega
    rw [← hy, eq_negOne_of_involution h2 hyy hy1]
  exact ⟨φ, hinj, hrange, hzφ, hτ, hsq⟩

theorem coords_B {z t : G} {K : Subgroup G} {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (hq : Nat.card F % 4 = 3) (φ : SL2 F →* G) (hinj : Function.Injective φ) (hrange : φ.range = K)
    (hz : φ (negOne F) = z) (g : GL (Fin 2) F)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F))
    (hτ : ∀ x, t * φ x * t⁻¹ = φ (slConj g x)) (hsq : ∀ x, slConj (g * g) x = x) :
    ∃ φ' : SL2 F →* G, Function.Injective φ' ∧ φ'.range = K ∧ φ' (negOne F) = z ∧
      (∀ x, t * φ' x * t⁻¹ = φ' (slConj (dNeg F) x)) := by
  have hsplit : IsSquare (-((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) := by
    have := isSquare_mul_of_not_isSquare h2 (not_isSquare_negOne hq) hns
    rwa [neg_one_mul] at this
  obtain ⟨P, hP⟩ := exists_slConj_split h2 g hns hsq hsplit
  refine ⟨φ.comp (slConj P⁻¹), hinj.comp (slConj_injective _), ?_, ?_, ?_⟩
  · rw [← hrange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := slConj_surjective P⁻¹ y
      exact ⟨y', by simp [hy']⟩
  · simp [slConj_negOne, hz]
  · intro x
    have e1 : slConj (dNeg F) x = slConj (P * g * P⁻¹) x := (hP x).symm
    simp only [MonoidHom.comp_apply]
    rw [hτ, ← slConj_mul, e1, ← slConj_mul]
    congr 2
    group

end Existence

section Final

variable {G : Type} [Group G]

theorem exists_P51Coord {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hmod : q₁ % 4 = q₂ % 4) :
    ∃ u : G, Nonempty (P51Coord z t u K₁ K₂ F₁ F₂) := by
  have := hSet.finite₁
  have := hSet.finite₂
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card (by rw [hSet.card₁]; exact hSet.odd₁)
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card (by rw [hSet.card₂]; exact hSet.odd₂)
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hzord, sq] at this; exact this
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨φ₁, inj₁, range₁, z₁, hτ₁, hsq₁⟩ :=
    exists_coords0 h2₁ hzord hSet.z_mem₁ hRem.sq e₁ g₁ hact₁
  obtain ⟨φ₂, inj₂, range₂, z₂, hτ₂, hsq₂⟩ :=
    exists_coords0 h2₂ hzord hSet.z_mem₂ hRem.sq e₂ g₂ hact₂
  have hc : ∀ (a : SL2 F₁) (b : SL2 F₂), φ₁ a * φ₂ b = φ₂ b * φ₁ a := fun a b =>
    hSet.comm _ (range₁.le ⟨a, rfl⟩) _ (range₂.le ⟨b, rfl⟩)
  have hq₁ : q₁ % 4 = 1 ∨ q₁ % 4 = 3 := by
    obtain ⟨k, hk⟩ := hSet.odd₁
    omega
  rcases hq₁ with h1 | h3
  ·
    have hF₁ : Nat.card F₁ % 4 = 1 := by rw [hSet.card₁]; exact h1
    have hF₂ : Nat.card F₂ % 4 = 1 := by rw [hSet.card₂, ← hmod]; exact h1
    obtain ⟨ι₁, hι₁⟩ := exists_unit_sqrt_negOne hF₁
    obtain ⟨ι₂, hι₂⟩ := exists_unit_sqrt_negOne hF₂
    refine ⟨φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂), ⟨?_⟩⟩
    refine
      { φ₁ := φ₁, φ₂ := φ₂, inj₁ := inj₁, inj₂ := inj₂, range₁ := range₁, range₂ := range₂,
        z₁ := z₁, z₂ := z₂, τ₁ := g₁, τ₂ := g₂, hτ₁ := hτ₁, hτ₂ := hτ₂, ns₁ := hns₁, ns₂ := hns₂,
        hu₁ := ?_, hu₂ := ?_, hu2 := ?_,
        hcase := Or.inl ⟨sl2D ι₁, sl2D_mem_tSub _, sl2D ι₂, sl2D_mem_tSub _, rfl⟩ }
    · intro x
      have e : (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) * φ₁ x * (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂))⁻¹ =
          φ₁ (sl2D ι₁) * (φ₂ (sl2D ι₂) * φ₁ x * (φ₂ (sl2D ι₂))⁻¹) * (φ₁ (sl2D ι₁))⁻¹ := by group
      have hcc : φ₂ (sl2D ι₂) * φ₁ x * (φ₂ (sl2D ι₂))⁻¹ = φ₁ x := by
        rw [← hc x (sl2D ι₂)]; group
      rw [e, hcc, ← slConj_sqrt_negOne ι₁ hι₁ x]
      simp [map_mul, map_inv, mul_assoc]
    · intro x
      have e : (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) * φ₂ x * (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂))⁻¹ =
          φ₁ (sl2D ι₁) * (φ₂ (sl2D ι₂ * x * (sl2D ι₂)⁻¹)) * (φ₁ (sl2D ι₁))⁻¹ := by
        simp [map_mul, map_inv, mul_assoc]
      have hcc : φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂ * x * (sl2D ι₂)⁻¹) * (φ₁ (sl2D ι₁))⁻¹ =
          φ₂ (sl2D ι₂ * x * (sl2D ι₂)⁻¹) := by
        rw [hc]; group
      rw [e, hcc, slConj_sqrt_negOne ι₂ hι₂ x]
    · have e : (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) * (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) =
          φ₁ (sl2D ι₁ * sl2D ι₁) * φ₂ (sl2D ι₂ * sl2D ι₂) := by
        have := hc (sl2D ι₁) (sl2D ι₂)
        calc (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) * (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂))
            = φ₁ (sl2D ι₁) * (φ₂ (sl2D ι₂) * φ₁ (sl2D ι₁)) * φ₂ (sl2D ι₂) := by group
          _ = φ₁ (sl2D ι₁) * (φ₁ (sl2D ι₁) * φ₂ (sl2D ι₂)) * φ₂ (sl2D ι₂) := by rw [this]
          _ = _ := by simp [map_mul, mul_assoc]
      rw [e, sl2D_sq_of_sqrt ι₁ hι₁, sl2D_sq_of_sqrt ι₂ hι₂, z₁, z₂, hzz]
  ·
    have hF₁ : Nat.card F₁ % 4 = 3 := by rw [hSet.card₁]; exact h3
    have hF₂ : Nat.card F₂ % 4 = 3 := by rw [hSet.card₂, ← hmod]; exact h3
    obtain ⟨ψ₁, jn₁, rg₁, zz₁, ht₁⟩ :=
      coords_B h2₁ hF₁ φ₁ inj₁ range₁ z₁ g₁ hns₁ hτ₁ hsq₁
    obtain ⟨ψ₂, jn₂, rg₂, zz₂, ht₂⟩ :=
      coords_B h2₂ hF₂ φ₂ inj₂ range₂ z₂ g₂ hns₂ hτ₂ hsq₂
    have hdet₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det (dNeg F₁) : F₁ˣ) : F₁) := by
      have : ((Matrix.GeneralLinearGroup.det (dNeg F₁) : F₁ˣ) : F₁) = -1 := by
        unfold dNeg; rw [t2C_det_diagGL]; simp
      rw [this]; exact not_isSquare_negOne hF₁
    have hdet₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det (dNeg F₂) : F₂ˣ) : F₂) := by
      have : ((Matrix.GeneralLinearGroup.det (dNeg F₂) : F₂ˣ) : F₂) = -1 := by
        unfold dNeg; rw [t2C_det_diagGL]; simp
      rw [this]; exact not_isSquare_negOne hF₂
    refine ⟨t, ⟨?_⟩⟩
    exact
      { φ₁ := ψ₁
        φ₂ := ψ₂
        inj₁ := jn₁
        inj₂ := jn₂
        range₁ := rg₁
        range₂ := rg₂
        z₁ := zz₁
        z₂ := zz₂
        τ₁ := dNeg F₁
        τ₂ := dNeg F₂
        hτ₁ := ht₁
        hτ₂ := ht₂
        ns₁ := hdet₁
        ns₂ := hdet₂
        hu₁ := ht₁
        hu₂ := ht₂
        hu2 := hRem.sq
        hcase := Or.inr ⟨rfl, rfl, rfl⟩ }

variable [Finite G]

theorem loc5_of_coord {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t u : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (C : P51Coord z t u K₁ K₂ F₁ F₂) :
    ∃ N : T2N1 G, N.z = z ∧ N.K₁ = K₁ ∧ N.K₂ = K₂ ∧ N.q₁ = q₁ ∧ N.q₂ = q₂ ∧ Ch6Loc5 N u ∧
      Ch6Coord N := by
  have hzord : orderOf z = 2 := hSet.central.1
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hzord, sq] at this; exact this
  have htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hRem.gen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨s, T, hu_mem, hsC⟩ :=
    C.torus_mem hSet.comm hSet.inter_eq.le hzz hRem.sq hSet.le_residual htC
  rcases C with ⟨φ₁, φ₂, inj₁, inj₂, range₁, range₂, z₁, z₂, τ₁, τ₂, hτ₁, hτ₂, ns₁, ns₂, hu₁, hu₂,
    hu2, hcase⟩
  subst range₁ range₂ z₁
  exact loc5_core φ₁ φ₂ s u _ _ hSet T hu₁ hu₂ hu2 hu_mem hsC

theorem ch6T2P51 : Ch6T2P51 := by
  intro G _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem hmod
  obtain ⟨u, ⟨C⟩⟩ := exists_P51Coord hSet hRem hmod
  obtain ⟨N, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ := loc5_of_coord hSet hRem C
  exact ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩

end Final

end CFSG.GH74.GLS.Stage4.Rest
