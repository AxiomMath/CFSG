module

public import CFSG.GH74.GLS.SP.Local.SPLWt2
public import CFSG.GH74.GLS.SP.Local.SPLJ
public import CFSG.GH74.GLS.SP.Local.SPLKernel

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def kernelOf (H A : Subgroup G) : Subgroup G := centralizer (A : Set G) ⊓ H

theorem mem_kernelOf_iff {H A : Subgroup G} {h : G} :
    h ∈ kernelOf H A ↔ h ∈ H ∧ ∀ a ∈ A, h * a = a * h := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun a ha => (mem_centralizer_iff.mp h1 a ha).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_centralizer_iff.mpr fun a ha => (h2 a ha).symm, h1⟩

omit [Group G] in
theorem exists_ne_one_of_two_le {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (h : 2 ≤ Nat.card ↥A) : ∃ a ∈ A, a ≠ 1 := by
  by_contra hcon
  have : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    by_contra hne
    exact hcon ⟨a, ha, fun h => hne (Subgroup.mem_bot.mpr h)⟩
  rw [this, Subgroup.card_bot] at h
  omega

omit [Group G] in
theorem eq_one_of_inv_eq_self {G : Type} [Group G] {p : ℕ} (hp : Odd p) {x : G} (hx : x ^ p = 1)
    (h : x⁻¹ = x) : x = 1 := by
  obtain ⟨m, rfl⟩ := hp
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [h]
      _ = 1 := by group
  have h3 : x ^ 2 = 1 := by rw [pow_two]; exact h2
  rw [pow_succ, pow_mul, h3, one_pow, one_mul] at hx
  exact hx

section Kernels

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem z_mem_ker₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.z ∈ kernelOf D.H D.X₁ := by
  refine mem_kernelOf_iff.mpr ⟨z_mem_H D h1, fun x hx => ?_⟩
  exact (hs.comps.cz₁ (h3.X₁_le hx)).symm

theorem z_mem_ker₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.z ∈ kernelOf D.H D.X₂ := by
  refine mem_kernelOf_iff.mpr ⟨z_mem_H D h1, fun x hx => ?_⟩
  exact (hs.comps.cz₂ (X₂_le_K₂ D hs h3.toSPL3X hx)).symm

theorem z_inv_X₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∀ x ∈ D.X₄, D.z * x * D.z⁻¹ = x⁻¹ := by
  intro x hx
  rw [SPLNot3.X₄, mem_conjBy_iff] at hx
  have h := h3.z_X₃ _ hx
  have hzw : D.z * D.w₁ = D.w₁ * D.z := (w₁_comm_z D hs h1).symm
  have hc : D.w₁⁻¹ * D.z * D.w₁ = D.z := by
    calc D.w₁⁻¹ * D.z * D.w₁ = D.w₁⁻¹ * (D.z * D.w₁) := by group
      _ = D.z := by rw [hzw]; group
  have hc' : D.w₁⁻¹ * D.z⁻¹ * D.w₁ = D.z⁻¹ := by
    have := congrArg (fun y => y⁻¹) hc
    simpa [mul_assoc] using this
  calc D.z * x * D.z⁻¹ = (D.w₁⁻¹ * D.z * D.w₁) * x * (D.w₁⁻¹ * D.z⁻¹ * D.w₁) := by rw [hc, hc']
    _ = D.w₁⁻¹ * (D.z * (D.w₁ * x * D.w₁⁻¹) * D.z⁻¹) * D.w₁ := by group
    _ = D.w₁⁻¹ * (D.w₁ * x * D.w₁⁻¹)⁻¹ * D.w₁ := by rw [h]
    _ = x⁻¹ := by group

theorem z_not_mem_ker₃ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    D.z ∉ kernelOf D.H D.X₃ := by
  intro hz
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_two_le D.X₃ (by
    rw [X₃_card D h3]; have := hs.q_ge; omega)
  have hxz := (mem_kernelOf_iff.mp hz).2 x hx
  have h1' := h3.z_X₃ x hx
  have : D.z * x * D.z⁻¹ = x := by rw [hxz]; group
  rw [this] at h1'
  exact hx1 (eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) ((X₃_eab D h3).2 x hx)
    h1'.symm)

theorem z_not_mem_ker₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.z ∉ kernelOf D.H D.X₄ := by
  intro hz
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_two_le D.X₄ (by
    rw [X₄_card D h3]; have := hs.q_ge; omega)
  have hxz := (mem_kernelOf_iff.mp hz).2 x hx
  have h1' := z_inv_X₄ D hs h1 h3 x hx
  have : D.z * x * D.z⁻¹ = x := by rw [hxz]; group
  rw [this] at h1'
  exact hx1 (eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) ((X₄_eab D h3).2 x hx)
    h1'.symm)


omit [Finite G] in
theorem centralizer_K₁_le_zpowers (hs : SPLSetup D.toSPLNot0) {k : G} (hk : k ∈ D.K₁)
    (hc : ∀ x ∈ D.K₁, k * x = x * k) : k ∈ zpowers D.z := by
  have : (⟨k, hk⟩ : ↥D.K₁) ∈ center ↥D.K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  exact (mem_center_K₁_iff D hs _).mp this

theorem h₁_not_mem_ker₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.h₁ ∉ kernelOf D.H D.X₁ := by
  intro hker
  have hX₁ : ∀ x ∈ D.X₁, D.h₁ * x = x * D.h₁ := (mem_kernelOf_iff.mp hker).2
  have hX₁' : ∀ x ∈ D.X₁', D.h₁ * x = x * D.h₁ := by
    intro x hx
    rw [h3.X₁'_eq, mem_conjBy_iff] at hx
    have e1 : D.w₁ * D.h₁ * D.w₁⁻¹ = D.h₁⁻¹ := h1.w₁_inv _ (mem_zpowers _)
    have h := hX₁ _ hx
    have hy : D.h₁⁻¹ * (D.w₁ * x * D.w₁⁻¹) = (D.w₁ * x * D.w₁⁻¹) * D.h₁⁻¹ := by
      have : Commute D.h₁ (D.w₁ * x * D.w₁⁻¹) := h
      exact (this.inv_left).eq
    calc D.h₁ * x = D.w₁⁻¹ * ((D.w₁ * D.h₁ * D.w₁⁻¹) * (D.w₁ * x * D.w₁⁻¹)) * D.w₁ := by group
      _ = D.w₁⁻¹ * (D.h₁⁻¹ * (D.w₁ * x * D.w₁⁻¹)) * D.w₁ := by rw [e1]
      _ = D.w₁⁻¹ * ((D.w₁ * x * D.w₁⁻¹) * D.h₁⁻¹) * D.w₁ := by rw [hy]
      _ = D.w₁⁻¹ * ((D.w₁ * x * D.w₁⁻¹) * (D.w₁ * D.h₁ * D.w₁⁻¹)) * D.w₁ := by rw [e1]
      _ = x * D.h₁ := by group
  have hK : ∀ x ∈ D.K₁, D.h₁ * x = x * D.h₁ := by
    intro x hx
    have hle : D.K₁ ≤ centralizer ({D.h₁} : Set G) := by
      rw [h3.K₁_eq]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact mem_centralizer_singleton_iff.mpr (hX₁ y hy).symm
      · exact mem_centralizer_singleton_iff.mpr (hX₁' y hy).symm
    exact (mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hz := centralizer_K₁_le_zpowers D hs h1.h₁_mem (fun x hx => hK x hx)
  rcases eq_one_or_z hs hz with h | h
  · have := h1.h₁_ord
    rw [h, orderOf_one] at this
    have := hs.q_ge
    omega
  · have := h1.h₁_ord
    rw [h, hs.syl.z_inv] at this
    have := hs.q_ge
    omega

theorem h₁_mem_ker₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.h₁ ∈ kernelOf D.H D.X₂ := by
  refine mem_kernelOf_iff.mpr ⟨H₁_le_H D (mem_zpowers _), fun x hx => ?_⟩
  exact hs.comps.comm D.h₁ h1.h₁_mem x (X₂_le_K₂ D hs h3.toSPL3X hx)

theorem h₂_mem_ker₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.h₂ ∈ kernelOf D.H D.X₁ := by
  refine mem_kernelOf_iff.mpr ⟨H₂_le_H D (mem_zpowers _), fun x hx => ?_⟩
  exact (hs.comps.comm x (h3.X₁_le hx) D.h₂ (h₂_mem D hs h1)).symm

theorem h₂_not_mem_ker₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.h₂ ∉ kernelOf D.H D.X₂ := by
  intro hker
  apply h₁_not_mem_ker₁ D hs h1 h3
  refine mem_kernelOf_iff.mpr ⟨H₁_le_H D (mem_zpowers _), fun x hx => ?_⟩
  have htt := t_inv D hs
  have hx' : D.t * x * D.t ∈ D.X₂ := by
    show D.t * x * D.t ∈ conjBy D.t D.X₁
    rw [mem_conjBy_iff, htt]
    have : D.t * (D.t * x * D.t) * D.t = x := by
      have h2 := t_mul_t D hs
      calc D.t * (D.t * x * D.t) * D.t = (D.t * D.t) * x * (D.t * D.t) := by group
        _ = x := by rw [h2]; group
    rw [this]; exact hx
  have h := (mem_kernelOf_iff.mp hker).2 _ hx'
  have e : D.h₂ = D.t * D.h₁ * D.t := by
    show D.t * D.h₁ * D.t⁻¹ = D.t * D.h₁ * D.t
    rw [htt]
  rw [e] at h
  have h2 := t_mul_t D hs
  calc D.h₁ * x = D.t * (D.t * D.h₁ * D.t * (D.t * x * D.t)) * D.t := by
        calc D.h₁ * x = (D.t * D.t) * D.h₁ * (D.t * D.t) * x * (D.t * D.t) := by
              rw [h2]; group
          _ = _ := by group
    _ = D.t * ((D.t * x * D.t) * (D.t * D.h₁ * D.t)) * D.t := by rw [h]
    _ = x * D.h₁ := by
        calc D.t * ((D.t * x * D.t) * (D.t * D.h₁ * D.t)) * D.t
            = (D.t * D.t) * x * (D.t * D.t) * D.h₁ * (D.t * D.t) := by group
          _ = x * D.h₁ := by rw [h2]; group

theorem t_inv_X₃ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    ∀ x ∈ D.X₃, D.t * x * D.t = x⁻¹ := by
  intro x hx
  have ht := t_mul_t D hs
  have htt := t_inv D hs
  have hcomm : ∀ a ∈ D.X₁, ∀ b ∈ conjBy D.t D.X₁, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a (h3.X₁_le ha) b (X₂_le_K₂ D hs h3.toSPL3X hb)
  obtain ⟨φ, hφ, -, hinvY, -⟩ := Y1_spec ht h3.X₁_eab hcomm (X₁_inf_X₂ D hs h3)
  have hY₁ : D.Y₁ = ⁅D.X₁ ⊔ conjBy D.t D.X₁, zpowers D.t⁆ := h3.Y₁_eq
  have hY : ∀ y ∈ D.Y₁, D.t * y * D.t⁻¹ = y⁻¹ := fun y hy => hinvY y (by rw [← hY₁]; exact hy)
  rw [SPLNot3.X₃, mem_conjBy_iff] at hx
  have h := hY _ hx
  have hat : D.t * D.a = D.a * D.t := (mem_centralizer_singleton_iff.mp h3.a_mem).symm
  have hta : D.a⁻¹ * D.t * D.a = D.t := by
    calc D.a⁻¹ * D.t * D.a = D.a⁻¹ * (D.t * D.a) := by group
      _ = D.t := by rw [hat]; group
  have hta' : D.a⁻¹ * D.t⁻¹ * D.a = D.t⁻¹ := by
    have := congrArg (fun y => y⁻¹) hta
    simpa [mul_assoc] using this
  calc D.t * x * D.t = D.t * x * D.t⁻¹ := by rw [htt]
    _ = (D.a⁻¹ * D.t * D.a) * x * (D.a⁻¹ * D.t⁻¹ * D.a) := by rw [hta, hta']
    _ = D.a⁻¹ * (D.t * (D.a * x * D.a⁻¹) * D.t⁻¹) * D.a := by group
    _ = D.a⁻¹ * (D.a * x * D.a⁻¹)⁻¹ * D.a := by rw [h]
    _ = x⁻¹ := by group


theorem comm_t_mem_ker₃ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    {h : G} (hh : h ∈ D.H) : h * (D.t * h * D.t⁻¹)⁻¹ ∈ kernelOf D.H D.X₃ := by
  have htt := t_inv D hs
  refine mem_kernelOf_iff.mpr ⟨?_, fun x hx => ?_⟩
  · have := t_norm_H D hs h1 h hh
    exact D.H.mul_mem hh (D.H.inv_mem this)
  · have hy : h⁻¹ * x⁻¹ * h ∈ D.X₃ := by
      have := h3.H_X₃ h⁻¹ (D.H.inv_mem hh) x⁻¹ (D.X₃.inv_mem hx)
      simpa using this
    have hty := t_inv_X₃ D hs h3 _ hy
    have hx1 := t_inv_X₃ D hs h3 x hx
    have htx : D.t * x = x⁻¹ * D.t := by
      calc D.t * x = (D.t * x * D.t) * D.t⁻¹ := by group
        _ = x⁻¹ * D.t := by rw [hx1, htt]
    have hty' : D.t * (h⁻¹ * x⁻¹ * h) = (h⁻¹ * x⁻¹ * h)⁻¹ * D.t := by
      calc D.t * (h⁻¹ * x⁻¹ * h) = (D.t * (h⁻¹ * x⁻¹ * h) * D.t) * D.t⁻¹ := by group
        _ = (h⁻¹ * x⁻¹ * h)⁻¹ * D.t := by rw [hty, htt]
    have hinv : (D.t * h * D.t⁻¹)⁻¹ = D.t * h⁻¹ * D.t⁻¹ := by group
    rw [hinv, htt]
    calc h * (D.t * h⁻¹ * D.t) * x = h * D.t * h⁻¹ * (D.t * x) := by group
      _ = h * D.t * h⁻¹ * (x⁻¹ * D.t) := by rw [htx]
      _ = h * (D.t * (h⁻¹ * x⁻¹ * h)) * h⁻¹ * D.t := by group
      _ = h * ((h⁻¹ * x⁻¹ * h)⁻¹ * D.t) * h⁻¹ * D.t := by rw [hty']
      _ = x * (h * (D.t * h⁻¹ * D.t)) := by group

omit [Finite G] in
theorem centralizes_conjBy_iff {g c : G} {A : Subgroup G} :
    (∀ x ∈ conjBy g A, c * x = x * c) ↔ ∀ a ∈ A, (g * c * g⁻¹) * a = a * (g * c * g⁻¹) := by
  constructor
  · intro h a ha
    have hx : g⁻¹ * a * g ∈ conjBy g A := by
      rw [mem_conjBy_iff]
      have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [this]; exact ha
    have := h _ hx
    calc (g * c * g⁻¹) * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [this]
      _ = a * (g * c * g⁻¹) := by group
  · intro h x hx
    rw [mem_conjBy_iff] at hx
    have := h _ hx
    calc c * x = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by rw [this]
      _ = x * c := by group

theorem mem_ker₄_iff (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) {h : G} (hh : h ∈ D.H) :
    h ∈ kernelOf D.H D.X₄ ↔ D.w₁ * h * D.w₁⁻¹ ∈ kernelOf D.H D.X₃ := by
  have hH : D.w₁ * h * D.w₁⁻¹ ∈ D.H := w₁_norm_H D hs h1 h hh
  constructor
  · intro hk
    refine mem_kernelOf_iff.mpr ⟨hH, ?_⟩
    exact centralizes_conjBy_iff.mp (mem_kernelOf_iff.mp hk).2
  · intro hk
    refine mem_kernelOf_iff.mpr ⟨hh, ?_⟩
    exact centralizes_conjBy_iff.mpr (mem_kernelOf_iff.mp hk).2

theorem H₀_le_ker₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.H₀ ≤ kernelOf D.H D.X₄ := by
  have hg₀ : D.h₁ * D.h₂ ∈ D.H := SPLNot1.H₀_le_H D.toSPLNot1 (mem_zpowers _)
  rw [show D.H₀ = zpowers (D.h₁ * D.h₂) from rfl, zpowers_le]
  rw [mem_ker₄_iff D hs h1 hg₀]
  have e : D.w₁ * (D.h₁ * D.h₂) * D.w₁⁻¹ = D.h₁⁻¹ * (D.t * D.h₁⁻¹ * D.t⁻¹)⁻¹ := by
    have e1 : D.w₁ * D.h₁ * D.w₁⁻¹ = D.h₁⁻¹ := h1.w₁_inv _ (mem_zpowers _)
    have e2 : D.w₁ * D.h₂ * D.w₁⁻¹ = D.h₂ := by
      have := hs.comps.comm _ h1.w₁_mem _ (h₂_mem D hs h1)
      calc D.w₁ * D.h₂ * D.w₁⁻¹ = D.h₂ * D.w₁ * D.w₁⁻¹ := by rw [this]
        _ = D.h₂ := by group
    calc D.w₁ * (D.h₁ * D.h₂) * D.w₁⁻¹ = (D.w₁ * D.h₁ * D.w₁⁻¹) * (D.w₁ * D.h₂ * D.w₁⁻¹) := by group
      _ = D.h₁⁻¹ * D.h₂ := by rw [e1, e2]
      _ = _ := by
        show D.h₁⁻¹ * D.h₂ = D.h₁⁻¹ * (D.t * D.h₁⁻¹ * D.t⁻¹)⁻¹
        unfold SPLNot1.h₂
        group
  rw [e]
  exact comm_t_mem_ker₃ D hs h1 h3 (D.H.inv_mem (H₁_le_H D (mem_zpowers _)))

theorem K₁_le_M₂ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.K₁ ≤ D.M₂ := by
  intro k hk
  rw [SPLNot3.M₂, mem_normalizer_iff]
  intro y
  have hconj : ∀ x ∈ D.X₂, k * x * k⁻¹ = x := by
    intro x hx
    rw [hs.comps.comm k hk x (X₂_le_K₂ D hs h3 hx)]
    group
  constructor
  · intro hy
    rw [hconj y hy]
    exact hy
  · intro hy
    have hcc := hs.comps.comm k hk _ (X₂_le_K₂ D hs h3 hy)
    have h1 : k * (k * y * k⁻¹) = k * y := by
      rw [hcc]
      group
    have h2 : k * y * k⁻¹ = y := mul_left_cancel h1
    rwa [h2] at hy

theorem K₁_normalizes_R₂ (hs : SPLSetup D.toSPLNot0) (hX : SPL3X D)
    (hRn : D.M₂ ≤ normalizer (D.R₂ : Set G)) :
    ∀ k ∈ D.K₁, ∀ r ∈ D.R₂, k * r * k⁻¹ ∈ D.R₂ := by
  intro k hk r hr
  exact (mem_normalizer_iff.mp (hRn (K₁_le_M₂ D hs hX hk)) r).mp hr

theorem K₁_normalizes_X₂ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    ∀ k ∈ D.K₁, ∀ y ∈ D.X₂, k * y * k⁻¹ ∈ D.X₂ := by
  intro k hk y hy
  have hkM : k ∈ normalizer (D.X₂ : Set G) := K₁_le_M₂ D hs h3 hk
  exact (mem_normalizer_iff.mp hkM y).mp hy

omit [Finite G] in
theorem X₃_le_R₂ : D.X₃ ≤ D.R₂ := le_sup_right.trans le_sup_left

theorem faithful_H₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {h : G} (hh : h ∈ D.H₁) (hc : ∀ x ∈ D.X₃, h * x = x * h) : h = 1 := by
  have hH : h ∈ D.H := H₁_le_H D hh
  have hc₄ : ∀ x ∈ D.X₄, h * x = x * h := by
    have : h ∈ kernelOf D.H D.X₄ := by
      rw [mem_ker₄_iff D hs h1 hH]
      refine mem_kernelOf_iff.mpr ⟨w₁_norm_H D hs h1 h hH, fun x hx => ?_⟩
      rw [h1.w₁_inv h hh]
      have h' : h⁻¹ * x = x * h⁻¹ := by
        have := hc x hx
        calc h⁻¹ * x = h⁻¹ * (x * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * x) * h⁻¹ := by rw [this]
          _ = x * h⁻¹ := by group
      exact h'
    exact (mem_kernelOf_iff.mp this).2
  refine kernel_eq_one_of_quasisimple D.K₁ D.R₂ D.X₂ D.z hs.comps.quasi₁ hs.comps.cen₁
    (z_mul_z D hs) (K₁_normalizes_R₂ D hs h3.toSPL3X h3.R₂_normal) (K₁_normalizes_X₂ D hs h3.toSPL3X) (z_mem_K₁ hs) ?_
    (H₁_le_K₁ D h1 hh) ?_
  · obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_two_le D.X₃ (by
      rw [X₃_card D h3]; have := hs.q_ge; omega)
    refine ⟨x, X₃_le_R₂ D hx, fun hmem => ?_⟩
    have h1' := h3.z_X₃ x hx
    have e : D.z * x * D.z⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ := by rw [h1']
    rw [e] at hmem
    have hX₃ : x⁻¹ * x⁻¹ ∈ D.X₃ := D.X₃.mul_mem (D.X₃.inv_mem hx) (D.X₃.inv_mem hx)
    have h12 : x⁻¹ * x⁻¹ ∈ D.X₂ ⊓ D.X₃ := ⟨hmem, hX₃⟩
    rw [X₂_inf_X₃ D h3 hR] at h12
    have h0 : x⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h12
    have hxx : x * x = 1 := by
      have := congrArg (fun y => y⁻¹) h0
      simpa [mul_inv_rev] using this
    exact hx1 (eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) ((X₃_eab D h3).2 x hx)
      (inv_eq_of_mul_eq_one_right hxx))
  · intro r hr
    rw [← SetLike.mem_coe, h3.R₂_prod] at hr
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc', rfl⟩ := hr
    have hb' : h * b * h⁻¹ = b := by rw [hc b hb]; group
    have hc'' : h * c * h⁻¹ = c := by rw [hc₄ c hc']; group
    have e : h * (a * b * c) * h⁻¹ * (a * b * c)⁻¹ = (h * a * h⁻¹) * a⁻¹ := by
      calc h * (a * b * c) * h⁻¹ * (a * b * c)⁻¹
          = (h * a * h⁻¹) * (h * b * h⁻¹) * (h * c * h⁻¹) * c⁻¹ * b⁻¹ * a⁻¹ := by group
        _ = (h * a * h⁻¹) * b * c * c⁻¹ * b⁻¹ * a⁻¹ := by rw [hb', hc'']
        _ = (h * a * h⁻¹) * a⁻¹ := by group
    rw [e]
    exact D.X₂.mul_mem (H_X₂ D hs h1 h3.toSPL3X h hH a ha) (D.X₂.inv_mem ha)

theorem ker₃_ne_ker₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) : kernelOf D.H D.X₃ ≠ kernelOf D.H D.X₄ := by
  intro heq
  have hh₁ : D.h₁ ∈ D.H := H₁_le_H D (mem_zpowers _)
  have hc : D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹ ∈ kernelOf D.H D.X₃ :=
    comm_t_mem_ker₃ D hs h1 h3 hh₁
  have hc4 : D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹ ∈ kernelOf D.H D.X₄ := heq ▸ hc
  have hcH : D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹ ∈ D.H := (mem_kernelOf_iff.mp hc).1
  have hw := (mem_ker₄_iff D hs h1 hcH).mp hc4
  have e1 : D.w₁ * D.h₁ * D.w₁⁻¹ = D.h₁⁻¹ := h1.w₁_inv _ (mem_zpowers _)
  have e2 : D.w₁ * D.h₂ * D.w₁⁻¹ = D.h₂ := by
    have := hs.comps.comm _ h1.w₁_mem _ (h₂_mem D hs h1)
    calc D.w₁ * D.h₂ * D.w₁⁻¹ = D.h₂ * D.w₁ * D.w₁⁻¹ := by rw [this]
      _ = D.h₂ := by group
  have hsq : D.h₁ * D.h₁ ∈ kernelOf D.H D.X₃ := by
    have := (kernelOf D.H D.X₃).mul_mem hc ((kernelOf D.H D.X₃).inv_mem hw)
    have e : D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹ *
        (D.w₁ * (D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹) * D.w₁⁻¹)⁻¹ = D.h₁ * D.h₁ := by
      have e3 : D.w₁ * (D.h₁ * (D.t * D.h₁ * D.t⁻¹)⁻¹) * D.w₁⁻¹ = D.h₁⁻¹ * (D.t * D.h₁ * D.t⁻¹)⁻¹ := by
        have : D.t * D.h₁ * D.t⁻¹ = D.h₂ := rfl
        rw [this]
        calc D.w₁ * (D.h₁ * D.h₂⁻¹) * D.w₁⁻¹ = (D.w₁ * D.h₁ * D.w₁⁻¹) * (D.w₁ * D.h₂ * D.w₁⁻¹)⁻¹ := by
              group
          _ = D.h₁⁻¹ * D.h₂⁻¹ := by rw [e1, e2]
      rw [e3]
      group
    rwa [e] at this
  have hsq1 : D.h₁ * D.h₁ ∈ D.H₁ := D.H₁.mul_mem (mem_zpowers _) (mem_zpowers _)
  have h0 := faithful_H₁ D hs h1 h3 hR hsq1 (fun x hx => (mem_kernelOf_iff.mp hsq).2 x hx)
  have h2 : orderOf D.h₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h0)
  have := Nat.le_of_dvd (by norm_num) h2
  rw [h1.h₁_ord] at this
  have := hs.q_ge
  omega

theorem ker₄_not_le_ker₃ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) : ¬ kernelOf D.H D.X₄ ≤ kernelOf D.H D.X₃ := by
  intro hle
  apply ker₃_ne_ker₄ D hs h1 h3 hR
  refine le_antisymm ?_ hle
  intro h hh
  have hhH : h ∈ D.H := (mem_kernelOf_iff.mp hh).1
  have hH' : D.w₁⁻¹ * h * D.w₁ ∈ D.H := w₁_inv_norm_H D hs h1 h hhH
  have hk4 : D.w₁⁻¹ * h * D.w₁ ∈ kernelOf D.H D.X₄ := by
    rw [mem_ker₄_iff D hs h1 hH']
    have e : D.w₁ * (D.w₁⁻¹ * h * D.w₁) * D.w₁⁻¹ = h := by group
    rw [e]; exact hh
  have hk3 := hle hk4
  have hz : D.z ∈ D.H := z_mem_H D h1
  have hcomm := H_comm D hs h1
  have e : D.w₁ * h * D.w₁⁻¹ = D.z * (D.w₁⁻¹ * h * D.w₁) * D.z⁻¹ := by
    have hw : D.w₁ = D.z * D.w₁⁻¹ := by rw [← h1.w₁_sq]; group
    calc D.w₁ * h * D.w₁⁻¹ = (D.z * D.w₁⁻¹) * h * (D.z * D.w₁⁻¹)⁻¹ := by rw [← hw]
      _ = D.z * (D.w₁⁻¹ * h * D.w₁) * D.z⁻¹ := by group
  have e' : D.z * (D.w₁⁻¹ * h * D.w₁) * D.z⁻¹ = D.w₁⁻¹ * h * D.w₁ := by
    rw [hcomm D.z hz _ hH']; group
  rw [mem_ker₄_iff D hs h1 hhH, e, e']
  exact hk3

theorem ker₄_not_le_ker₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ¬ kernelOf D.H D.X₄ ≤ kernelOf D.H D.X₁ := by
  intro hle
  have hg : D.h₁ * D.h₂ ∈ kernelOf D.H D.X₄ := H₀_le_ker₄ D hs h1 h3 (mem_zpowers _)
  have := hle hg
  apply h₁_not_mem_ker₁ D hs h1 h3
  have : D.h₁ = (D.h₁ * D.h₂) * D.h₂⁻¹ := by group
  rw [this]
  exact (kernelOf D.H D.X₁).mul_mem ‹_› ((kernelOf D.H D.X₁).inv_mem (h₂_mem_ker₁ D hs h1 h3))

theorem ker₄_not_le_ker₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ¬ kernelOf D.H D.X₄ ≤ kernelOf D.H D.X₂ := by
  intro hle
  have hg : D.h₁ * D.h₂ ∈ kernelOf D.H D.X₄ := H₀_le_ker₄ D hs h1 h3 (mem_zpowers _)
  have hg2 := hle hg
  apply h₂_not_mem_ker₂ D hs h1 h3
  have : D.h₂ = D.h₁⁻¹ * (D.h₁ * D.h₂) := by group
  rw [this]
  exact (kernelOf D.H D.X₂).mul_mem ((kernelOf D.H D.X₂).inv_mem (h₁_mem_ker₂ D hs h1 h3)) hg2

end Kernels

end CFSG.GH74.GLS.SP.Local
