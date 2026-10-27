module

public import CFSG.GH74.Uniqueness.SU.SU13TC6F

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

def normSub (E P : Subgroup G) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (g : G)
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : Subgroup G where
  carrier := {e | e ∈ E ∧ e * (g * e * g⁻¹) ∈ P}
  one_mem' := ⟨E.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haE, ha⟩ ⟨hbE, hb⟩
    refine ⟨E.mul_mem haE hbE, ?_⟩
    have hga := hg a haE
    have hcomm : b * (g * a * g⁻¹) = (g * a * g⁻¹) * b := hE _ hbE _ hga
    have : a * b * (g * (a * b) * g⁻¹) = (a * (g * a * g⁻¹)) * (b * (g * b * g⁻¹)) := by
      calc a * b * (g * (a * b) * g⁻¹) = a * (b * (g * a * g⁻¹)) * (g * b * g⁻¹) := by group
        _ = a * ((g * a * g⁻¹) * b) * (g * b * g⁻¹) := by rw [hcomm]
        _ = (a * (g * a * g⁻¹)) * (b * (g * b * g⁻¹)) := by group
    rw [this]
    exact P.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haE, ha⟩
    refine ⟨E.inv_mem haE, ?_⟩
    have hga := hg a haE
    have hcomm : a * (g * a * g⁻¹) = (g * a * g⁻¹) * a := hE _ haE _ hga
    have : a⁻¹ * (g * a⁻¹ * g⁻¹) = (a * (g * a * g⁻¹))⁻¹ := by
      calc a⁻¹ * (g * a⁻¹ * g⁻¹) = (g * a * g⁻¹ * a)⁻¹ := by group
        _ = (a * (g * a * g⁻¹))⁻¹ := by rw [← hcomm]
    rw [this]
    exact P.inv_mem ha

theorem norm_mem_of_gen {E P : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {g : G}
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) {a b c : G}
    (hgen : ∀ e ∈ E, ∃ i j k : ℤ, e = a ^ i * b ^ j * c ^ k)
    (ha : a ∈ E ∧ a * (g * a * g⁻¹) ∈ P) (hb : b ∈ E ∧ b * (g * b * g⁻¹) ∈ P)
    (hc : c ∈ E ∧ c * (g * c * g⁻¹) ∈ P) {e : G} (he : e ∈ E) : e * (g * e * g⁻¹) ∈ P := by
  have hS : e ∈ normSub E P hE g hg := by
    obtain ⟨i, j, k, rfl⟩ := hgen e he
    exact mul_mem (mul_mem (zpow_mem (show a ∈ normSub E P hE g hg from ha) i)
      (zpow_mem (show b ∈ normSub E P hE g hg from hb) j))
      (zpow_mem (show c ∈ normSub E P hE g hg from hc) k)
  exact hS.2

theorem mem_of_mem_zpowers_ne_one [Finite G] {s u : G} (hs : orderOf s = 3) (hu : u ∈ zpowers s) (hu1 : u ≠ 1)
    {K : Subgroup G} (huK : u ∈ K) : s ∈ K := by
  have hle : zpowers u ≤ zpowers s := (zpowers_le).mpr hu
  have hd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, Nat.card_zpowers, hs] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hu1
  · have heq : zpowers u = zpowers s :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hs, h])
    have : s ∈ zpowers u := by rw [heq]; exact mem_zpowers _
    exact (zpowers_le).mpr huK this

end Generic

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Ctx9

variable (X : Ctx9 G z)

theorem x_mul_x : X.L.e9.x * X.L.e9.x = 1 := by
  rw [← pow_two]
  exact sq_eq_one_of_orderOf_eq_two X.L.e9.x_ord

theorem x_inv : X.L.e9.x⁻¹ = X.L.e9.x := inv_eq_of_mul_eq_one_right X.x_mul_x

theorem x_conj_C {c : G} (hc : c ∈ X.C) : X.L.e9.x * c * X.L.e9.x⁻¹ ∈ X.C := by
  have hcs : c * X.L.e.s₂ = X.L.e.s₂ * c := mem_centralizer_singleton_iff.mp hc
  have hcs' : c * X.L.e.s₂⁻¹ = X.L.e.s₂⁻¹ * c := (Commute.inv_right (show Commute c X.L.e.s₂ from hcs)).eq
  have key : X.L.e9.x⁻¹ * X.L.e.s₂ * X.L.e9.x = X.L.e.s₂⁻¹ := by
    have := X.L.e9.x_s₂
    rw [X.x_inv] at this ⊢
    exact this
  rw [mem_centralizer_singleton_iff]
  calc X.L.e9.x * c * X.L.e9.x⁻¹ * X.L.e.s₂
      = X.L.e9.x * (c * (X.L.e9.x⁻¹ * X.L.e.s₂ * X.L.e9.x)) * X.L.e9.x⁻¹ := by group
    _ = X.L.e9.x * (c * X.L.e.s₂⁻¹) * X.L.e9.x⁻¹ := by rw [key]
    _ = X.L.e9.x * (X.L.e.s₂⁻¹ * c) * X.L.e9.x⁻¹ := by rw [hcs']
    _ = X.L.e9.x * ((X.L.e9.x⁻¹ * X.L.e.s₂ * X.L.e9.x) * c) * X.L.e9.x⁻¹ := by rw [key]
    _ = X.L.e.s₂ * (X.L.e9.x * c * X.L.e9.x⁻¹) := by group

theorem x_conj_Y {y : G} (hy : y ∈ X.Y) : X.L.e9.x * y * X.L.e9.x⁻¹ ∈ X.Y := by
  let N : Subgroup G := X.Y.map (MulAut.conj X.L.e9.x).toMonoidHom
  have hNC : N ≤ X.C := by
    rintro _ ⟨y', hy', rfl⟩
    exact X.x_conj_C (X.Y_le_C hy')
  have hNn : ∀ c ∈ X.C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    rintro c hc _ ⟨y', hy', rfl⟩
    have hc' : X.L.e9.x⁻¹ * c * X.L.e9.x ∈ X.C := by
      have := X.x_conj_C hc
      rw [X.x_inv] at this ⊢
      exact this
    refine ⟨(X.L.e9.x⁻¹ * c * X.L.e9.x) * y' * (X.L.e9.x⁻¹ * c * X.L.e9.x)⁻¹, X.conj_Y hc' hy', ?_⟩
    show X.L.e9.x * ((X.L.e9.x⁻¹ * c * X.L.e9.x) * y' * (X.L.e9.x⁻¹ * c * X.L.e9.x)⁻¹) * X.L.e9.x⁻¹ =
      c * (X.L.e9.x * y' * X.L.e9.x⁻¹) * c⁻¹
    group
  have hodd : Odd (Nat.card N) := by
    have : Nat.card N = Nat.card X.Y :=
      Subgroup.card_map_of_injective (MulAut.conj X.L.e9.x).injective
    rw [this]
    exact odd_card_oc _
  have hle := le_oc_of_normal_odd hNC hNn hodd
  exact hle ⟨y, hy, rfl⟩

theorem x_conj_Y' {n : G} (hn : n ∈ ⁅X.Y, X.Y⁆) : X.L.e9.x * n * X.L.e9.x⁻¹ ∈ ⁅X.Y, X.Y⁆ :=
  conj_mem_commutator (fun _ hy => X.x_conj_Y hy) hn

abbrev Y0 : Subgroup G := ⁅X.Y, X.Y⁆ ⊓ centralizer ({z} : Set G)

theorem Y0_le_E : X.Y0 ≤ X.E := fun e he => by
  have : e ∈ oc X.C ⊓ centralizer ({z} : Set G) :=
    mem_inf.mpr ⟨X.Y'_le_Y (mem_inf.mp he).1, (mem_inf.mp he).2⟩
  rw [X.l3.Y_cent] at this
  exact this

theorem Y0_ne_bot : X.Y0 ≠ ⊥ := by
  intro h0
  have h : (⁅X.Y, X.Y⁆ ⊓ centralizer ({z} : Set G) : Subgroup G) = ⊥ := h0
  have hlat := lattice_card X.hz X.L.e X.l X.L.m (N := ⁅X.Y, X.Y⁆) X.Y'_le_Y
    (fun c hc n hn => X.conj_Y' hc hn)
  have hb : (⁅X.Y, X.Y⁆ ⊓ zpowers X.L.e.s₂ : Subgroup G) = ⊥ :=
    inf_zpowers_eq_bot X.L.e.s₂_ord X.s₂_not_mem_Y'
  rw [hb, Subgroup.card_bot, h, Subgroup.card_bot] at hlat
  have h1 : Nat.card (⁅X.Y, X.Y⁆ : Subgroup G) = 1 := by simpa using hlat
  exact X.Y'_ne_bot (Subgroup.eq_bot_of_card_eq _ h1)

theorem conj_Y0 {g : G} (hg' : ∀ n ∈ ⁅X.Y, X.Y⁆, g * n * g⁻¹ ∈ ⁅X.Y, X.Y⁆) (hgz : g * z = z * g)
    {n : G} (hn : n ∈ X.Y0) : g * n * g⁻¹ ∈ X.Y0 := by
  obtain ⟨hnY', hnz⟩ := mem_inf.mp hn
  refine mem_inf.mpr ⟨hg' n hnY', ?_⟩
  rw [mem_centralizer_singleton_iff] at hnz ⊢
  have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
  calc g * n * g⁻¹ * z = g * n * (g⁻¹ * z) := by group
    _ = g * n * (z * g⁻¹) := by rw [hgi]
    _ = g * (n * z) * g⁻¹ := by group
    _ = g * (z * n) * g⁻¹ := by rw [hnz]
    _ = (g * z) * n * g⁻¹ := by group
    _ = (z * g) * n * g⁻¹ := by rw [hgz]
    _ = z * (g * n * g⁻¹) := by group

theorem Y0_inf_s₂ : X.Y0 ⊓ zpowers X.L.e.s₂ = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have hb := inf_zpowers_eq_bot X.L.e.s₂_ord X.s₂_not_mem_Y'
  have : u ∈ (⁅X.Y, X.Y⁆ ⊓ zpowers X.L.e.s₂ : Subgroup G) :=
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hu).1).1, (mem_inf.mp hu).2⟩
  rw [hb] at this
  exact this

theorem x_s₄' : X.L.e9.x * X.L.e9.s₄ * X.L.e9.x⁻¹ = X.L.e9.s₄ := by
  rw [X.L.e9.x_s₄]
  group

theorem false_of_ctx9 (X : Ctx9 G z) : False := by
  have hE := X.L.E.E_abel
  have hxN := X.L.E.x_norm
  have htN := X.L.E.t_norm
  have htxN : ∀ e ∈ X.L.E.E, (X.L.e.t * X.L.e9.x) * e * (X.L.e.t * X.L.e9.x)⁻¹ ∈ X.L.E.E := by
    intro e he
    have : (X.L.e.t * X.L.e9.x) * e * (X.L.e.t * X.L.e9.x)⁻¹ =
        X.L.e.t * (X.L.e9.x * e * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
    rw [this]
    exact htN _ (hxN e he)
  have hs₁ := X.L.E.s₁_mem
  have hs₂ := X.L.E.s₂_mem
  have hs₄ := X.L.E.s₄_mem
  have B1 : ∀ e ∈ X.L.E.E, e * (X.L.e.t * e * X.L.e.t⁻¹) ∈ zpowers X.L.e.s₂ := by
    refine fun e he => norm_mem_of_gen hE htN X.L.E.E_gen
      ⟨hs₁, ?_⟩ ⟨hs₂, ?_⟩ ⟨hs₄, ?_⟩ he
    · rw [X.L.e.t_s₁, mul_inv_cancel]; exact one_mem _
    · have : X.L.e.t * X.L.e.s₂ * X.L.e.t⁻¹ = X.L.e.s₂ := by rw [X.L.e.t_s₂]; group
      rw [this]; exact mul_mem (mem_zpowers _) (mem_zpowers _)
    · rw [X.L.e9.t_s₄, mul_inv_cancel]; exact one_mem _
  have B2 : ∀ e ∈ X.L.E.E, e * (X.L.e9.x * e * X.L.e9.x⁻¹) ∈ zpowers X.L.e9.s₄ := by
    refine fun e he => norm_mem_of_gen hE hxN X.L.E.E_gen
      ⟨hs₁, ?_⟩ ⟨hs₂, ?_⟩ ⟨hs₄, ?_⟩ he
    · rw [X.L.e9.x_s₁, mul_inv_cancel]; exact one_mem _
    · rw [X.L.e9.x_s₂, mul_inv_cancel]; exact one_mem _
    · rw [X.x_s₄']; exact mul_mem (mem_zpowers _) (mem_zpowers _)
  have B4 : ∀ e ∈ X.L.E.E, e * ((X.L.e.t * X.L.e9.x) * e * (X.L.e.t * X.L.e9.x)⁻¹) ∈
      zpowers X.L.e.s₁ := by
    refine fun e he => norm_mem_of_gen hE htxN X.L.E.E_gen
      ⟨hs₁, ?_⟩ ⟨hs₂, ?_⟩ ⟨hs₄, ?_⟩ he
    · have : (X.L.e.t * X.L.e9.x) * X.L.e.s₁ * (X.L.e.t * X.L.e9.x)⁻¹ = X.L.e.s₁ := by
        calc (X.L.e.t * X.L.e9.x) * X.L.e.s₁ * (X.L.e.t * X.L.e9.x)⁻¹
            = X.L.e.t * (X.L.e9.x * X.L.e.s₁ * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
          _ = X.L.e.t * X.L.e.s₁⁻¹ * X.L.e.t⁻¹ := by rw [X.L.e9.x_s₁]
          _ = (X.L.e.t * X.L.e.s₁ * X.L.e.t⁻¹)⁻¹ := by group
          _ = X.L.e.s₁ := by rw [X.L.e.t_s₁, inv_inv]
      rw [this]; exact mul_mem (mem_zpowers _) (mem_zpowers _)
    · have : (X.L.e.t * X.L.e9.x) * X.L.e.s₂ * (X.L.e.t * X.L.e9.x)⁻¹ = X.L.e.s₂⁻¹ := by
        calc (X.L.e.t * X.L.e9.x) * X.L.e.s₂ * (X.L.e.t * X.L.e9.x)⁻¹
            = X.L.e.t * (X.L.e9.x * X.L.e.s₂ * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
          _ = X.L.e.t * X.L.e.s₂⁻¹ * X.L.e.t⁻¹ := by rw [X.L.e9.x_s₂]
          _ = (X.L.e.t * X.L.e.s₂ * X.L.e.t⁻¹)⁻¹ := by group
          _ = X.L.e.s₂⁻¹ := by rw [X.L.e.t_s₂]; group
      rw [this, mul_inv_cancel]; exact one_mem _
    · have : (X.L.e.t * X.L.e9.x) * X.L.e9.s₄ * (X.L.e.t * X.L.e9.x)⁻¹ = X.L.e9.s₄⁻¹ := by
        calc (X.L.e.t * X.L.e9.x) * X.L.e9.s₄ * (X.L.e.t * X.L.e9.x)⁻¹
            = X.L.e.t * (X.L.e9.x * X.L.e9.s₄ * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
          _ = X.L.e.t * X.L.e9.s₄ * X.L.e.t⁻¹ := by rw [X.x_s₄']
          _ = X.L.e9.s₄⁻¹ := X.L.e9.t_s₄
      rw [this, mul_inv_cancel]; exact one_mem _
  have ht0 : ∀ n ∈ X.Y0, X.L.e.t * n * X.L.e.t⁻¹ ∈ X.Y0 := fun n hn =>
    X.conj_Y0 (fun m hm => X.conj_Y' X.t_mem_C hm) X.L.e.t_comm hn
  have hx0 : ∀ n ∈ X.Y0, X.L.e9.x * n * X.L.e9.x⁻¹ ∈ X.Y0 := fun n hn =>
    X.conj_Y0 (fun m hm => X.x_conj_Y' hm) X.L.e9.x_comm hn
  have htx0 : ∀ n ∈ X.Y0, (X.L.e.t * X.L.e9.x) * n * (X.L.e.t * X.L.e9.x)⁻¹ ∈ X.Y0 := by
    intro n hn
    have : (X.L.e.t * X.L.e9.x) * n * (X.L.e.t * X.L.e9.x)⁻¹ =
        X.L.e.t * (X.L.e9.x * n * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
    rw [this]
    exact ht0 _ (hx0 n hn)
  rcases Subgroup.bot_or_exists_ne_one X.Y0 with h | ⟨e₀, he₀, he₀1⟩
  · exact X.Y0_ne_bot h
  have he₀E : e₀ ∈ X.L.E.E := X.Y0_le_E he₀
  have ht₀ : X.L.e.t * e₀ * X.L.e.t⁻¹ = e₀⁻¹ := by
    have hu : e₀ * (X.L.e.t * e₀ * X.L.e.t⁻¹) ∈ X.Y0 ⊓ zpowers X.L.e.s₂ :=
      mem_inf.mpr ⟨X.Y0.mul_mem he₀ (ht0 _ he₀), B1 e₀ he₀E⟩
    rw [X.Y0_inf_s₂, mem_bot] at hu
    exact eq_inv_of_mul_eq_one_right hu
  by_cases hu4 : e₀ * (X.L.e9.x * e₀ * X.L.e9.x⁻¹) = 1
  ·
    have hx₀ : X.L.e9.x * e₀ * X.L.e9.x⁻¹ = e₀⁻¹ := eq_inv_of_mul_eq_one_right hu4
    have htx₀ : (X.L.e.t * X.L.e9.x) * e₀ * (X.L.e.t * X.L.e9.x)⁻¹ = e₀ := by
      calc (X.L.e.t * X.L.e9.x) * e₀ * (X.L.e.t * X.L.e9.x)⁻¹
          = X.L.e.t * (X.L.e9.x * e₀ * X.L.e9.x⁻¹) * X.L.e.t⁻¹ := by group
        _ = X.L.e.t * e₀⁻¹ * X.L.e.t⁻¹ := by rw [hx₀]
        _ = (X.L.e.t * e₀ * X.L.e.t⁻¹)⁻¹ := by group
        _ = e₀ := by rw [ht₀, inv_inv]
    have hu1 : e₀ * ((X.L.e.t * X.L.e9.x) * e₀ * (X.L.e.t * X.L.e9.x)⁻¹) ∈ X.Y0 :=
      X.Y0.mul_mem he₀ (htx0 _ he₀)
    have hne : e₀ * ((X.L.e.t * X.L.e9.x) * e₀ * (X.L.e.t * X.L.e9.x)⁻¹) ≠ 1 := by
      rw [htx₀]
      intro h1
      apply he₀1
      have h3 := X.L.E.E_exp e₀ he₀E
      calc e₀ = e₀ ^ 3 * (e₀ * e₀)⁻¹ := by group
        _ = 1 := by rw [h3, h1, inv_one, mul_one]
    have hs₁Y0 : X.L.e.s₁ ∈ X.Y0 :=
      mem_of_mem_zpowers_ne_one X.L.e.s₁_ord (B4 e₀ he₀E) hne hu1
    have hs₁Y' : X.L.e.s₁ ∈ ⁅X.Y, X.Y⁆ := (mem_inf.mp hs₁Y0).1
    refine X.not_conj_s₁_mem 1 ?_
    simpa using hs₁Y'
  · have hu4Y0 : e₀ * (X.L.e9.x * e₀ * X.L.e9.x⁻¹) ∈ X.Y0 :=
      X.Y0.mul_mem he₀ (hx0 _ he₀)
    have hs₄Y0 : X.L.e9.s₄ ∈ X.Y0 :=
      mem_of_mem_zpowers_ne_one X.L.e9.s₄_ord (B2 e₀ he₀E) hu4 hu4Y0
    have hs₄Y' : X.L.e9.s₄ ∈ ⁅X.Y, X.Y⁆ := (mem_inf.mp hs₄Y0).1
    obtain ⟨h, -, hhs⟩ := X.L.e9.s₄_class
    apply X.not_conj_s₂_mem h⁻¹
    have : h⁻¹ * X.L.e.s₂ * h⁻¹⁻¹ = X.L.e9.s₄ := by
      calc h⁻¹ * X.L.e.s₂ * h⁻¹⁻¹ = h⁻¹ * (h * X.L.e9.s₄ * h⁻¹) * h⁻¹⁻¹ := by rw [hhs]
        _ = X.L.e9.s₄ := by group
    rw [this]
    exact hs₄Y'

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
