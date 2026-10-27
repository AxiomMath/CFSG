module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistModule

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open scoped MatrixGroups

section SL2

variable {k : Type} [Field k] [CharP k 2]

theorem inv_apply_one_zero {g : SL(2, k)} (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [hg]

theorem conj_upperElt_mem {g : SL(2, k)} (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (t : k) :
    g * upperElt k t * g⁻¹ ∈ upperUnipotent k := by
  rw [mem_upperUnipotent_iff]
  refine ⟨((g : Matrix (Fin 2) (Fin 2) k) 0 0) ^ 2 * t, ?_⟩
  have hdet := g.2
  rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hdet
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_upperElt, coe_upperElt, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hg, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · linear_combination hdet

theorem conj_mem_upperUnipotent {g : SL(2, k)} (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    {b : SL(2, k)} (hb : b ∈ upperUnipotent k) : g * b * g⁻¹ ∈ upperUnipotent k := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).mp hb
  exact conj_upperElt_mem hg t

end SL2

structure Data (G : Type*) [Group G] [Finite G] (k : Type) [Field k] [Finite k] [CharP k 2]
    (m : ℕ) where
  S : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  F : Subgroup G
  N : Subgroup G
  w : G
  u : G
  π : N →* SL(2, k)
  hk : Nat.card k = 2 ^ m
  hm : 2 ≤ m
  hm3 : m ≠ 3
  hm2 : 3 ∣ 2 ^ m - 1
  X₁_le : X₁ ≤ S
  X₂_le : X₂ ≤ S
  S_eq : ∀ s ∈ S, ∃ a ∈ X₁, ∃ b ∈ X₂, s = a * b
  X₁_ab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a
  X₂_ab : ∀ a ∈ X₂, ∀ b ∈ X₂, a * b = b * a
  X₁_sq : ∀ x ∈ X₁, x * x = 1
  X₂_sq : ∀ x ∈ X₂, x * x = 1
  F_le₁ : F ≤ X₁
  F_le₂ : F ≤ X₂
  X₁_inf_X₂ : ∀ x, x ∈ X₁ → x ∈ X₂ → x ∈ F
  F_central : ∀ f ∈ F, ∀ s ∈ S, s * f = f * s
  centre_le : ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → x ∈ F
  comm_mem_F : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ F
  card_X₁ : Nat.card X₁ = (2 ^ m) ^ 3
  card_F : Nat.card F = (2 ^ m) ^ 2
  S_le_N : S ≤ N
  N_le_norm : N ≤ normalizer (X₁ : Set G)
  N_conj : ∀ g ∈ normalizer (X₁ : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N
  π_surj : Function.Surjective π
  π_ker : ∀ n : N, π n = 1 ↔ (n : G) ∈ X₁
  π_S : ∀ n : N, (n : G) ∈ S ↔ π n ∈ upperUnipotent k
  w_mem : w ∈ N
  X₁_eq : ∀ x ∈ X₁, ∃ a ∈ F, ∃ b ∈ F, x = a * (w * b * w⁻¹)
  u_norm : u ∈ normalizer (S : Set G)
  u_X₁ : ∀ x ∈ X₁, u * x * u⁻¹ ∈ X₂
  u_X₂ : ∀ x ∈ X₂, u * x * u⁻¹ ∈ X₁
  u_sq : u * u ∈ S
  CC : ∀ z ∈ F, (∀ n ∈ N, n * z = z * n) → (∀ n ∈ N, u * n * u⁻¹ * z = z * (u * n * u⁻¹)) →
    z = 1


theorem card_sup_mul_card_inf' {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

namespace Data

variable {G : Type*} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2] {m : ℕ}
  (d : Data G k m)

include d in
theorem two_pow_ge : 4 ≤ 2 ^ m := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) d.hm

theorem F_le_S : d.F ≤ d.S := d.F_le₁.trans d.X₁_le

theorem conj_mem_F {g : G} (hg : g ∈ normalizer (d.S : Set G)) {f : G} (hf : f ∈ d.F) :
    g * f * g⁻¹ ∈ d.F := by
  refine d.centre_le _ ((mem_normalizer_iff.mp hg f).mp (d.F_le_S hf)) fun s hs => ?_
  have hs' : g⁻¹ * s * g ∈ d.S := by
    have := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    simpa using this
  have h1 := d.F_central f hf _ hs'
  calc s * (g * f * g⁻¹) = g * ((g⁻¹ * s * g) * f) * g⁻¹ := by group
    _ = g * (f * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * f * g⁻¹ * s := by group

theorem w_not_mem_normalizer : d.w ∉ normalizer (d.S : Set G) := by
  intro hw
  have hX : d.X₁ ≤ d.F := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := d.X₁_eq x hx
    exact mul_mem ha (d.conj_mem_F hw hb)
  have h1 := Subgroup.card_le_of_le hX
  rw [d.card_X₁, d.card_F] at h1
  have h4 := d.two_pow_ge
  nlinarith

theorem w_mem_normalizer_of
    (h : ((d.π ⟨d.w, d.w_mem⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    d.w ∈ normalizer (d.S : Set G) := by
  rw [mem_normalizer_iff]
  intro s
  have hinv : ((d.π ⟨d.w, d.w_mem⟩)⁻¹ : SL(2, k)) 1 0 = 0 := inv_apply_one_zero h
  constructor
  · intro hs
    have hsN : s ∈ d.N := d.S_le_N hs
    have hwsN : d.w * s * d.w⁻¹ ∈ d.N := mul_mem (mul_mem d.w_mem hsN) (inv_mem d.w_mem)
    rw [d.π_S ⟨_, hwsN⟩]
    have e : d.π ⟨d.w * s * d.w⁻¹, hwsN⟩ =
        d.π ⟨d.w, d.w_mem⟩ * d.π ⟨s, hsN⟩ * (d.π ⟨d.w, d.w_mem⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact conj_mem_upperUnipotent h ((d.π_S ⟨s, hsN⟩).mp hs)
  · intro hs
    have hwsN : d.w * s * d.w⁻¹ ∈ d.N := d.S_le_N hs
    have hsN : s ∈ d.N := by
      have := mul_mem (mul_mem (inv_mem d.w_mem) hwsN) d.w_mem
      rwa [show d.w⁻¹ * (d.w * s * d.w⁻¹) * d.w = s by group] at this
    rw [d.π_S ⟨s, hsN⟩]
    have e : d.π ⟨s, hsN⟩ = (d.π ⟨d.w, d.w_mem⟩)⁻¹ * d.π ⟨d.w * s * d.w⁻¹, hwsN⟩ *
        d.π ⟨d.w, d.w_mem⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change s = d.w⁻¹ * (d.w * s * d.w⁻¹) * d.w
      group
    rw [e]
    have := conj_mem_upperUnipotent hinv ((d.π_S ⟨_, hwsN⟩).mp hs)
    simpa using this

theorem mem_sup_of_mem_N {n : G} (hn : n ∈ d.N) :
    n ∈ d.S ⊔ d.S.map (MulAut.conj d.w).toMonoidHom := by
  set g := d.π ⟨d.w, d.w_mem⟩ with hgdef
  have hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := fun h =>
    d.w_not_mem_normalizer (d.w_mem_normalizer_of h)
  have htop :=
    CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.upperUnipotent_sup_map_conj_eq_top hg
  set H : Subgroup d.N := (d.S ⊔ d.S.map (MulAut.conj d.w).toMonoidHom).subgroupOf d.N with hH
  have hπH : ⊤ ≤ H.map d.π := by
    rw [← htop]
    refine sup_le ?_ ?_
    · intro b hb
      obtain ⟨n', rfl⟩ := d.π_surj b
      exact ⟨n', mem_subgroupOf.mpr (mem_sup_left ((d.π_S n').mpr hb)), rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨n', rfl⟩ := d.π_surj b
      have hn'S : (n' : G) ∈ d.S := (d.π_S n').mpr hb
      refine ⟨⟨d.w, d.w_mem⟩ * n' * ⟨d.w, d.w_mem⟩⁻¹, mem_subgroupOf.mpr
        (mem_sup_right ⟨n', hn'S, ?_⟩), ?_⟩
      · simp
      · simp [map_mul, map_inv, hgdef]
  obtain ⟨h, hh, hπ⟩ := hπH (mem_top (d.π ⟨n, hn⟩))
  have hker : d.π (h⁻¹ * ⟨n, hn⟩) = 1 := by rw [map_mul, map_inv, hπ, inv_mul_cancel]
  have hX : ((h⁻¹ * ⟨n, hn⟩ : d.N) : G) ∈ d.X₁ := (d.π_ker _).mp hker
  have hS : ((h⁻¹ * ⟨n, hn⟩ : d.N) : G) ∈ d.S ⊔ d.S.map (MulAut.conj d.w).toMonoidHom :=
    mem_sup_left (d.X₁_le hX)
  have := mul_mem (mem_subgroupOf.mp hh) hS
  simpa using this

def Z : Subgroup G := d.F ⊓ d.F.map (MulAut.conj d.w).toMonoidHom

theorem mem_Z {z : G} : z ∈ d.Z ↔ z ∈ d.F ∧ ∃ b ∈ d.F, d.w * b * d.w⁻¹ = z := by
  simp [Z, Subgroup.mem_inf, Subgroup.mem_map]

theorem Z_le_F : d.Z ≤ d.F := inf_le_left

theorem Z_le_X₁ : d.Z ≤ d.X₁ := d.Z_le_F.trans d.F_le₁

theorem Z_central {z : G} (hz : z ∈ d.Z) {n : G} (hn : n ∈ d.N) : n * z = z * n := by
  have hS : d.S ≤ centralizer ({z} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact d.F_central z (d.Z_le_F hz) s hs
  have hSw : d.S.map (MulAut.conj d.w).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨-, b, hb, rfl⟩ := d.mem_Z.mp hz
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc d.w * s * d.w⁻¹ * (d.w * b * d.w⁻¹) = d.w * (s * b) * d.w⁻¹ := by group
      _ = d.w * (b * s) * d.w⁻¹ := by rw [d.F_central b hb s hs]
      _ = d.w * b * d.w⁻¹ * (d.w * s * d.w⁻¹) := by group
  have := (sup_le hS hSw) (d.mem_sup_of_mem_N hn)
  rw [mem_centralizer_singleton_iff] at this
  exact this

theorem card_Z : Nat.card d.Z = 2 ^ m := by
  set Fw := d.F.map (MulAut.conj d.w).toMonoidHom with hFw
  have hFw_le : Fw ≤ d.X₁ := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp (d.N_le_norm d.w_mem) b).mp (d.F_le₁ hb)
  have hsup : d.F ⊔ Fw = d.X₁ := le_antisymm (sup_le d.F_le₁ hFw_le) (fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := d.X₁_eq x hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right ⟨b, hb, rfl⟩))
  have hnorm : d.F ≤ normalizer (Fw : Set G) := by
    intro f hf
    rw [mem_normalizer_iff]
    intro x
    have hf1 := d.F_le₁ hf
    constructor
    · intro hx
      rw [d.X₁_ab f hf1 x (hFw_le hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hx1 : x ∈ d.X₁ := by
        have := mul_mem (mul_mem (inv_mem hf1) (hFw_le hx)) hf1
        rwa [show f⁻¹ * (f * x * f⁻¹) * f = x by group] at this
      rwa [d.X₁_ab f hf1 x hx1, mul_inv_cancel_right] at hx
  have h := card_sup_mul_card_inf' hnorm
  rw [hsup, d.card_X₁, hFw, Subgroup.card_map_of_injective (MulAut.conj d.w).injective,
    d.card_F] at h
  have h2 : (2 ^ m) ^ 3 * Nat.card d.Z = (2 ^ m) ^ 3 * 2 ^ m := by
    change (2 ^ m) ^ 3 * Nat.card (d.F ⊓ Fw : Subgroup G) = _
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h2

theorem Z_eq {z : G} : z ∈ d.Z ↔ z ∈ d.X₁ ∧ ∀ n ∈ d.N, n * z = z * n := by
  constructor
  · intro hz
    exact ⟨d.Z_le_X₁ hz, fun n hn => d.Z_central hz hn⟩
  · rintro ⟨hz1, hzc⟩
    have hF : z ∈ d.F := d.centre_le z (d.X₁_le hz1) fun s hs => hzc s (d.S_le_N hs)
    exact d.mem_Z.mpr ⟨hF, z, hF, by rw [hzc d.w d.w_mem, mul_inv_cancel_right]⟩

theorem card_X₂ : Nat.card d.X₂ = (2 ^ m) ^ 3 := by
  have h1 : (d.X₁.map (MulAut.conj d.u).toMonoidHom) ≤ d.X₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact d.u_X₁ x hx
  have h2 : (d.X₂.map (MulAut.conj d.u).toMonoidHom) ≤ d.X₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact d.u_X₂ x hx
  have c1 := Subgroup.card_le_of_le h1
  have c2 := Subgroup.card_le_of_le h2
  rw [Subgroup.card_map_of_injective (MulAut.conj d.u).injective] at c1 c2
  rw [d.card_X₁] at c1 c2
  omega

theorem map_u_X₁ : d.X₁.map (MulAut.conj d.u).toMonoidHom = d.X₂ := by
  have h1 : (d.X₁.map (MulAut.conj d.u).toMonoidHom) ≤ d.X₂ := by
    rintro _ ⟨x, hx, rfl⟩
    exact d.u_X₁ x hx
  exact Subgroup.eq_of_le_of_card_ge h1 (by
    rw [Subgroup.card_map_of_injective (MulAut.conj d.u).injective, d.card_X₂, d.card_X₁])

theorem map_u_X₂ : d.X₂.map (MulAut.conj d.u).toMonoidHom = d.X₁ := by
  have h2 : (d.X₂.map (MulAut.conj d.u).toMonoidHom) ≤ d.X₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact d.u_X₂ x hx
  exact Subgroup.eq_of_le_of_card_ge h2 (by
    rw [Subgroup.card_map_of_injective (MulAut.conj d.u).injective, d.card_X₂, d.card_X₁])

theorem conj_inv_u_X₁ {x : G} (hx : x ∈ d.X₂) : d.u⁻¹ * x * d.u ∈ d.X₁ := by
  rw [← d.map_u_X₁] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have e : d.u⁻¹ * (d.u * y * d.u⁻¹) * d.u = y := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [e]
  exact hy

theorem conj_inv_u_X₂ {x : G} (hx : x ∈ d.X₁) : d.u⁻¹ * x * d.u ∈ d.X₂ := by
  rw [← d.map_u_X₂] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have e : d.u⁻¹ * (d.u * y * d.u⁻¹) * d.u = y := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [e]
  exact hy

theorem conj_inv_u_F {f : G} (hf : f ∈ d.F) : d.u⁻¹ * f * d.u ∈ d.F := by
  have := d.conj_mem_F (inv_mem d.u_norm) hf
  simpa using this

theorem module_facts :
    (∀ n ∈ d.N, n ≠ 1 → Odd (orderOf n) → ∀ x ∈ d.X₁, n * x * n⁻¹ * x⁻¹ ∈ d.Z → x ∈ d.Z) ∧
    (∀ s ∈ d.S, s ∉ d.X₁ → ∀ x ∈ d.X₁, s * x * s⁻¹ * x⁻¹ ∈ d.Z → x ∈ d.F) ∧
    (∀ g ∈ d.N, (∀ f ∈ d.F, g * f * g⁻¹ * f⁻¹ ∈ d.Z) → g ∈ d.S) ∧
    (∀ n ∈ d.N, n ∉ d.X₁ → Odd (orderOf n) → ∀ s ∈ d.S, n * s * n⁻¹ * s⁻¹ ∈ d.X₁ →
      s ∈ d.X₁) ∧
    (∃ ω ∈ d.N, ω ∈ normalizer (d.S : Set G) ∧ ω ∉ d.X₁ ∧ ω * ω * ω = 1) := by
  have h := natural_module_facts (G := G) (k := k) d.hk d.hm d.hm3 (N := d.N) (X := d.X₁)
    (Z := d.Z) (S₀ := d.S) (F₀ := d.F) d.N_le_norm d.X₁_sq d.X₁_ab d.Z_le_X₁
    (fun n hn z hz => d.Z_central hz hn) (by rw [d.card_X₁, d.card_Z]; ring) d.π d.π_surj
    d.π_ker d.S_le_N d.π_S d.Z_le_F d.F_le₁
    (fun x hx => ⟨fun hxF s hs => d.F_central x hxF s hs,
      fun h => d.centre_le x (d.X₁_le hx) h⟩) (by rw [d.card_F, d.card_Z]; ring)
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  exact ⟨c1, c2, c3, c4, c5 d.hm2⟩

theorem S_eq' : ∀ s ∈ d.S, ∃ a ∈ d.X₂, ∃ b ∈ d.X₁, s = a * b := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := d.S_eq s⁻¹ (inv_mem hs)
  exact ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, by rw [← mul_inv_rev, ← hab, inv_inv]⟩

theorem centralizer_X₁ {x : G} (hx : x ∈ d.X₁) (hxF : x ∉ d.F) {s : G} (hs : s ∈ d.S)
    (hc : s * x = x * s) : s ∈ d.X₁ := by
  by_contra hsX
  apply hxF
  refine d.module_facts.2.1 s hs hsX x hx ?_
  have : s * x * s⁻¹ * x⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact one_mem _

theorem centralizer_X₂ {y : G} (hy : y ∈ d.X₂) (hyF : y ∉ d.F) {s : G} (hs : s ∈ d.S)
    (hc : s * y = y * s) : s ∈ d.X₂ := by
  have hy' := d.conj_inv_u_X₁ hy
  have hy'F : d.u⁻¹ * y * d.u ∉ d.F := fun h => hyF (by
    have := d.conj_mem_F d.u_norm h
    simpa [mul_assoc] using this)
  have hs' : d.u⁻¹ * s * d.u ∈ d.S := by
    have := (mem_normalizer_iff.mp (inv_mem d.u_norm) s).mp hs
    simpa using this
  have hc' : (d.u⁻¹ * s * d.u) * (d.u⁻¹ * y * d.u) = (d.u⁻¹ * y * d.u) * (d.u⁻¹ * s * d.u) := by
    calc (d.u⁻¹ * s * d.u) * (d.u⁻¹ * y * d.u) = d.u⁻¹ * (s * y) * d.u := by group
      _ = d.u⁻¹ * (y * s) * d.u := by rw [hc]
      _ = (d.u⁻¹ * y * d.u) * (d.u⁻¹ * s * d.u) := by group
  have h1 := d.u_X₁ _ (d.centralizer_X₁ hy' hy'F hs' hc')
  have e : d.u * (d.u⁻¹ * s * d.u) * d.u⁻¹ = s := by group
  rwa [e] at h1

theorem mem_normalizer_of_cube {B : Subgroup G} {g : G} (hg3 : g * g * g = 1)
    (h : ∀ y ∈ B, g * y * g⁻¹ ∈ B) : g ∈ normalizer (B : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have e : y = g * (g * (g * y * g⁻¹) * g⁻¹) * g⁻¹ := by
    have h0 : g * (g * (g * y * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * y * (g * g * g)⁻¹ := by group
    rw [h0, hg3]
    group
  rw [e]
  exact h _ (h _ hy)

theorem mem_normalizer_F {g : G} (hg : g ∈ normalizer (d.S : Set G)) :
    g ∈ normalizer (d.F : Set G) := by
  rw [mem_normalizer_iff]
  intro f
  refine ⟨fun hf => d.conj_mem_F hg hf, fun hf => ?_⟩
  have := d.conj_mem_F (inv_mem hg) hf
  have e : g⁻¹ * (g * f * g⁻¹) * g⁻¹⁻¹ = f := by group
  rwa [e] at this

theorem mem_normalizer_Z {g : G} (hg : g ∈ normalizer (d.X₁ : Set G)) :
    g ∈ normalizer (d.Z : Set G) := by
  have key : ∀ {h : G}, h ∈ normalizer (d.X₁ : Set G) → ∀ z ∈ d.Z, h * z * h⁻¹ ∈ d.Z := by
    intro h hh z hz
    rw [d.Z_eq]
    refine ⟨(mem_normalizer_iff.mp hh z).mp (d.Z_le_X₁ hz), fun n hn => ?_⟩
    have hn' : h⁻¹ * n * h ∈ d.N := by
      have := d.N_conj _ (inv_mem hh) n hn
      simpa using this
    have h1 := d.Z_central hz hn'
    calc n * (h * z * h⁻¹) = h * ((h⁻¹ * n * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * n * h)) * h⁻¹ := by rw [h1]
      _ = h * z * h⁻¹ * n := by group
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key hg z hz, fun hz => ?_⟩
  have := key (inv_mem hg) _ hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem conj_mem_of_normalizes {A B : Subgroup G} (hAS : A ≤ d.S) (hBS : B ≤ d.S)
    (hS : ∀ s ∈ d.S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) (hAsq : ∀ a ∈ A, a * a = 1)
    (hBsq : ∀ b ∈ B, b * b = 1) (hFA : d.F ≤ A) (hFB : d.F ≤ B)
    (hAB : ∀ x, x ∈ A → x ∈ B → x ∈ d.F)
    (hCB : ∀ y ∈ B, y ∉ d.F → ∀ s ∈ d.S, s * y = y * s → s ∈ B)
    {g : G} (hg : g ∈ normalizer (d.S : Set G)) (hgA : g ∈ normalizer (A : Set G)) :
    ∀ y ∈ B, g * y * g⁻¹ ∈ B := by
  intro y hy
  have hyS : y ∈ d.S := hBS hy
  have hy'S : g * y * g⁻¹ ∈ d.S := (mem_normalizer_iff.mp hg y).mp hyS
  by_cases hyF : y ∈ d.F
  · exact hFB (d.conj_mem_F hg hyF)
  · obtain ⟨a, ha, b, hb, hab⟩ := hS _ hy'S
    have hy'sq : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
      calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hBsq y hy]; group
    have hcomm : a * b = b * a := by
      have h1 : (a * b) * (a * b) = 1 := by rw [← hab]; exact hy'sq
      have h2 := inv_eq_of_mul_eq_one_right h1
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hAsq a ha),
        inv_eq_of_mul_eq_one_right (hBsq b hb)] at h2
      exact h2.symm
    by_cases haF : a ∈ d.F
    · rw [hab]
      exact mul_mem (hFB haF) hb
    · have hbF : b ∈ d.F := by
        by_contra hbF
        exact haF (hAB a ha (hCB b hb hbF a (hAS ha) hcomm))
      have hy'A : g * y * g⁻¹ ∈ A := by
        rw [hab]
        exact mul_mem ha (hFA hbF)
      have hyA : y ∈ A := (mem_normalizer_iff.mp hgA y).mpr hy'A
      exact (hyF (hAB y hyA hy)).elim

end Data

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
