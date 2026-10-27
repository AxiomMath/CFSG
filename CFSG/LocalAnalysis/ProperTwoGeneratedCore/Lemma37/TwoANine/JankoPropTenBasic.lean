module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup

variable {G : Type} [Group G]

theorem mem_zpowers_three {a x : G} (ha : orderOf a = 3) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a ∨ x = a⁻¹ := by
  obtain ⟨k, rfl⟩ := hx
  have h3 : a ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← ha, pow_orderOf_eq_one]
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Int.ediv_mul_add_emod k 3, zpow_add, mul_comm, zpow_mul, h3, one_zpow,
      one_mul]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  change a ^ k = 1 ∨ a ^ k = a ∨ a ^ k = a⁻¹
  rw [hk]
  rcases hr with h | h | h <;> rw [h]
  · left; exact zpow_zero a
  · right; left; exact zpow_one a
  · right; right
    rw [← mul_eq_one_iff_eq_inv, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, h3]

theorem ne_inv_of_orderOf_three {a : G} (ha : orderOf a = 3) : a ≠ a⁻¹ := by
  intro h
  have h2 : a ^ 2 = 1 := by rw [sq]; nth_rw 2 [h]; exact mul_inv_cancel a
  have := orderOf_dvd_of_pow_eq_one h2
  rw [ha] at this
  omega

theorem conj_eq_of_odd {a x : G} (ha : orderOf a = 3) (hx : Odd (orderOf x))
    (hxa : x ∈ normalizer (zpowers a : Set G)) : x * a * x⁻¹ = a := by
  have hmem : x * a * x⁻¹ ∈ zpowers a :=
    (mem_normalizer_iff.mp hxa a).mp (mem_zpowers a)
  rcases mem_zpowers_three ha hmem with h | h | h
  · exfalso
    have : a = 1 := by
      have h' := congrArg (fun y => x⁻¹ * y * x) h
      simpa [mul_assoc] using h'
    rw [this, orderOf_one] at ha
    omega
  · exact h
  · exfalso
    have hx2 : x ^ 2 ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have : x ^ 2 * a * (x ^ 2)⁻¹ = a := by
        calc x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by
              simp only [sq, mul_inv_rev, mul_assoc]
          _ = x * a⁻¹ * x⁻¹ := by rw [h]
          _ = (x * a * x⁻¹)⁻¹ := by group
          _ = a := by rw [h, inv_inv]
      calc x ^ 2 * a = x ^ 2 * a * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = a * x ^ 2 := by rw [this]
    obtain ⟨k, hk⟩ := hx
    have hxk : x = (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hxC : x ∈ centralizer ({a} : Set G) := hxk ▸ pow_mem hx2 _
    rw [mem_centralizer_singleton_iff] at hxC
    have : x * a * x⁻¹ = a := by rw [hxC, mul_inv_cancel_right]
    exact ne_inv_of_orderOf_three ha (this.symm.trans h)

theorem odd_orderOf_of_isPGroup {p : ℕ} (hp : Odd p) {X : Subgroup G} (hX : IsPGroup p X)
    {x : G} (hx : x ∈ X) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact Odd.of_dvd_nat (hp.pow) (orderOf_dvd_of_pow_eq_one hk')

theorem le_centralizer_of_isPGroup {a : G} (ha : orderOf a = 3) {X : Subgroup G}
    (hX : IsPGroup 3 X) (hXa : X ≤ normalizer (zpowers a : Set G)) :
    X ≤ centralizer (zpowers a : Set G) := by
  intro x hx
  have hxa := conj_eq_of_odd ha (odd_orderOf_of_isPGroup (by decide) hX hx) (hXa hx)
  rw [mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  have : x * a ^ k * x⁻¹ = a ^ k := by rw [← conj_zpow, hxa]
  calc a ^ k * x = x * a ^ k * x⁻¹ * x := by rw [this]
    _ = x * a ^ k := by group

theorem mem_normalizer_centralizer {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hx a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      have := (mem_normalizer_iff.mp (inv_mem hg) a).mp ha
      rwa [inv_inv] at this
    have := hx _ ha'
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * a := by group
  · intro hx a ha
    have ha' : g * a * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg a).mp ha
    have := hx _ ha'
    calc a * x = g⁻¹ * ((g * a * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * a * g⁻¹)) * g := by rw [this]
      _ = x * a := by group

theorem mem_normalizer_oddCoreOf [Finite G] {C : Subgroup G} {g : G}
    (hg : g ∈ normalizer (C : Set G)) : g ∈ normalizer (oddCoreOf C : Set G) := by
  set O := oddCoreOf C
  set O' := O.map (MulAut.conj g).toMonoidHom
  have hOC : O ≤ C := oddCoreOf_le C
  have hO'C : O' ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (hOC hx)
  have hCO' : C ≤ normalizer (O' : Set G) := by
    intro c hc
    refine Walter.J1.mem_normalizer_of_conj_mem fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := hw
    have hc' : g⁻¹ * c * g ∈ C := by
      have := (mem_normalizer_iff.mp (inv_mem hg) c).mp hc
      rwa [inv_inv] at this
    have hx' := (mem_normalizer_iff.mp (le_normalizer_oddCoreOf C hc') x).mp hx
    refine ⟨_, hx', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hodd : Odd (Nat.card O') := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact odd_card_oddCoreOf C
  have hle : O' ≤ O := le_oddCoreOf hO'C hCO' hodd
  exact Walter.J1.mem_normalizer_of_conj_mem fun x hx => hle ⟨x, hx, rfl⟩

theorem conj_mem_of_le_normalizer {C K : Subgroup G} (hCK : C ≤ normalizer (K : Set G)) {c x : G}
    (hc : c ∈ C) (hx : x ∈ K) : c * x * c⁻¹ ∈ K :=
  (mem_normalizer_iff.mp (hCK hc) x).mp hx

variable [Finite G] {z : G}

structure Hyp (fr : JankoFrame G z) : Prop where
  set : JankoSetting G z
  frames : JankoFrames G
  p7 : JankoProp7 fr
  not_le : ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)

namespace Hyp

variable {fr : JankoFrame G z}

omit [Finite G] in
theorem card_P₁ (fr : JankoFrame G z) : Nat.card fr.P₁ = 3 := by
  rw [fr.P₁_eq, Nat.card_zpowers, fr.orderOf_s₁]

omit [Finite G] in
theorem P₁_le_H (fr : JankoFrame G z) : fr.P₁ ≤ centralizer ({z} : Set G) := by
  have : fr.P₁ ≤ centralizer (fr.P₁ : Set G) ⊓ centralizer ({z} : Set G) :=
    fr.centralizer_P₁ ▸ le_sup_left
  exact this.trans inf_le_right

omit [Finite G] in
theorem P₁_le_C₁ (fr : JankoFrame G z) : fr.P₁ ≤ centralizer (fr.P₁ : Set G) := by
  rw [fr.P₁_eq]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact (Commute.zpow_zpow_self fr.s₁ j i).eq

omit [Finite G] in
theorem commute_of_mem_C₁ (fr : JankoFrame G z) {c p : G}
    (hc : c ∈ centralizer (fr.P₁ : Set G)) (hp : p ∈ fr.P₁) : c * p = p * c :=
  (mem_centralizer_iff.mp hc p hp).symm

theorem C₁_le_normalizer_P₁ (fr : JankoFrame G z) :
    centralizer (fr.P₁ : Set G) ≤ normalizer (fr.P₁ : Set G) := fun c hc =>
  Walter.J1.mem_normalizer_of_conj_mem fun x hx => by
    rw [commute_of_mem_C₁ fr hc hx, mul_inv_cancel_right]
    exact hx

omit [Finite G] in
theorem pow_three_of_mem_P₁ (fr : JankoFrame G z) {x : G} (hx : x ∈ fr.P₁) : x ^ 3 = 1 := by
  rw [fr.P₁_eq] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← fr.orderOf_s₁,
    pow_orderOf_eq_one, one_zpow]

omit [Finite G] in
theorem t_conj_of_mem_P₁ (fr : JankoFrame G z) {x : G} (hx : x ∈ fr.P₁) :
    fr.t * x * fr.t⁻¹ = x⁻¹ := by
  rw [fr.P₁_eq] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← conj_zpow, fr.t_mul_s₁, inv_zpow]

theorem t_mem_normalizer_P₁ (fr : JankoFrame G z) : fr.t ∈ normalizer (fr.P₁ : Set G) :=
  Walter.J1.mem_normalizer_of_conj_mem fun x hx => by
    rw [t_conj_of_mem_P₁ fr hx]; exact inv_mem hx

omit [Finite G] in
theorem P₁_inf_centralizer_t (fr : JankoFrame G z) :
    fr.P₁ ⊓ centralizer ({fr.t} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxt⟩
  rw [mem_bot]
  have h1 : fr.t * x * fr.t⁻¹ = x := by
    rw [← mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right]
  rw [t_conj_of_mem_P₁ fr hxP] at h1
  have h2 : x ^ 2 = 1 := by rw [sq]; nth_rw 1 [← h1]; exact inv_mul_cancel x
  have h3 := pow_three_of_mem_P₁ fr hxP
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3]; group

omit [Finite G] in
theorem t_mul_z (fr : JankoFrame G z) : fr.t * z = z * fr.t :=
  mem_centralizer_singleton_iff.mp fr.t_mem

omit [Finite G] in
theorem t_mul_t (fr : JankoFrame G z) : fr.t * fr.t = 1 :=
  (Walter.J1.orderOf_eq_two_iff.mp fr.orderOf_t).1

omit [Finite G] in
theorem ℓ_pow_eight (fr : JankoFrame G z) : fr.ℓ ^ 8 = 1 := by
  rw [← fr.orderOf_ℓ, pow_orderOf_eq_one]

omit [Finite G] in
theorem z_mul_z (fr : JankoFrame G z) : z * z = 1 := by
  rw [← fr.ℓ_pow_four, ← pow_add, ℓ_pow_eight]

omit [Finite G] in
theorem z_ne_one (fr : JankoFrame G z) : z ≠ 1 := by
  intro h
  have h4 : fr.ℓ ^ 4 = 1 := fr.ℓ_pow_four.trans h
  have := orderOf_dvd_of_pow_eq_one h4
  rw [fr.orderOf_ℓ] at this
  omega

omit [Finite G] in
theorem y_conj_t (fr : JankoFrame G z) : fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = fr.t * z := by
  have h6 : fr.t * fr.ℓ ^ 6 * fr.t⁻¹ = fr.ℓ ^ 2 := by
    rw [← conj_pow, fr.t_mul_ℓ, ← pow_mul,
      show 3 * 6 = 8 * 2 + 2 by norm_num, pow_add, pow_mul, ℓ_pow_eight, one_pow, one_mul]
  calc fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = (fr.t * fr.ℓ ^ 6 * fr.t⁻¹) * fr.t * (fr.ℓ ^ 2)⁻¹ := by
        rw [h6]
    _ = fr.t * fr.ℓ ^ 4 := by group
    _ = fr.t * z := by rw [fr.ℓ_pow_four]

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen
