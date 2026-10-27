module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

namespace OrdWr

theorem card_cond_pairs {G : Type*} [Group G] (cond : G → Prop) :
    Nat.card {q : G × G // cond (q.1⁻¹ * q.2)} = Nat.card G * Nat.card {u : G // cond u} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.1⁻¹ * q.1.2, q.2⟩)
      invFun := fun r => ⟨(r.1, r.1 * r.2.1), by simpa using r.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨g, g'⟩, hq⟩
    simp
  · rintro ⟨g, ⟨u, hu⟩⟩
    simp

theorem card_fibre {G Y : Type*} [Group G] (Z : Subgroup G) (α β : G → Y)
    (P : Y × Y → Prop) (cond : G → Prop)
    (hα : ∀ g g' : G, α g = α g' ↔ g⁻¹ * g' ∈ Z)
    (hβ : ∀ g g' : G, β g = β g' ↔ g⁻¹ * g' ∈ Z)
    (hP : ∀ g g' : G, P (α g, β g') ↔ cond (g⁻¹ * g'))
    (g₀ g₀' : G) (hs : P (α g₀, β g₀')) :
    Nat.card {q : {q : G × G // cond (q.1⁻¹ * q.2)} //
        (α q.1.1, β q.1.2) = (α g₀, β g₀')} = Nat.card Z * Nat.card Z := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun q => (⟨g₀⁻¹ * q.1.1.1, ?_⟩, ⟨g₀'⁻¹ * q.1.1.2, ?_⟩)
      invFun := fun r => ⟨⟨(g₀ * r.1, g₀' * r.2), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (hα _ _).1 (congrArg Prod.fst q.2).symm
  · exact (hβ _ _).1 (congrArg Prod.snd q.2).symm
  · have h1 : α (g₀ * r.1) = α g₀ := ((hα _ _).2 (by simp)).symm
    have h2 : β (g₀' * r.2) = β g₀' := ((hβ _ _).2 (by simp)).symm
    show cond _
    rw [← hP, h1, h2]
    exact hs
  · have h1 : α (g₀ * r.1) = α g₀ := ((hα _ _).2 (by simp)).symm
    have h2 : β (g₀' * r.2) = β g₀' := ((hβ _ _).2 (by simp)).symm
    show (α (g₀ * r.1), β (g₀' * r.2)) = (α g₀, β g₀')
    rw [h1, h2]
  · rintro ⟨⟨⟨g, g'⟩, hq⟩, hq'⟩
    simp
  · rintro ⟨c, d⟩
    simp

theorem count_pairs {G Y : Type*} [Group G] [Finite G] (Z : Subgroup G) (α β : G → Y)
    (P : Y × Y → Prop) (cond : G → Prop)
    (hα : ∀ g g' : G, α g = α g' ↔ g⁻¹ * g' ∈ Z)
    (hβ : ∀ g g' : G, β g = β g' ↔ g⁻¹ * g' ∈ Z)
    (hP : ∀ g g' : G, P (α g, β g') ↔ cond (g⁻¹ * g'))
    (hPr : ∀ p, P p → ∃ g g' : G, p = (α g, β g')) :
    Nat.card Z * Nat.card Z * Nat.card {p : Y × Y // P p} =
      Nat.card G * Nat.card {u : G // cond u} := by
  classical
  rw [← card_cond_pairs]
  let Φ : {q : G × G // cond (q.1⁻¹ * q.2)} → {p : Y × Y // P p} :=
    fun q => ⟨(α q.1.1, β q.1.2), (hP _ _).2 q.2⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨p, hp⟩
    obtain ⟨g, g', rfl⟩ := hPr p hp
    exact ⟨⟨(g, g'), (hP g g').1 hp⟩, rfl⟩
  have hfin : Finite {p : Y × Y // P p} := Finite.of_surjective Φ hsurj
  have : Fintype {p : Y × Y // P p} := Fintype.ofFinite _
  have hfib : ∀ s : {p : Y × Y // P p}, Nat.card {q // Φ q = s} = Nat.card Z * Nat.card Z := by
    intro s
    obtain ⟨⟨⟨g, g'⟩, hc⟩, hq⟩ := hsurj s
    have hs : P (α g, β g') := by
      have := s.2
      rw [← hq] at this
      exact this
    have h := card_fibre Z α β P cond hα hβ hP g g' hs
    rw [← h]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [← hq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  refine Eq.symm ?_
  calc Nat.card {q : G × G // cond (q.1⁻¹ * q.2)}
      = Nat.card (Σ s : {p : Y × Y // P p}, {q // Φ q = s}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv Φ)).symm
    _ = ∑ s : {p : Y × Y // P p}, Nat.card {q // Φ q = s} := Nat.card_sigma
    _ = ∑ _s : {p : Y × Y // P p}, Nat.card Z * Nat.card Z :=
        Finset.sum_congr rfl fun s _ => hfib s
    _ = Nat.card Z * Nat.card Z * Nat.card {p : Y × Y // P p} := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]

section Elementary

variable {X : Type*} [Group X]

theorem zpow_of_sq_eq_one {y : X} (hy : y * y = 1) (n : ℤ) : y ^ n = 1 ∨ y ^ n = y := by
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left; rw [hm, zpow_mul, h2, one_zpow]
  · right; rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem conj_eq_iff {H Z : Subgroup X} {s : X}
    (hs : ∀ c ∈ H, s * c = c * s → c ∈ Z)
    (hsZ : ∀ c ∈ Z, s * c = c * s) {g g' : X} (hg : g ∈ H) (hg' : g' ∈ H) :
    g * s * g⁻¹ = g' * s * g'⁻¹ ↔ g⁻¹ * g' ∈ Z := by
  constructor
  · intro h
    refine hs _ (mul_mem (inv_mem hg) hg') ?_
    calc s * (g⁻¹ * g') = g⁻¹ * (g * s * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * s * g'⁻¹) * g' := by rw [h]
      _ = (g⁻¹ * g') * s := by group
  · intro hc
    have h1 := hsZ _ hc
    have hcs : (g⁻¹ * g') * s * (g⁻¹ * g')⁻¹ = s := by
      rw [← h1]; group
    calc g * s * g⁻¹ = g * ((g⁻¹ * g') * s * (g⁻¹ * g')⁻¹) * g⁻¹ := by rw [hcs]
      _ = g' * s * g'⁻¹ := by group

end Elementary

structure ZSetup {X : Type*} [Group X] (K₁ K₂ : Subgroup X) (z t : X) : Prop where
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  inf : K₁ ⊓ K₂ = Subgroup.zpowers z
  z2 : orderOf z = 2
  t2 : t * t = 1
  tz : z * t = t * z
  tK : t ∉ K₁ ⊔ K₂
  t₁ : ∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂
  t₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁

namespace ZSetup

variable {X : Type*} [Group X] {K₁ K₂ : Subgroup X} {z t : X}

theorem z_mul_z (hS : ZSetup K₁ K₂ z t) : z * z = 1 := by
  rw [← pow_two]
  have := pow_orderOf_eq_one z
  rwa [hS.z2] at this

theorem z_ne_one (hS : ZSetup K₁ K₂ z t) : z ≠ 1 := by
  intro h
  have := hS.z2
  rw [h, orderOf_one] at this
  omega

theorem mem_Z_iff (hS : ZSetup K₁ K₂ z t) {x : X} :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact zpow_of_sq_eq_one hS.z_mul_z n
  · rintro (h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z

theorem zL (hS : ZSetup K₁ K₂ z t) : z ∈ K₁ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [hS.inf]; exact Subgroup.mem_zpowers z
  exact this.1

theorem zR (hS : ZSetup K₁ K₂ z t) : z ∈ K₂ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [hS.inf]; exact Subgroup.mem_zpowers z
  exact this.2

theorem Z_le_left (hS : ZSetup K₁ K₂ z t) : Subgroup.zpowers z ≤ K₁ := by
  rw [← hS.inf]; exact inf_le_left

theorem Z_le_right (hS : ZSetup K₁ K₂ z t) : Subgroup.zpowers z ≤ K₂ := by
  rw [← hS.inf]; exact inf_le_right

theorem comm_z_sup (hS : ZSetup K₁ K₂ z t) {y : X} (hy : y ∈ K₁ ⊔ K₂) : y * z = z * y := by
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer {z} := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact (hS.comm a ha z hS.zR).symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact hS.comm z hS.zL b hb
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) z (Set.mem_singleton z)).symm

theorem Z_comm (hS : ZSetup K₁ K₂ z t) {x y : X} (hx : x ∈ Subgroup.zpowers z)
    (hy : y ∈ K₁ ⊔ K₂) : x * y = y * x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hc : Commute z y := (hS.comm_z_sup hy).symm
  exact (hc.zpow_left n).eq

theorem Z_comm_t (hS : ZSetup K₁ K₂ z t) {x : X} (hx : x ∈ Subgroup.zpowers z) :
    t * x = x * t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hc : Commute t z := hS.tz.symm
  exact (hc.zpow_right n).eq

theorem Z_tau (hS : ZSetup K₁ K₂ z t) {x : X} (hx : x ∈ Subgroup.zpowers z) :
    t * x * t⁻¹ = x := by
  rw [hS.Z_comm_t hx, mul_inv_cancel_right]

open scoped Pointwise in
theorem decomp (hS : ZSetup K₁ K₂ z t) {x : X} (hx : x ∈ K₁ ⊔ K₂) :
    ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  have hle : K₁ ≤ Subgroup.normalizer (K₂ : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hS.comm a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hc
      have h1 := hS.comm a⁻¹ (inv_mem ha) _ hc
      have h2 : b * a⁻¹ = (a * b * a⁻¹) * a⁻¹ := by rw [← h1]; group
      have h3 : b = a * b * a⁻¹ := mul_right_cancel h2
      rw [h3]
      exact hc
  have hx' : x ∈ (K₁ : Set X) * (K₂ : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hle]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem tau_mem_sup (hS : ZSetup K₁ K₂ z t) {x : X} (hx : x ∈ K₁ ⊔ K₂) :
    t * x * t⁻¹ ∈ K₁ ⊔ K₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hS.decomp hx
  have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right (hS.t₁ a ha)) (Subgroup.mem_sup_left (hS.t₂ b hb))

theorem both_mem_Z (hS : ZSetup K₁ K₂ z t) {x y : X} (hx : x ∈ K₁) (hy : y ∈ K₂)
    (hxy : x * y ∈ Subgroup.zpowers z) :
    x ∈ Subgroup.zpowers z ∧ y ∈ Subgroup.zpowers z := by
  have hx2 : x ∈ K₂ := by
    have : x * y * y⁻¹ ∈ K₂ := mul_mem (hS.Z_le_right hxy) (inv_mem hy)
    rwa [mul_inv_cancel_right] at this
  have hxZ : x ∈ Subgroup.zpowers z := by rw [← hS.inf]; exact ⟨hx, hx2⟩
  refine ⟨hxZ, ?_⟩
  have : x⁻¹ * (x * y) ∈ Subgroup.zpowers z := mul_mem (inv_mem hxZ) hxy
  rwa [inv_mul_cancel_left] at this

theorem z_pow_of_odd (hS : ZSetup K₁ K₂ z t) {k : ℕ} (hk : Odd k) : z ^ k = z := by
  obtain ⟨m, rfl⟩ := hk
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hS.z_mul_z
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem odd_of_z_pow (hS : ZSetup K₁ K₂ z t) {k : ℕ} (h : z ^ k = z) : Odd k := by
  rcases Nat.even_or_odd k with hk | hk
  · exfalso
    obtain ⟨m, rfl⟩ := hk
    have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hS.z_mul_z
    rw [← two_mul, pow_mul, h2, one_pow] at h
    exact hS.z_ne_one h.symm
  · exact hk

theorem ab_mul (hS : ZSetup K₁ K₂ z t) {g g' : X} (hg : g ∈ K₁) (hg' : g' ∈ K₁) :
    (g * t * g⁻¹) * (g' * (t * z) * g'⁻¹) =
      z * (g * (g⁻¹ * g')⁻¹ * g⁻¹) * (t * (g⁻¹ * g') * t⁻¹) := by
  have hB2 : t * (g⁻¹ * g') * t⁻¹ ∈ K₂ := hS.t₁ _ (mul_mem (inv_mem hg) hg')
  have h1 : t * (g⁻¹ * g') * t⁻¹ * g'⁻¹ = g'⁻¹ * (t * (g⁻¹ * g') * t⁻¹) :=
    (hS.comm g'⁻¹ (inv_mem hg') _ hB2).symm
  have h2 : z * (t * (g⁻¹ * g') * t⁻¹) = t * (g⁻¹ * g') * t⁻¹ * z := hS.comm z hS.zL _ hB2
  have h3 : g * z = z * g := hS.comm g hg z hS.zR
  calc (g * t * g⁻¹) * (g' * (t * z) * g'⁻¹)
      = g * (t * (g⁻¹ * g') * t⁻¹) * (t * t) * z * g'⁻¹ := by group
    _ = g * (t * (g⁻¹ * g') * t⁻¹) * z * g'⁻¹ := by rw [hS.t2, mul_one]
    _ = g * (z * (t * (g⁻¹ * g') * t⁻¹)) * g'⁻¹ := by rw [h2]; simp only [mul_assoc]
    _ = (g * z) * ((t * (g⁻¹ * g') * t⁻¹) * g'⁻¹) := by simp only [mul_assoc]
    _ = (z * g) * (g'⁻¹ * (t * (g⁻¹ * g') * t⁻¹)) := by rw [h3, h1]
    _ = z * (g * (g⁻¹ * g')⁻¹ * g⁻¹) * (t * (g⁻¹ * g') * t⁻¹) := by group

theorem ab_iff [Finite X] (hS : ZSetup K₁ K₂ z t) {g g' : X} (hg : g ∈ K₁) (hg' : g' ∈ K₁) :
    z ∈ Subgroup.zpowers ((g * t * g⁻¹) * (g' * (t * z) * g'⁻¹)) ↔
      ∃ k : ℕ, Odd k ∧ ((g⁻¹ * g') ^ k = 1 ∨ (g⁻¹ * g') ^ k = z) := by
  have hu : g⁻¹ * g' ∈ K₁ := mul_mem (inv_mem hg) hg'
  rw [hS.ab_mul hg hg']
  generalize g⁻¹ * g' = u at hu ⊢
  have hA : g * u⁻¹ * g⁻¹ ∈ K₁ := mul_mem (mul_mem hg (inv_mem hu)) (inv_mem hg)
  have hB : t * u * t⁻¹ ∈ K₂ := hS.t₁ u hu
  have hcAB : Commute (g * u⁻¹ * g⁻¹) (t * u * t⁻¹) := hS.comm _ hA _ hB
  have hzA : Commute z (g * u⁻¹ * g⁻¹) := (hS.comm _ hA z hS.zR).symm
  have hzB : Commute z (t * u * t⁻¹) := hS.comm z hS.zL _ hB
  have hpow : ∀ k : ℕ, (z * (g * u⁻¹ * g⁻¹) * (t * u * t⁻¹)) ^ k =
      z ^ k * ((g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k) := by
    intro k
    have h1 : Commute (z * (g * u⁻¹ * g⁻¹)) (t * u * t⁻¹) := Commute.mul_left hzB hcAB
    rw [h1.mul_pow, hzA.mul_pow, mul_assoc]
  have hAk : ∀ k : ℕ, (g * u⁻¹ * g⁻¹) ^ k = g * (u ^ k)⁻¹ * g⁻¹ := by
    intro k; rw [conj_pow, inv_pow]
  have hBk : ∀ k : ℕ, (t * u * t⁻¹) ^ k = t * u ^ k * t⁻¹ := by
    intro k; rw [conj_pow]
  have hkey : ∀ k : ℕ, u ^ k ∈ Subgroup.zpowers z →
      (g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k = 1 := by
    intro k hk
    have hc := hS.Z_comm (inv_mem hk) (Subgroup.mem_sup_left hg)
    rw [hAk, hBk, hS.Z_tau hk, ← hc, mul_inv_cancel_right, inv_mul_cancel]
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hz)
    rw [hpow] at hk
    have hAkK : (g * u⁻¹ * g⁻¹) ^ k ∈ K₁ := Subgroup.pow_mem _ hA k
    have hBkK : (t * u * t⁻¹) ^ k ∈ K₂ := Subgroup.pow_mem _ hB k
    have hprod : (g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k ∈ Subgroup.zpowers z := by
      have : (g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k = (z ^ k)⁻¹ * z := by
        calc (g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k
            = (z ^ k)⁻¹ * (z ^ k * ((g * u⁻¹ * g⁻¹) ^ k * (t * u * t⁻¹) ^ k)) :=
              (inv_mul_cancel_left _ _).symm
          _ = (z ^ k)⁻¹ * z := by rw [hk]
      rw [this]
      exact mul_mem (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) k))
        (Subgroup.mem_zpowers z)
    obtain ⟨hAZ, _⟩ := hS.both_mem_Z hAkK hBkK hprod
    have hc := hS.Z_comm hAZ (Subgroup.mem_sup_left hg)
    have h1 : (u ^ k)⁻¹ = (g * u⁻¹ * g⁻¹) ^ k := by
      calc (u ^ k)⁻¹ = g⁻¹ * (g * (u ^ k)⁻¹ * g⁻¹) * g := by group
        _ = g⁻¹ * (g * u⁻¹ * g⁻¹) ^ k * g := by rw [hAk k]
        _ = (g * u⁻¹ * g⁻¹) ^ k := by rw [mul_assoc, hc, inv_mul_cancel_left]
    have hukZ : u ^ k ∈ Subgroup.zpowers z := by
      have : (u ^ k)⁻¹ ∈ Subgroup.zpowers z := h1 ▸ hAZ
      simpa using inv_mem this
    rw [hkey k hukZ, mul_one] at hk
    exact ⟨k, hS.odd_of_z_pow hk, hS.mem_Z_iff.1 hukZ⟩
  · rintro ⟨k, hk, hu'⟩
    have hukZ : u ^ k ∈ Subgroup.zpowers z := hS.mem_Z_iff.2 hu'
    have h1 : (z * (g * u⁻¹ * g⁻¹) * (t * u * t⁻¹)) ^ k = z := by
      rw [hpow, hkey k hukZ, mul_one]
      exact hS.z_pow_of_odd hk
    have h2 := Subgroup.pow_mem (Subgroup.zpowers (z * (g * u⁻¹ * g⁻¹) * (t * u * t⁻¹)))
      (Subgroup.mem_zpowers _) k
    rwa [h1] at h2

theorem alpha_eq_iff (hS : ZSetup K₁ K₂ z t) {g g' : X} (hg : g ∈ K₁) (hg' : g' ∈ K₁) :
    g * t * g⁻¹ = g' * t * g'⁻¹ ↔ g⁻¹ * g' ∈ Subgroup.zpowers z := by
  refine conj_eq_iff (H := K₁) ?_ (fun c hc => hS.Z_comm_t hc) hg hg'
  intro c hc h
  have h1 : t * c * t⁻¹ = c := by rw [h, mul_inv_cancel_right]
  have h2 : c ∈ K₂ := by rw [← h1]; exact hS.t₁ c hc
  rw [← hS.inf]
  exact ⟨hc, h2⟩

theorem beta_eq_iff (hS : ZSetup K₁ K₂ z t) {g g' : X} (hg : g ∈ K₁) (hg' : g' ∈ K₁) :
    g * (t * z) * g⁻¹ = g' * (t * z) * g'⁻¹ ↔ g⁻¹ * g' ∈ Subgroup.zpowers z := by
  refine conj_eq_iff (H := K₁) ?_ ?_ hg hg'
  · intro c hc h
    have hcz : c * z = z * c := hS.comm c hc z hS.zR
    have h1 : t * c = c * t := by
      have : t * c * z = c * t * z := by
        calc t * c * z = t * (c * z) := by rw [mul_assoc]
          _ = t * (z * c) := by rw [hcz]
          _ = (t * z) * c := by rw [mul_assoc]
          _ = c * (t * z) := h
          _ = c * t * z := by rw [mul_assoc]
      exact mul_right_cancel this
    have h2 : t * c * t⁻¹ = c := by rw [h1, mul_inv_cancel_right]
    have h3 : c ∈ K₂ := by rw [← h2]; exact hS.t₁ c hc
    rw [← hS.inf]
    exact ⟨hc, h3⟩
  · intro c hc
    have h1 := hS.Z_comm_t hc
    have h2 : z * c = c * z := (hS.Z_comm hc (Subgroup.mem_sup_left hS.zL)).symm
    calc t * z * c = t * (z * c) := by rw [mul_assoc]
      _ = t * (c * z) := by rw [h2]
      _ = (t * c) * z := by rw [mul_assoc]
      _ = (c * t) * z := by rw [h1]
      _ = c * (t * z) := by rw [mul_assoc]

theorem z_not_mem_zpowers_mul_z (hS : ZSetup K₁ K₂ z t) {a : X} (hc : a * z = z * a)
    (hsq : a * a = 1) (hne : a ≠ 1) : z ∉ Subgroup.zpowers (a * z) := by
  intro hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hy : (a * z) * (a * z) = 1 := by
    calc (a * z) * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hc]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [hsq, hS.z_mul_z, one_mul]
  rcases zpow_of_sq_eq_one hy n with h | h
  · exact hS.z_ne_one (by rw [← hn, h])
  · have h1 : a * z = z := h.symm.trans hn
    have h2 : a * z = 1 * z := by rw [one_mul]; exact h1
    exact hne (mul_right_cancel h2)

theorem norm_pow_ne_z (hS : ZSetup K₁ K₂ z t) {κ : X} (hκ : κ ∈ K₁ ⊔ K₂) (m : ℕ) :
    (κ * (t * κ * t⁻¹)) ^ m ≠ z := by
  intro hm
  obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hS.decomp hκ
  have hT₁ : t * κ₁ * t⁻¹ ∈ K₂ := hS.t₁ κ₁ h₁
  have hT₂ : t * κ₂ * t⁻¹ ∈ K₁ := hS.t₂ κ₂ h₂
  have hx : κ₁ * (t * κ₂ * t⁻¹) ∈ K₁ := mul_mem h₁ hT₂
  have hy : κ₂ * (t * κ₁ * t⁻¹) ∈ K₂ := mul_mem h₂ hT₁
  have hQ : κ₁ * κ₂ * (t * (κ₁ * κ₂) * t⁻¹) =
      (κ₁ * (t * κ₂ * t⁻¹)) * (κ₂ * (t * κ₁ * t⁻¹)) := by
    rw [show t * (κ₁ * κ₂) * t⁻¹ = (t * κ₁ * t⁻¹) * (t * κ₂ * t⁻¹) by group]
    generalize t * κ₁ * t⁻¹ = T₁ at hT₁ ⊢
    generalize t * κ₂ * t⁻¹ = T₂ at hT₂ ⊢
    have e2 : T₂ * T₁ = T₁ * T₂ := hS.comm _ hT₂ _ hT₁
    have e3 : T₂ * κ₂ = κ₂ * T₂ := hS.comm _ hT₂ _ h₂
    calc κ₁ * κ₂ * (T₁ * T₂) = κ₁ * (κ₂ * (T₂ * T₁)) := by rw [e2]; simp only [mul_assoc]
      _ = κ₁ * ((κ₂ * T₂) * T₁) := by simp only [mul_assoc]
      _ = κ₁ * ((T₂ * κ₂) * T₁) := by rw [e3]
      _ = (κ₁ * T₂) * (κ₂ * T₁) := by simp only [mul_assoc]
  have hpow : ((κ₁ * (t * κ₂ * t⁻¹)) * (κ₂ * (t * κ₁ * t⁻¹))) ^ m =
      (κ₁ * (t * κ₂ * t⁻¹)) ^ m * (κ₂ * (t * κ₁ * t⁻¹)) ^ m :=
    (show Commute _ _ from hS.comm _ hx _ hy).mul_pow m
  rw [hQ, hpow] at hm
  obtain ⟨hxZ, hyZ⟩ := hS.both_mem_Z (Subgroup.pow_mem _ hx m) (Subgroup.pow_mem _ hy m)
    (by rw [hm]; exact Subgroup.mem_zpowers z)
  have hτy : t * (κ₂ * (t * κ₁ * t⁻¹)) * t⁻¹ = κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) * κ₁ := by
    calc t * (κ₂ * (t * κ₁ * t⁻¹)) * t⁻¹
        = (t * κ₂ * t⁻¹) * ((t * t) * κ₁ * (t * t)⁻¹) := by group
      _ = (t * κ₂ * t⁻¹) * κ₁ := by rw [hS.t2]; group
      _ = κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) * κ₁ := by group
  have hconj1 : (t * (κ₂ * (t * κ₁ * t⁻¹)) * t⁻¹) ^ m = t * (κ₂ * (t * κ₁ * t⁻¹)) ^ m * t⁻¹ :=
    conj_pow
  have hconj2 : (κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) * κ₁) ^ m =
      κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) ^ m * κ₁ := by
    have := conj_pow (a := κ₁⁻¹) (b := κ₁ * (t * κ₂ * t⁻¹)) (i := m)
    simpa using this
  have hy' : t * (κ₂ * (t * κ₁ * t⁻¹)) ^ m * t⁻¹ = κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) ^ m * κ₁ := by
    rw [← hconj1, ← hconj2, hτy]
  rw [hS.Z_tau hyZ] at hy'
  have hc := hS.Z_comm hxZ (Subgroup.mem_sup_left h₁)
  have h3 : κ₁⁻¹ * (κ₁ * (t * κ₂ * t⁻¹)) ^ m * κ₁ = (κ₁ * (t * κ₂ * t⁻¹)) ^ m := by
    rw [mul_assoc, hc, inv_mul_cancel_left]
  rw [h3] at hy'
  rw [hy'] at hm
  have hsq : (κ₁ * (t * κ₂ * t⁻¹)) ^ m * (κ₁ * (t * κ₂ * t⁻¹)) ^ m = 1 := by
    rcases hS.mem_Z_iff.1 hxZ with h | h
    · rw [h, one_mul]
    · rw [h, hS.z_mul_z]
  rw [hsq] at hm
  exact hS.z_ne_one hm.symm

theorem not_mem_zpowers_K_beta [Finite X] (hS : ZSetup K₁ K₂ z t) {a g' : X}
    (ha : a ∈ K₁ ⊔ K₂) (hg' : g' ∈ K₁) :
    z ∉ Subgroup.zpowers (a * (g' * (t * z) * g'⁻¹)) := by
  intro hz
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hz)
  have hβt : g' * (t * z) * g'⁻¹ * t⁻¹ ∈ K₁ ⊔ K₂ := by
    have e : g' * (t * z) * g'⁻¹ * t⁻¹ = g' * (t * (z * g'⁻¹) * t⁻¹) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hg')
      (Subgroup.mem_sup_right (hS.t₁ _ (mul_mem hS.zL (inv_mem hg'))))
  have hκ : a * (g' * (t * z) * g'⁻¹ * t⁻¹) ∈ K₁ ⊔ K₂ := mul_mem ha hβt
  generalize hκdef : a * (g' * (t * z) * g'⁻¹ * t⁻¹) = κ at hκ
  have hw : a * (g' * (t * z) * g'⁻¹) = κ * t := by rw [← hκdef]; group
  have hsq : (κ * t) * (κ * t) = κ * (t * κ * t⁻¹) := by
    calc (κ * t) * (κ * t) = κ * (t * κ * t⁻¹) * (t * t) := by group
      _ = κ * (t * κ * t⁻¹) := by rw [hS.t2, mul_one]
  rw [hw] at hn
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h2 : (κ * t) ^ (2 * m) = (κ * (t * κ * t⁻¹)) ^ m := by rw [pow_mul, pow_two, hsq]
    rw [h2] at hn
    exact hS.norm_pow_ne_z hκ m hn
  · have h2 : (κ * t) ^ (2 * m + 1) = ((κ * (t * κ * t⁻¹)) ^ m * κ) * t := by
      rw [pow_succ, pow_mul, pow_two, hsq]
      exact (mul_assoc _ _ _).symm
    rw [h2] at hn
    have hQK : (κ * (t * κ * t⁻¹)) ^ m * κ ∈ K₁ ⊔ K₂ :=
      mul_mem (Subgroup.pow_mem _ (mul_mem hκ (hS.tau_mem_sup hκ)) m) hκ
    apply hS.tK
    have h3 : t = ((κ * (t * κ * t⁻¹)) ^ m * κ)⁻¹ * z := eq_inv_mul_of_mul_eq hn
    have h4 : ((κ * (t * κ * t⁻¹)) ^ m * κ)⁻¹ * z ∈ K₁ ⊔ K₂ :=
      mul_mem (inv_mem hQK) (Subgroup.mem_sup_left hS.zL)
    rwa [← h3] at h4

theorem pair_cases [Finite X] (hS : ZSetup K₁ K₂ z t) {p : X × X}
    (h1 : (∃ g ∈ K₁, p.1 = g * t * g⁻¹) ∨
      (p.1 ∈ K₁ ⊔ K₂ ∧ p.1 * p.1 = 1 ∧ p.1 ≠ 1 ∧ p.1 ≠ z))
    (h2 : p.2 = z ∨ ∃ g ∈ K₁, p.2 = g * (t * z) * g⁻¹)
    (h3 : z ∈ Subgroup.zpowers (p.1 * p.2)) :
    ∃ g ∈ K₁, ∃ g' ∈ K₁, p = (g * t * g⁻¹, g' * (t * z) * g'⁻¹) := by
  rcases h2 with h2 | ⟨g', hg', h2⟩
  · exfalso
    rw [h2] at h3
    have key : p.1 * z = z * p.1 ∧ p.1 * p.1 = 1 ∧ p.1 ≠ 1 := by
      rcases h1 with ⟨g, hg, h1⟩ | ⟨hK, hsq, hne, _⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [h1]
          have hz1 : Commute z g := (hS.comm_z_sup (Subgroup.mem_sup_left hg)).symm
          have hz2 : Commute z t := hS.tz
          exact ((hz1.mul_right hz2).mul_right hz1.inv_right).eq.symm
        · rw [h1]
          calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
            _ = 1 := by rw [hS.t2]; group
        · intro h
          apply hS.tK
          rw [h1] at h
          have ht1 : t = 1 := by
            calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
              _ = 1 := by rw [h]; group
          rw [ht1]
          exact one_mem _
      · exact ⟨hS.comm_z_sup hK, hsq, hne⟩
    obtain ⟨hc, hsq, hne⟩ := key
    exact hS.z_not_mem_zpowers_mul_z hc hsq hne h3
  · rcases h1 with ⟨g, hg, h1⟩ | ⟨hK, _, _, _⟩
    · exact ⟨g, hg, g', hg', Prod.ext h1 h2⟩
    · exfalso
      rw [h2] at h3
      exact hS.not_mem_zpowers_K_beta hK hg' h3

end ZSetup

end OrdWr

theorem zside_count {X : Type} [Group X] [Finite X] (K₁ K₂ : Subgroup X) (z t : X)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    (ht2 : t * t = 1) (htz : z * t = t * z) (htK : t ∉ K₁ ⊔ K₂)
    (ht₁ : ∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂) (ht₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁) :
    4 * Nat.card {p : X × X //
        ((∃ g ∈ K₁, p.1 = g * t * g⁻¹) ∨
          (p.1 ∈ K₁ ⊔ K₂ ∧ p.1 * p.1 = 1 ∧ p.1 ≠ 1 ∧ p.1 ≠ z)) ∧
        (p.2 = z ∨ ∃ g ∈ K₁, p.2 = g * (t * z) * g⁻¹) ∧
        z ∈ Subgroup.zpowers (p.1 * p.2)} =
      Nat.card K₁ * Nat.card {u : K₁ // ∃ k : ℕ, Odd k ∧ ((u : X) ^ k = 1 ∨ (u : X) ^ k = z)} := by
  have hS : OrdWr.ZSetup K₁ K₂ z t := ⟨hcomm, hinf, hz2, ht2, htz, htK, ht₁, ht₂⟩
  have hZc : Nat.card ((Subgroup.zpowers z).subgroupOf K₁) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.Z_le_left).toEquiv, Nat.card_zpowers, hz2]
  have key := OrdWr.count_pairs ((Subgroup.zpowers z).subgroupOf K₁)
    (fun g : K₁ => (g : X) * t * (g : X)⁻¹) (fun g : K₁ => (g : X) * (t * z) * (g : X)⁻¹)
    (fun p : X × X => ((∃ g ∈ K₁, p.1 = g * t * g⁻¹) ∨
          (p.1 ∈ K₁ ⊔ K₂ ∧ p.1 * p.1 = 1 ∧ p.1 ≠ 1 ∧ p.1 ≠ z)) ∧
        (p.2 = z ∨ ∃ g ∈ K₁, p.2 = g * (t * z) * g⁻¹) ∧
        z ∈ Subgroup.zpowers (p.1 * p.2))
    (fun u : K₁ => ∃ k : ℕ, Odd k ∧ ((u : X) ^ k = 1 ∨ (u : X) ^ k = z))
    (fun g g' => by
      rw [Subgroup.mem_subgroupOf]
      exact hS.alpha_eq_iff g.2 g'.2)
    (fun g g' => by
      rw [Subgroup.mem_subgroupOf]
      exact hS.beta_eq_iff g.2 g'.2)
    (fun g g' => by
      constructor
      · rintro ⟨-, -, h3⟩
        exact (hS.ab_iff g.2 g'.2).1 h3
      · intro h
        exact ⟨Or.inl ⟨g, g.2, rfl⟩, Or.inr ⟨g', g'.2, rfl⟩, (hS.ab_iff g.2 g'.2).2 h⟩)
    (fun p hp => by
      obtain ⟨g, hg, g', hg', rfl⟩ := hS.pair_cases hp.1 hp.2.1 hp.2.2
      exact ⟨⟨g, hg⟩, ⟨g', hg'⟩, rfl⟩)
  rw [hZc] at key
  omega

end CFSG.GH74.GLS.SP.Local
