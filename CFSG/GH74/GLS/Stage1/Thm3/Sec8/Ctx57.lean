module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx56

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

theorem card_le_mul_inf {G : Type*} [Group G] [Finite G] {C S S₁ : Subgroup G} {n : ℕ}
    (hCS : C ≤ S) (h2 : S₁.relIndex S ≤ n) : Nat.card ↥C ≤ n * Nat.card ↥(S₁ ⊓ C) := by
  have h1 : S₁.relIndex C ≤ S₁.relIndex S :=
    Subgroup.relIndex_le_of_le_right hCS (relIndex_ne_zero' _ _)
  have h3 := card_mul_relIndex_of_le (A := S₁ ⊓ C) (B := C) inf_le_right
  rw [Subgroup.inf_relIndex_right] at h3
  have h4 : Nat.card ↥(S₁ ⊓ C) * S₁.relIndex C ≤ Nat.card ↥(S₁ ⊓ C) * n :=
    Nat.mul_le_mul_left _ (h1.trans h2)
  calc Nat.card ↥C = Nat.card ↥(S₁ ⊓ C) * S₁.relIndex C := h3.symm
    _ ≤ Nat.card ↥(S₁ ⊓ C) * n := h4
    _ = n * Nat.card ↥(S₁ ⊓ C) := mul_comm _ _

theorem card_cent_le_conj {G : Type*} [Group G] [Finite G] {S : Subgroup G} {d g : G}
    (hgC : ∀ x ∈ S, x * d = d * x → g⁻¹ * x * g ∈ S) :
    Nat.card ↥(S ⊓ centralizer ({d} : Set G)) ≤
      Nat.card ↥(S ⊓ centralizer ({g⁻¹ * d * g} : Set G)) := by
  have hmem : ∀ x : ↥(S ⊓ centralizer ({d} : Set G)),
      g⁻¹ * (x : G) * g ∈ S ⊓ centralizer ({g⁻¹ * d * g} : Set G) := by
    intro x
    have hxd : (x : G) * d = d * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    refine Subgroup.mem_inf.2 ⟨hgC x x.2.1 hxd, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g⁻¹ * (x : G) * g * (g⁻¹ * d * g) = g⁻¹ * ((x : G) * d) * g := by group
      _ = g⁻¹ * (d * (x : G)) * g := by rw [hxd]
      _ = g⁻¹ * d * g * (g⁻¹ * (x : G) * g) := by group
  refine Nat.card_le_card_of_injective (fun x => ⟨g⁻¹ * (x : G) * g, hmem x⟩) ?_
  intro x y hxy
  have h1 : g⁻¹ * (x : G) * g = g⁻¹ * (y : G) * g := congrArg Subtype.val hxy
  have h2 : (x : G) = (y : G) := mul_left_cancel (mul_right_cancel h1)
  exact Subtype.ext h2

end Basic

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y E₁ E₂ D : Subgroup G} {t w : G}

theorem card_S_eq_of_w_one (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hC : Concl86 z S K₁ W₂ U u h Y D t w) (hE : EData Y U E₁ E₂) (hw : w = 1) :
    Nat.card ↥S = 2 ^ 7 := by
  obtain ⟨hD, hY⟩ := hs.YData_of_concl86 hC hE
  subst hD
  obtain ⟨-, hto, htu', -⟩ := hC.2.2.2.2.1
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hto
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htu : t * u * t⁻¹ = u * z := by rw [ht'] at htu' ⊢; exact htu'
  have hDeq : Nh S h = zpowers t ⊔ zpowers w := hC.2.2.2.1.1
  have htD : t ∈ Nh S h := hDeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hwcent : Nh S h ⊓ centralizer (U : Set G) = zpowers w := hC.2.2.2.2.2.1.1
  have htW : t ∉ Wsub S U := hs.t₀_not_mem_W hII (Nh_le_S htD) htu
  have hD₀ : Nh S h ⊓ Wsub S U = zpowers w := (hs.Nh_inf_centralizer.symm).trans hwcent
  have hcard := hs.card_Nh_eq_two_mul hII htD htW
  rw [hD₀, Nat.card_zpowers, hw, orderOf_one] at hcard
  rw [hY.card_S hII hs, hcard]
  norm_num

theorem relIndex_Y_S (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : Y.relIndex S = 4 := by
  have h1 := Basic.card_mul_relIndex_of_le cfg.hY.Y_le_S
  have h3 : Nat.card ↥S = 256 := by rw [cfg.hS256]; norm_num
  rw [cfg.hY.card, h3] at h1
  omega

theorem sq_mem_Y (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : ∀ s ∈ S, s * s ∈ Y := by
  intro s hs
  obtain ⟨y, hy, d', hd', rfl⟩ := cfg.hY.decomp s hs
  have hd'2 := Nh_sq cfg d' hd'
  have h1 : (y * d') * (y * d') = y * (d' * y * d'⁻¹) := by
    calc (y * d') * (y * d') = y * (d' * y * d'⁻¹) * (d' * d') := by group
      _ = y * (d' * y * d'⁻¹) := by rw [hd'2, mul_one]
  rw [h1]
  exact mul_mem hy (cfg.hY.norm_D d' hd' y hy)

theorem W_dec (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    ∀ x ∈ Wsub S U, x ∈ Y ∨ ∃ y ∈ Y, x = y * w := by
  intro x hx
  obtain ⟨y, hy, d₀, hd₀, hxy⟩ := cfg.hY.decomp x hx.1
  have hd₀W : d₀ ∈ Wsub S U := by
    have : d₀ = y⁻¹ * x := by rw [hxy]; group
    rw [this]
    exact mul_mem (inv_mem (cfg.hY.le_W hy)) hx
  have hmem : d₀ ∈ zpowers w := by
    rw [← cfg.hD₀]
    exact Subgroup.mem_inf.2 ⟨hd₀, hd₀W⟩
  rcases (Basic.mem_zpowers_of_sq' cfg.hw2).1 hmem with h1 | h1
  · left
    rw [hxy, h1, mul_one]
    exact hy
  · right
    exact ⟨y, hy, by rw [hxy, h1]⟩

theorem Nh_comm (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : ∀ a ∈ Nh S h, ∀ b ∈ Nh S h, a * b = b * a := by
  intro a ha b hb
  have h1 := Nh_sq cfg (a * b) (mul_mem ha hb)
  have ha2 := Nh_sq cfg a ha
  have hb2 := Nh_sq cfg b hb
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have h2 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hai, hbi] at h2
  exact h2.symm

theorem four_mul_card_cent_le (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) {c : G} (hDc : ∀ a ∈ Nh S h, a * c = c * a) :
    4 * Nat.card ↥(Y ⊓ centralizer ({c} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({c} : Set G)) := by
  have hY := cfg.hY
  set A := Y ⊓ centralizer ({c} : Set G) with hA
  have hDN : Nh S h ≤ normalizer (A : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ d ∈ Nh S h, ∀ y ∈ A, d * y * d⁻¹ ∈ A := by
      intro d hd y hy
      refine Subgroup.mem_inf.2 ⟨hY.norm_D d hd y hy.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
      have hdc : d * c = c * d := hDc d hd
      have hdc' : d⁻¹ * c = c * d⁻¹ := hDc d⁻¹ (inv_mem hd)
      calc d * y * d⁻¹ * c = d * y * (d⁻¹ * c) := by group
        _ = d * y * (c * d⁻¹) := by rw [hdc']
        _ = d * (y * c) * d⁻¹ := by group
        _ = d * (c * y) * d⁻¹ := by rw [hyc]
        _ = (d * c) * y * d⁻¹ := by group
        _ = (c * d) * y * d⁻¹ := by rw [hdc]
        _ = c * (d * y * d⁻¹) := by group
    intro y
    constructor
    · intro hy
      exact key d hd y hy
    · intro hy
      have h1 := key d⁻¹ (inv_mem hd) _ hy
      have e : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hcard := Basic.card_sup_mul_card_inf' (A := A) (B := Nh S h) hDN
  have hinf : A ⊓ Nh S h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Y ⊓ Nh S h := Subgroup.mem_inf.2 ⟨hx.1.1, hx.2⟩
    rw [hY.Y_inf_Nh hII hs, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  rw [hinf, Subgroup.card_bot, mul_one, cfg.hD4] at hcard
  have hsup : A ⊔ Nh S h ≤ S ⊓ centralizer ({c} : Set G) := by
    apply sup_le
    · intro x hx
      exact Subgroup.mem_inf.2 ⟨hY.Y_le_S hx.1, hx.2⟩
    · intro d hd
      exact Subgroup.mem_inf.2 ⟨Nh_le_S hd, Subgroup.mem_centralizer_singleton_iff.2 (hDc d hd)⟩
  have := Subgroup.card_le_of_le hsup
  omega

theorem d_mem_Nh (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : t * w ∈ Nh S h := mul_mem cfg.htD cfg.hwD

theorem d_not_W (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : t * w ∉ Wsub S U := by
  intro hd
  apply cfg.htW
  have : t = (t * w) * w⁻¹ := by group
  rw [this]
  exact mul_mem hd (inv_mem cfg.hwW)

theorem d_ne_one (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : t * w ≠ 1 := fun e =>
  d_not_W cfg (e ▸ one_mem _)

theorem d_u (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    (t * w) * u * (t * w)⁻¹ = u * z := by
  have hw : w * u * w⁻¹ = u := hs.W_cent_U cfg.hwW hs.u_mem
  calc (t * w) * u * (t * w)⁻¹ = t * (w * u * w⁻¹) * t⁻¹ := by group
    _ = t * u * t⁻¹ := by rw [hw]
    _ = u * z := cfg.htu

theorem d_z (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : (t * w) * z * (t * w)⁻¹ = z := by
  have hw : w * z * w⁻¹ = z := hs.W_cent_U cfg.hwW hs.z_mem
  have htS : t ∈ S := Nh_le_S cfg.htD
  have hzt : t * z * t⁻¹ = z := by rw [← hs.z_comm hII htS]; group
  calc (t * w) * z * (t * w)⁻¹ = t * (w * z * w⁻¹) * t⁻¹ := by group
    _ = t * z * t⁻¹ := by rw [hw]
    _ = z := hzt

theorem d_swap (h87 : conjugate E₁ t = E₁) (h88 : conjugate E₁ w = E₂) :
    ∀ y, (t * w) * y * (t * w)⁻¹ ∈ E₁ ↔ y ∈ E₂ := by
  intro y
  have e : (t * w) * y * (t * w)⁻¹ = t * (w * y * w⁻¹) * t⁻¹ := by group
  rw [e]
  constructor
  · intro hy
    have h1 : w * y * w⁻¹ ∈ conjugate E₁ t := mem_conjugate_iff.2 hy
    rw [h87] at h1
    have h2 : y ∈ conjugate E₁ w := mem_conjugate_iff.2 h1
    rwa [h88] at h2
  · intro hy
    rw [← h88] at hy
    have h1 : w * y * w⁻¹ ∈ E₁ := mem_conjugate_iff.1 hy
    rw [← h87] at h1
    exact mem_conjugate_iff.1 h1

theorem d_not_P (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hE : EData Y U E₁ E₂)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hII : II4_4_4_center)
    (h87 : ∀ s ∈ Pz S z, orderOf s = 2 → s⁻¹ * u * s = u * z →
      conjugate E₁ s = E₁ ∧ conjugate E₂ s = E₂)
    (hswap : ∀ y, (t * w) * y * (t * w)⁻¹ ∈ E₁ ↔ y ∈ E₂) : t * w ∉ Pz S z := by
  intro hdP
  have hd2 := tw_sq cfg
  have hdo : orderOf (t * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd2) (d_ne_one cfg)
  have hdinv : (t * w)⁻¹ = t * w := inv_eq_of_mul_eq_one_right hd2
  have hdu : (t * w)⁻¹ * u * (t * w) = u * z := by
    have := d_u hs cfg
    rw [hdinv] at this ⊢
    exact this
  obtain ⟨h1, -⟩ := h87 _ hdP hdo hdu
  apply E₁_ne_E₂ hs hE
  ext y
  constructor
  · intro hy
    have : y ∈ conjugate E₁ (t * w) := by rw [h1]; exact hy
    exact (hswap y).1 (mem_conjugate_iff.1 this)
  · intro hy
    have := mem_conjugate_iff.2 ((hswap y).2 hy)
    rwa [h1] at this

theorem cent_U_d (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    ∀ c ∈ U, c * (t * w) = (t * w) * c → c = 1 ∨ c = z := by
  intro c hc hcd
  have hdc : (t * w) * c * (t * w)⁻¹ = c := by rw [← hcd]; group
  have hz1 := hs.z_ne
  have hzz := hs.z_sq
  rcases hs.U_elems c hc with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1, d_u hs cfg] at hdc
    apply hz1
    have : u * z = u * 1 := by rw [mul_one]; exact hdc
    exact mul_left_cancel this
  · exfalso
    rw [h1] at hdc
    have h2 : (t * w) * (u * z) * (t * w)⁻¹ = u := by
      calc (t * w) * (u * z) * (t * w)⁻¹ =
          ((t * w) * u * (t * w)⁻¹) * ((t * w) * z * (t * w)⁻¹) := by group
        _ = (u * z) * z := by rw [d_u hs cfg, d_z hII hs cfg]
        _ = u := by rw [mul_assoc, hzz, mul_one]
    rw [h2] at hdc
    apply hz1
    have : u * 1 = u * z := by rw [mul_one]; exact hdc
    exact (mul_left_cancel this).symm

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
