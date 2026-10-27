module

public import CFSG.GH74.GLS.LU.Local.FiveL86b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Gen

variable {G : Type} [Group G]

theorem card_le_four_mul_card_inf_centralizer {X P : Subgroup G} (hX : Nat.card ↥X = 5)
    (hP : P ≤ normalizer (X : Set G)) :
    Nat.card ↥P ≤ 4 * Nat.card ↥(P ⊓ centralizer (X : Set G) : Subgroup G) := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥X := isCyclic_of_prime_card hX
  have hfin : Finite ↥X := Nat.finite_of_card_ne_zero (by omega)
  let ψ : ↥P →* MulAut ↥X := (X.normalizerMonoidHom).comp (Subgroup.inclusion hP)
  have hker : ψ.ker = (centralizer (X : Set G)).subgroupOf P := by
    ext ⟨r, hr⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have h1 : ψ ⟨r, hr⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h]; rfl
      have h2 : ((ψ ⟨r, hr⟩ ⟨x, hx⟩ : ↥X) : G) = r * x * r⁻¹ := by simp [ψ]
      rw [h1] at h2
      have h3 : x = r * x * r⁻¹ := h2
      calc x * r = (r * x * r⁻¹) * r := by rw [← h3]
        _ = r * x := by group
    · intro h
      apply MulEquiv.ext
      intro ⟨x, hx⟩
      apply Subtype.ext
      have h2 : ((ψ ⟨r, hr⟩ ⟨x, hx⟩ : ↥X) : G) = r * x * r⁻¹ := by simp [ψ]
      rw [h2]
      show r * x * r⁻¹ = x
      have := h x hx
      calc r * x * r⁻¹ = (x * r) * r⁻¹ := by rw [this]
        _ = x := by group
  have h1 : Nat.card ↥(ψ.ker) = Nat.card ↥(P ⊓ centralizer (X : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 := Subgroup.index_mul_card ψ.ker
  rw [Subgroup.index_ker] at h2
  have h3 : Nat.card ↥ψ.range ≤ 4 := by
    have := Subgroup.card_le_card_group ψ.range
    rwa [IsCyclic.card_mulAut, hX, Nat.totient_prime (by norm_num)] at this
  rw [← h2, h1]
  exact Nat.mul_le_mul_right _ h3

end Gen

section C86

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.H_card (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥H = 16 := by
  obtain ⟨e⟩ := c.b66.H_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4), Nat.card_zmod]
  rw [this]

theorem Cfg2.H_pow_four (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : ∀ h ∈ H, h ^ 4 = 1 := by
  obtain ⟨e⟩ := c.b66.H_iso
  intro h hh
  have key : ∀ q : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), q ^ 4 = 1 := by decide
  have h1 : e ⟨h, hh⟩ ^ 4 = 1 := key _
  have h2 : e (⟨h, hh⟩ ^ 4) = e 1 := by rw [map_pow, h1, map_one]
  have h3 : (⟨h, hh⟩ : ↥H) ^ 4 = 1 := e.injective h2
  have := congrArg Subtype.val h3
  simpa using this

theorem Cfg2.H_le_normalizer_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    H ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) := fun h hh =>
  mem_normalizer_of_cjL_eq (c.hinv_X2 h hh)

theorem Cfg2.card_CK1u (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G) : Subgroup G) = 4 := by
  have h := c.ctx.eps.H_card
  have h4 : (Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G) : Subgroup G) : ℤ) = 4 := by
    rw [h, c.ctx.pf]; norm_num
  exact_mod_cast h4

theorem Cfg2.H_cent_X2_le_K1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    H ⊓ centralizer ((XB t X₁ : Subgroup G) : Set G) ≤ H ⊓ K₁ := by
  intro h hh
  obtain ⟨hH, hC⟩ := hh
  refine ⟨hH, ?_⟩
  have hz : h * z = z * h := (c.b66.H_cent h hH).1
  have hmem : h ∈ centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨hC, Subgroup.mem_centralizer_singleton_iff.mpr hz⟩
  rw [c.b82.CC_X2] at hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute (A := XB t X₁) (B := K₁)
    (fun a ha b hb => (c.hc.comm b hb a (c.X2_le_K2 ha)).symm)).mp hmem
  have hab : Commute a b := (c.hc.comm b hb a (c.X2_le_K2 ha)).symm
  have h4 := c.H_pow_four _ hH
  rw [hab.mul_pow] at h4
  have ha4K1 : a ^ 4 ∈ K₁ := by
    have := eq_inv_of_mul_eq_one_left h4
    rw [this]; exact inv_mem (pow_mem hb 4)
  have ha4K2 : a ^ 4 ∈ K₂ := pow_mem (c.X2_le_K2 ha) 4
  have hsq := c.K1_inf_K2_sq _ ⟨ha4K1, ha4K2⟩
  have ha5 : a ^ 5 = 1 := pow_five_of_card c.card_X2 ha
  have ha8 : a ^ 8 = 1 := by
    calc a ^ 8 = a ^ 4 * a ^ 4 := by group
      _ = 1 := hsq
  have ha1 : a = 1 := by
    calc a = (a ^ 8) ^ 2 * ((a ^ 5)⁻¹) ^ 3 := by group
      _ = 1 := by rw [ha8, ha5]; simp
  rw [ha1, one_mul]
  exact hb

theorem Cfg2.K1_inf_cent_le_H (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    K₁ ⊓ centralizer ({u} : Set G) ≤ H := by
  have hle : H ⊓ K₁ ≤ K₁ ⊓ centralizer ({u} : Set G) := by
    intro x hx
    exact ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (c.b66.H_cent x hx.1).2⟩
  have hcard : 4 ≤ Nat.card ↥(H ⊓ K₁ : Subgroup G) := by
    have h1 := card_le_four_mul_card_inf_centralizer c.card_X2 c.H_le_normalizer_X2
    rw [c.H_card] at h1
    have h3 := Subgroup.card_le_of_le c.H_cent_X2_le_K1
    omega
  have heq : H ⊓ K₁ = K₁ ⊓ centralizer ({u} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [c.card_CK1u]; exact hcard)
  rw [← heq]
  exact inf_le_left

omit [Finite G] in
theorem z_mem_UU (z u : G) : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

omit [Finite G] in
theorem u_mem_UU (z u : G) : u ∈ UU z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem Cfg3.u_inv_X2 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ a ∈ XB t X₁, u * a * u⁻¹ = a⁻¹ := fun a ha =>
  c.b83.u_inv a (Subgroup.mem_sup_left ((le_sup_right : XB t X₁ ≤ XX t X₁) ha))

theorem Cfg3.CU_inf_N_X2_le_H (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) {m : G}
    (hm : m ∈ centralizer ((UU z u : Subgroup G) : Set G))
    (hN : m ∈ normalizer ((XB t X₁ : Subgroup G) : Set G)) : m ∈ H := by
  have hzm : m * z = z * m := by
    have := Subgroup.mem_centralizer_iff.mp hm z (z_mem_UU z u)
    exact this.symm
  have hum : m * u = u * m := by
    have := Subgroup.mem_centralizer_iff.mp hm u (u_mem_UU z u)
    exact this.symm
  have hmem : m ∈ normalizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨hN, Subgroup.mem_centralizer_singleton_iff.mpr hzm⟩
  rw [c.b82.NC_X2] at hmem
  have hcommXK : ∀ a ∈ XB t X₁, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb =>
    (c.hc.comm b hb a (c.X2_le_K2 ha)).symm
  have hnormH : ∀ l ∈ H, ∀ e ∈ XB t X₁ ⊔ K₁, l * e * l⁻¹ ∈ XB t X₁ ⊔ K₁ := by
    intro l hl e he
    have hcj : cjL l (XB t X₁ ⊔ K₁) = XB t X₁ ⊔ K₁ := by
      rw [cjL_sup, c.hinv_X2 l hl, (c.b66.H_normK l hl).1]
    have := mem_cjL_self (g := l) he
    rwa [hcj] at this
  obtain ⟨e, he, h, hh, rfl⟩ := mem_sup_of_normalizes hnormH hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hcommXK).mp he
  have hu1 : u * a * u⁻¹ = a⁻¹ := c.u_inv_X2 a ha
  have hu2 : u * b * u⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp c.hs.u_norm b).mp hb
  have hu3 : u * h * u⁻¹ = h := by
    have := (c.b66.H_cent h hh).2
    calc u * h * u⁻¹ = (h * u) * u⁻¹ := by rw [this]
      _ = h := by group
  have hfix : u * (a * b * h) * u⁻¹ = a * b * h := by
    calc u * (a * b * h) * u⁻¹ = (a * b * h * u) * u⁻¹ := by rw [← hum]
      _ = a * b * h := by group
  have hsplit : u * (a * b * h) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) * (u * h * u⁻¹) := by group
  rw [hsplit, hu1, hu3] at hfix
  set b' := u * b * u⁻¹ with hb'
  have h1 : a⁻¹ * b' = a * b := mul_right_cancel hfix
  have h2 : b' * b⁻¹ = a * a := by
    calc b' * b⁻¹ = a * (a⁻¹ * b') * b⁻¹ := by group
      _ = a * (a * b) * b⁻¹ := by rw [h1]
      _ = a * a := by group
  have ha2K1 : a * a ∈ K₁ := by rw [← h2]; exact mul_mem hu2 (inv_mem hb)
  have ha2K2 : a * a ∈ K₂ := mul_mem (c.X2_le_K2 ha) (c.X2_le_K2 ha)
  have hsq := c.K1_inf_K2_sq _ ⟨ha2K1, ha2K2⟩
  have ha5 : a ^ 5 = 1 := pow_five_of_card c.card_X2 ha
  have ha4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a * a) * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hsq
  have ha1 : a = 1 := by
    calc a = a ^ 5 * (a ^ 4)⁻¹ := by group
      _ = 1 := by rw [ha5, ha4]; simp
  rw [ha1] at h2 ⊢
  have hb'b : b' = b := by
    have : b' * b⁻¹ = 1 := by rw [h2]; simp
    exact mul_inv_eq_one.mp this
  have hbC : b ∈ K₁ ⊓ centralizer ({u} : Set G) := by
    refine ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have : u * b * u⁻¹ = b := hb'b
    calc b * u = (u * b * u⁻¹) * u := by rw [this]
      _ = u * b := by group
  rw [one_mul]
  exact mul_mem (c.K1_inf_cent_le_H hbC) hh

end C86



end CFSG.GH74.GLS.LU.Local.Five
