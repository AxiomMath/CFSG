module

public import CFSG.Open.Catalog
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG.Open (WreathedTwoGroup)

def ex4 (a : Multiplicative (ZMod (2 ^ 2))) : ℕ := (Multiplicative.toAdd a).val

def ex2 (c : Multiplicative (ZMod 2)) : ℕ := (Multiplicative.toAdd c).val

variable {G : Type} [Group G] [Finite G]

theorem pow_mod_four {u : G} (hu : u ^ 4 = 1) (n : ℕ) : u ^ (n % 4) = u ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hu, one_pow, mul_one]

theorem ex4_mul (a b : Multiplicative (ZMod (2 ^ 2))) :
    ex4 (a * b) = (ex4 a + ex4 b) % 4 := by
  unfold ex4
  show (Multiplicative.toAdd a + Multiplicative.toAdd b).val = _
  rw [ZMod.val_add]
  rfl

theorem ex4_lt (a : Multiplicative (ZMod (2 ^ 2))) : ex4 a < 4 := by
  unfold ex4
  exact ZMod.val_lt _

theorem ex2_lt (c : Multiplicative (ZMod 2)) : ex2 c < 2 := by
  unfold ex2
  exact ZMod.val_lt _

theorem ex2_mul (c d : Multiplicative (ZMod 2)) : ex2 (c * d) = (ex2 c + ex2 d) % 2 := by
  unfold ex2
  show (Multiplicative.toAdd c + Multiplicative.toAdd d).val = _
  rw [ZMod.val_add]

structure WData (u v s : G) : Prop where
  hu4 : u ^ 4 = 1
  hv4 : v ^ 4 = 1
  huv : Commute u v
  hs2 : s ^ 2 = 1
  hsu : s * u * s⁻¹ = v
  hsv : s * v * s⁻¹ = u
  hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → 4 ∣ a ∧ 4 ∣ b
  hsnot : ∀ a b : ℕ, s ≠ u ^ a * v ^ b

namespace WData

variable {u v s : G}

theorem s_pow_u (h : WData u v s) (a : ℕ) : s * u ^ a = v ^ a * s := by
  have e : s * u ^ a * s⁻¹ = (s * u * s⁻¹) ^ a := (conj_pow).symm
  rw [h.hsu] at e
  rw [← e]
  group

theorem s_pow_v (h : WData u v s) (a : ℕ) : s * v ^ a = u ^ a * s := by
  have e : s * v ^ a * s⁻¹ = (s * v * s⁻¹) ^ a := (conj_pow).symm
  rw [h.hsv] at e
  rw [← e]
  group

theorem uv_mul (h : WData u v s) (a b c d : ℕ) :
    u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ (a + c) * v ^ (b + d) := by
  have hc : v ^ b * u ^ c = u ^ c * v ^ b := ((h.huv.pow_pow c b)).symm.eq
  calc u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ a * (v ^ b * u ^ c) * v ^ d := by group
    _ = u ^ a * (u ^ c * v ^ b) * v ^ d := by rw [hc]
    _ = u ^ (a + c) * v ^ (b + d) := by rw [pow_add, pow_add]; group

theorem pow_s_mod (h : WData u v s) (c : ℕ) : s ^ c = s ^ (c % 2) := by
  conv_lhs => rw [← Nat.mod_add_div c 2]
  rw [pow_add, pow_mul, h.hs2, one_pow, mul_one]

theorem s_uv (h : WData u v s) (a b : ℕ) : s * (u ^ a * v ^ b) = u ^ b * v ^ a * s := by
  calc s * (u ^ a * v ^ b) = (s * u ^ a) * v ^ b := (mul_assoc _ _ _).symm
    _ = (v ^ a * s) * v ^ b := by rw [h.s_pow_u]
    _ = v ^ a * (s * v ^ b) := mul_assoc _ _ _
    _ = v ^ a * (u ^ b * s) := by rw [h.s_pow_v]
    _ = (v ^ a * u ^ b) * s := (mul_assoc _ _ _).symm
    _ = (u ^ b * v ^ a) * s := by rw [(h.huv.pow_pow b a).eq]

theorem uv_inv (h : WData u v s) (p q : ℕ) :
    u ^ p * v ^ q * (u ^ (3 * p) * v ^ (3 * q)) = 1 := by
  rw [h.uv_mul, show p + 3 * p = 4 * p by ring, show q + 3 * q = 4 * q by ring, pow_mul, pow_mul,
    h.hu4, h.hv4, one_pow, one_pow, mul_one]

end WData

theorem ex2_one : ex2 1 = 0 := by decide

theorem ex2_ofAdd_one : ex2 (Multiplicative.ofAdd 1) = 1 := by decide

theorem nf_one {u v s : G} (h : WData u v s) (p0 p1 q0 q1 e : ℕ) :
    u ^ (p0 + q0) * v ^ (p1 + q1) * s ^ e =
      (u ^ p0 * v ^ p1 * s ^ 0) * (u ^ q0 * v ^ q1 * s ^ e) := by
  calc u ^ (p0 + q0) * v ^ (p1 + q1) * s ^ e
      = (u ^ p0 * v ^ p1 * (u ^ q0 * v ^ q1)) * s ^ e := by rw [h.uv_mul]
    _ = u ^ p0 * v ^ p1 * (u ^ q0 * v ^ q1 * s ^ e) := by rw [mul_assoc]
    _ = (u ^ p0 * v ^ p1 * s ^ 0) * (u ^ q0 * v ^ q1 * s ^ e) := by rw [pow_zero, mul_one]

theorem nf_two {u v s : G} (h : WData u v s) (p0 p1 q0 q1 e : ℕ) :
    u ^ (p0 + q1) * v ^ (p1 + q0) * s ^ (1 + e) =
      (u ^ p0 * v ^ p1 * s ^ 1) * (u ^ q0 * v ^ q1 * s ^ e) := by
  symm
  calc (u ^ p0 * v ^ p1 * s ^ 1) * (u ^ q0 * v ^ q1 * s ^ e)
      = u ^ p0 * v ^ p1 * (s ^ 1 * (u ^ q0 * v ^ q1 * s ^ e)) := by simp only [mul_assoc]
    _ = u ^ p0 * v ^ p1 * ((s * (u ^ q0 * v ^ q1)) * s ^ e) := by simp only [pow_one, mul_assoc]
    _ = u ^ p0 * v ^ p1 * ((u ^ q1 * v ^ q0 * s) * s ^ e) := by rw [h.s_uv]
    _ = (u ^ p0 * v ^ p1 * (u ^ q1 * v ^ q0)) * (s * s ^ e) := by simp only [mul_assoc]
    _ = u ^ (p0 + q1) * v ^ (p1 + q0) * (s * s ^ e) := by rw [h.uv_mul]
    _ = u ^ (p0 + q1) * v ^ (p1 + q0) * s ^ (1 + e) := by rw [add_comm 1 e, pow_succ']

def wmap (u v s : G) (w : Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) : G :=
  u ^ ex4 (w.left (Multiplicative.ofAdd 0)) * v ^ ex4 (w.left (Multiplicative.ofAdd 1)) *
    s ^ ex2 w.right

theorem wmap_mul {u v s : G} (h : WData u v s)
    (w1 w2 : Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) :
    wmap u v s (w1 * w2) = wmap u v s w1 * wmap u v s w2 := by
  obtain ⟨f, c⟩ := w1
  obtain ⟨g, d⟩ := w2
  have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := by revert c; decide
  have h01 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ * Multiplicative.ofAdd 0 =
      Multiplicative.ofAdd 1 := by decide
  have h10 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ * Multiplicative.ofAdd 1 =
      Multiplicative.ofAdd 0 := by decide
  rcases hc with rfl | rfl
  · simp only [wmap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, inv_one,
      one_mul, Pi.mul_apply, ex2_one]
    rw [ex4_mul, ex4_mul, pow_mod_four h.hu4, pow_mod_four h.hv4]
    exact nf_one h _ _ _ _ _
  · simp only [wmap, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, Pi.mul_apply,
      h01, h10, ex2_ofAdd_one]
    rw [ex4_mul, ex4_mul, ex2_mul, ex2_ofAdd_one, pow_mod_four h.hu4, pow_mod_four h.hv4]
    rw [← WData.pow_s_mod h]
    exact nf_two h _ _ _ _ _

def wHom {u v s : G} (h : WData u v s) :
    Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2) →* G :=
  MonoidHom.mk' (wmap u v s) (fun a b => wmap_mul h a b)

theorem ex4_eq_zero_iff : ∀ a : Multiplicative (ZMod (2 ^ 2)), ex4 a = 0 → a = 1 := by decide

theorem ex2_eq_zero_iff : ∀ c : Multiplicative (ZMod 2), ex2 c = 0 → c = 1 := by decide

theorem mul_two_cases : ∀ x : Multiplicative (ZMod 2),
    x = Multiplicative.ofAdd 0 ∨ x = Multiplicative.ofAdd 1 := by decide

theorem wHom_injective {u v s : G} (h : WData u v s) : Function.Injective (wHom h) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  change wmap u v s w = 1 at hw
  obtain ⟨L, c⟩ := w
  unfold wmap at hw
  dsimp only at hw
  have he2 := ex2_lt c
  have hc : ex2 c = 0 ∨ ex2 c = 1 := by omega
  rcases hc with hc | hc
  ·
    rw [hc, pow_zero, mul_one] at hw
    obtain ⟨h4a, h4b⟩ := h.hind _ _ hw
    have hA : ex4 (L (Multiplicative.ofAdd 0)) = 0 := by
      have := ex4_lt (L (Multiplicative.ofAdd 0))
      omega
    have hB : ex4 (L (Multiplicative.ofAdd 1)) = 0 := by
      have := ex4_lt (L (Multiplicative.ofAdd 1))
      omega
    have hL : L = 1 := by
      funext x
      rcases mul_two_cases x with rfl | rfl
      · exact ex4_eq_zero_iff _ hA
      · exact ex4_eq_zero_iff _ hB
    have hc1 : c = 1 := ex2_eq_zero_iff c hc
    subst hL
    subst hc1
    rfl
  ·
    rw [hc, pow_one] at hw
    exfalso
    apply h.hsnot (3 * ex4 (L (Multiplicative.ofAdd 0))) (3 * ex4 (L (Multiplicative.ofAdd 1)))
    have hinv : s = (u ^ ex4 (L (Multiplicative.ofAdd 0)) *
        v ^ ex4 (L (Multiplicative.ofAdd 1)))⁻¹ := eq_inv_of_mul_eq_one_right hw
    rw [hinv]
    exact inv_eq_of_mul_eq_one_right (h.uv_inv _ _)

theorem wmap_mem {T : Subgroup G} {u v s : G} (hu : u ∈ T) (hv : v ∈ T) (hs : s ∈ T)
    (w : Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) : wmap u v s w ∈ T := by
  unfold wmap
  exact T.mul_mem (T.mul_mem (T.pow_mem hu _) (T.pow_mem hv _)) (T.pow_mem hs _)

theorem wreath_iso {T : Subgroup G} (hT : Nat.card ↥T = 32) {u v s : G} (hu : u ∈ T) (hv : v ∈ T)
    (hs : s ∈ T) (h : WData u v s) : Nonempty (↥T ≃* WreathedTwoGroup 2) := by
  let Φ : Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2) →* ↥T :=
    (wHom h).codRestrict T (wmap_mem hu hv hs)
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply wHom_injective h
    exact congrArg Subtype.val hab
  have h4 : Nat.card (Multiplicative (ZMod (2 ^ 2))) = 4 := by
    rw [Nat.card_congr (Multiplicative.ofAdd : ZMod (2 ^ 2) ≃ Multiplicative (ZMod (2 ^ 2))).symm]
    simp
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).symm]
    simp
  have hcard : Nat.card (Multiplicative (ZMod (2 ^ 2)) ≀ᵣ Multiplicative (ZMod 2)) =
      Nat.card ↥T := by
    rw [RegularWreathProduct.card, h4, h2, hT]
    norm_num
  have hbij : Function.Bijective Φ := (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcard⟩
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm⟩

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
