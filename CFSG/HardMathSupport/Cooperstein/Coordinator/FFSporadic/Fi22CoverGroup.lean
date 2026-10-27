module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem comm_mul_central_left {a b k : G} (hk : ∀ g, k * g = g * k) : ⁅a * k, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (commutatorElement_eq_one_iff_mul_comm (g₁ := k) (g₂ := b)).2 (hk b)]
  simp

theorem comm_mul_central_right {a b k : G} (hk : ∀ g, k * g = g * k) : ⁅a, b * k⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    (commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := k)).2 (hk a).symm]
  simp

theorem comm_pow_right_of_central {a b : G} (h : ∀ g, ⁅a, b⁆ * g = g * ⁅a, b⁆) (n : ℕ) :
    ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n :=
  (Commute.commutatorElement_pow_right (a := a) (b := b) (h b).symm n).symm

theorem comm_pow_left_of_central {a b : G} (h : ∀ g, ⁅a, b⁆ * g = g * ⁅a, b⁆) (n : ℕ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n :=
  (Commute.commutatorElement_pow_left (a := a) (b := b) (h a).symm n).symm

theorem comm_eq_one_of_sign {c b d e k₁ k₂ : G}
    (hu : ∀ g, ⁅c, b⁆ * g = g * ⁅c, b⁆) (hk₁ : ∀ g, k₁ * g = g * k₁)
    (hk₂ : ∀ g, k₂ * g = g * k₂) (hce : c * e = e * c)
    (hdc : d * c = c * k₂ * d) (hdb : d * b = b * (b * (e * d)) * k₁) : ⁅c, b⁆ = 1 := by
  have h1 : d * c * d⁻¹ = c * k₂ := by rw [hdc, mul_inv_cancel_right]
  have h2 : d * b * d⁻¹ = b * (b * (e * k₁)) := by
    rw [mul_inv_eq_iff_eq_mul, hdb]
    simp only [mul_assoc]
    rw [hk₁ d]
  have key := conjugate_commutatorElement c b d
  rw [h1, h2] at key
  have hcen : d * ⁅c, b⁆ * d⁻¹ = ⁅c, b⁆ := by rw [← hu d, mul_inv_cancel_right]
  rw [hcen] at key
  have h3 : ⁅c * k₂, b * (b * (e * k₁))⁆ = ⁅c, b * b⁆ := by
    rw [comm_mul_central_left hk₂, ← mul_assoc b b, ← mul_assoc (b * b), comm_mul_central_right hk₁,
      commutatorElement_mul_right_eq_mul_conj,
      (commutatorElement_eq_one_iff_mul_comm (g₁ := c) (g₂ := e)).2 hce]
    simp [mul_assoc]
  rw [h3, ← pow_two, comm_pow_right_of_central hu 2, pow_two] at key
  have := congrArg (fun t => ⁅c, b⁆⁻¹ * t) key
  simpa using this.symm

theorem pow_three_eq_one_of_sign {b d e k : G} (hb3 : ∀ g, b ^ 3 * g = g * b ^ 3)
    (hk : ∀ g, k * g = g * k) (hk3 : k ^ 3 = 1) (he3 : e ^ 3 = 1) (hbe : b * e = e * b)
    (hdb : d * b = b * (b * (e * d)) * k) : b ^ 3 = 1 := by
  have h2 : d * b * d⁻¹ = b ^ 2 * (e * k) := by
    rw [mul_inv_eq_iff_eq_mul, hdb, pow_two]
    simp only [mul_assoc]
    rw [hk d]
  have hc : Commute (b ^ 2) (e * k) := by
    refine Commute.mul_right ((Commute.pow_left (a := b) (b := e) hbe 2)) ?_
    exact Commute.pow_left (a := b) (b := k) (hk b).symm 2
  have hek : (e * k) ^ 3 = 1 := by
    rw [Commute.mul_pow (hk e).symm, he3, hk3, one_mul]
  have h3 : (d * b * d⁻¹) ^ 3 = d * b ^ 3 * d⁻¹ := conj_pow
  have hcen : d * b ^ 3 * d⁻¹ = b ^ 3 := by rw [← hb3 d, mul_inv_cancel_right]
  rw [h2, hc.mul_pow, hek, mul_one, ← pow_mul, hcen] at h3
  have h4 : b ^ 3 = b ^ 3 * b ^ 3 := by rw [← pow_add]; simpa using h3.symm
  have := congrArg (fun t => (b ^ 3)⁻¹ * t) h4
  simpa using this.symm

theorem comm_eq_one_of_cross {a b d e e' k k' : G}
    (hu : ∀ g, ⁅a, b⁆ * g = g * ⁅a, b⁆) (hk : ∀ g, k * g = g * k) (hk' : ∀ g, k' * g = g * k')
    (hbe : Commute b e) (hae' : Commute a e') (hee : Commute e e')
    (hda : d * a = a * (a * (e * d)) * k) (hdb : d * b = b * (e' * d) * k') : ⁅a, b⁆ = 1 := by
  have h1 : d * a * d⁻¹ = a * a * e * k := by
    rw [mul_inv_eq_iff_eq_mul, hda]
    simp only [mul_assoc]
    rw [hk d]
  have h2 : d * b * d⁻¹ = b * e' * k' := by
    rw [mul_inv_eq_iff_eq_mul, hdb]
    simp only [mul_assoc]
    rw [hk' d]
  have key := conjugate_commutatorElement a b d
  rw [h1, h2] at key
  have hcen : d * ⁅a, b⁆ * d⁻¹ = ⁅a, b⁆ := by rw [← hu d, mul_inv_cancel_right]
  rw [hcen, comm_mul_central_left hk, comm_mul_central_right hk'] at key
  have h3 : ⁅a * a * e, b * e'⁆ = ⁅a * a, b⁆ := by
    have h4 : ⁅e, b * e'⁆ = 1 := (Commute.mul_right hbe.symm hee).commutator_eq
    have h5 : ⁅a * a, e'⁆ = 1 := (Commute.mul_left hae' hae').commutator_eq
    have h6 : ⁅a * a, b * e'⁆ = ⁅a * a, b⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, h5]
      simp
    rw [commutatorElement_mul_left_eq_conj_mul, h4, h6]
    simp
  rw [h3, ← pow_two, comm_pow_left_of_central hu 2, pow_two] at key
  have := congrArg (fun t => ⁅a, b⁆⁻¹ * t) key
  simpa using this.symm

theorem comm_two_letter {x y z : G} (hz : ⁅x, y⁆ = z) (hxz : Commute x z) (hyz : Commute y z)
    (hz3 : z ^ 3 = 1) (a b c d : ℕ) :
    ⁅x ^ a * y ^ b, x ^ c * y ^ d⁆ = z ^ (a * d + 2 * (b * c)) := by
  have hxy : ∀ m n : ℕ, ⁅x ^ m, y ^ n⁆ = z ^ (n * m) := by
    intro m n
    have h1 : ⁅x, y ^ n⁆ = z ^ n := by
      have := Commute.commutatorElement_pow_right (a := x) (b := y) (by rw [hz]; exact hyz) n
      rw [hz] at this
      exact this.symm
    have h2 := Commute.commutatorElement_pow_left (a := x) (b := y ^ n)
      (by rw [h1]; exact hxz.pow_right n) m
    rw [h1, ← pow_mul] at h2
    rw [← h2, mul_comm]
  have hyx : ∀ m n : ℕ, ⁅y ^ m, x ^ n⁆ = (z ^ (m * n))⁻¹ := by
    intro m n
    rw [← commutatorElement_inv, hxy, mul_comm]
  have hzx : ∀ m k : ℕ, Commute (x ^ m) (z ^ k) := fun m k => (hxz.pow_left m).pow_right k
  have hzy : ∀ m k : ℕ, Commute (y ^ m) (z ^ k) := fun m k => (hyz.pow_left m).pow_right k
  have hyy : ⁅y ^ b, y ^ d⁆ = 1 := ((Commute.refl y).pow_pow b d).commutator_eq
  have hxx : ⁅x ^ a, x ^ c⁆ = 1 := ((Commute.refl x).pow_pow a c).commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj, hyy, hxx, hxy, hyx]
  have hzz : (z ^ (b * c))⁻¹ = z ^ (2 * (b * c)) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show b * c + 2 * (b * c) = 3 * (b * c) by ring,
      pow_mul, hz3, one_pow]
  have e0 : (z ^ (b * c))⁻¹ * x ^ c * 1 * (x ^ c)⁻¹ = (z ^ (b * c))⁻¹ := by simp
  have e1 : 1 * x ^ c * z ^ (d * a) * (x ^ c)⁻¹ = z ^ (d * a) := by
    rw [one_mul, (hzx c (d * a)).eq, mul_inv_cancel_right]
  have e2 : x ^ a * (z ^ (b * c))⁻¹ * (x ^ a)⁻¹ = (z ^ (b * c))⁻¹ := by
    rw [((hzx a (b * c)).inv_right).eq, mul_inv_cancel_right]
  rw [e0, e2, e1, hzz, ← pow_add, mul_comm d a, add_comm]

theorem mul_swap_central {a d k : G} (hk : ∀ g, k * g = g * k) : a * d * k = a * k * d := by
  rw [mul_assoc, ← hk d, ← mul_assoc]

theorem comm_mul_commute_right {a b e : G} (h : Commute a e) : ⁅a, b * e⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, h.commutator_eq]
  simp

end Helpers

structure Fi22CoverStruct {L : Type*} [Group L] (p₀ p₁ p₂ q₀ q₁ q₂ c ω n : L) (r : ℕ) : Prop where
  ω3 : ω ^ 3 = 1
  ωc : Commute ω c
  ωp₀ : Commute ω p₀
  ωp₁ : Commute ω p₁
  ωp₂ : Commute ω p₂
  ωq₀ : Commute ω q₀
  ωq₁ : Commute ω q₁
  ωq₂ : Commute ω q₂
  ωn : Commute ω n
  c3 : c ^ 3 = 1
  c_ne : ∀ m : ℕ, c ≠ ω ^ m
  p₀3 : p₀ ^ 3 = 1
  p₁3 : p₁ ^ 3 = 1
  p₂3 : p₂ ^ 3 = 1
  q₀3 : q₀ ^ 3 = 1
  q₁3 : q₁ ^ 3 = 1
  q₂3 : q₂ ^ 3 = 1
  cp₀ : Commute c p₀
  cp₁ : Commute c p₁
  cp₂ : Commute c p₂
  cq₀ : Commute c q₀
  cq₁ : Commute c q₁
  cq₂ : Commute c q₂
  p₀p₁ : Commute p₀ p₁
  p₀p₂ : Commute p₀ p₂
  p₁p₂ : Commute p₁ p₂
  q₀q₁ : Commute q₀ q₁
  q₀q₂ : Commute q₀ q₂
  q₁q₂ : Commute q₁ q₂
  p₀q₁ : Commute p₀ q₁
  p₀q₂ : Commute p₀ q₂
  p₁q₀ : Commute p₁ q₀
  p₁q₂ : Commute p₁ q₂
  p₂q₀ : Commute p₂ q₀
  p₂q₁ : Commute p₂ q₁
  z₀ : ⁅p₀, q₀⁆ = c
  z₁ : ⁅p₁, q₁⁆ = c * ω ^ r
  z₂ : ⁅p₂, q₂⁆ = c * ω ^ (2 * r)
  nc : n * c = c * ω ^ r * n

theorem Fi22CoverStruct.map {L L' : Type*} [Group L] [Group L'] (f : L →* L')
    (hf : Function.Injective f) {p₀ p₁ p₂ q₀ q₁ q₂ c ω n : L} {r : ℕ}
    (h : Fi22CoverStruct p₀ p₁ p₂ q₀ q₁ q₂ c ω n r) :
    Fi22CoverStruct (f p₀) (f p₁) (f p₂) (f q₀) (f q₁) (f q₂) (f c) (f ω) (f n) r := by
  have hpow : ∀ {a : L}, a ^ 3 = 1 → f a ^ 3 = 1 := fun {a} ha => by rw [← map_pow, ha, map_one]
  refine ⟨hpow h.ω3, h.ωc.map f, h.ωp₀.map f, h.ωp₁.map f, h.ωp₂.map f, h.ωq₀.map f,
    h.ωq₁.map f, h.ωq₂.map f, h.ωn.map f, hpow h.c3, ?_, hpow h.p₀3, hpow h.p₁3, hpow h.p₂3, hpow h.q₀3,
    hpow h.q₁3, hpow h.q₂3, h.cp₀.map f, h.cp₁.map f, h.cp₂.map f, h.cq₀.map f, h.cq₁.map f,
    h.cq₂.map f, h.p₀p₁.map f, h.p₀p₂.map f, h.p₁p₂.map f, h.q₀q₁.map f, h.q₀q₂.map f,
    h.q₁q₂.map f, h.p₀q₁.map f, h.p₀q₂.map f, h.p₁q₀.map f, h.p₁q₂.map f, h.p₂q₀.map f,
    h.p₂q₁.map f, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact h.c_ne m (hf (by rw [map_pow]; exact hm))
  · rw [← map_commutatorElement, h.z₀]
  · rw [← map_commutatorElement, h.z₁, map_mul, map_pow]
  · rw [← map_commutatorElement, h.z₂, map_mul, map_pow]
  · have := congrArg f h.nc
    simpa only [map_mul, map_pow] using this

theorem fi22_cover_struct {L S : Type*} [Group L] [Group S] (π : L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L)
    (hcard : Nat.card π.ker = 3) {p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : S}
    (h : Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n) :
    ∃ (P₀ P₁ P₂ Q₀ Q₁ Q₂ c ω N : L) (r : ℕ), ω ∈ π.ker ∧ ω ≠ 1 ∧
      Fi22CoverStruct P₀ P₁ P₂ Q₀ Q₁ Q₂ c ω N r := by
  have hKc : ∀ k ∈ π.ker, ∀ g : L, k * g = g * k := fun k hk g =>
    (Subgroup.mem_center_iff.1 (hker hk) g).symm
  have hK3 : ∀ k ∈ π.ker, k ^ 3 = 1 := by
    intro k hk
    have h1 : (⟨k, hk⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  have hfin : Finite π.ker := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic π.ker := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := π.ker)
  have hgen' : ∀ k ∈ π.ker, ∃ m : ℕ, (g : L) ^ m = k := by
    intro k hk
    have := hg ⟨k, hk⟩
    rw [← mem_powers_iff_mem_zpowers] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, congrArg Subtype.val hm⟩
  have hg1 : (g : L) ≠ 1 := by
    intro h1
    have hsub : Subsingleton π.ker := ⟨fun a b => by
      obtain ⟨m, hm⟩ := hgen' a a.2
      obtain ⟨m', hm'⟩ := hgen' b b.2
      refine Subtype.ext ?_
      rw [← hm, ← hm', h1, one_pow, one_pow]⟩
    have := Nat.card_of_subsingleton (1 : π.ker)
    omega
  obtain ⟨ω, hωK, hω1, hgen⟩ : ∃ ω : L, ω ∈ π.ker ∧ ω ≠ 1 ∧ ∀ k ∈ π.ker, ∃ m : ℕ, ω ^ m = k :=
    ⟨g, g.2, hg1, hgen'⟩
  have liftrel : ∀ {u v : L}, π u = π v → ∃ k ∈ π.ker, u = v * k := fun {u v} huv =>
    ⟨v⁻¹ * u, by rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel], by group⟩
  obtain ⟨P₀, hP₀⟩ := hπ p₀
  obtain ⟨P₁, hP₁⟩ := hπ p₁
  obtain ⟨P₂, hP₂⟩ := hπ p₂
  obtain ⟨Q₀, hQ₀⟩ := hπ q₀
  obtain ⟨Q₁, hQ₁⟩ := hπ q₁
  obtain ⟨Q₂, hQ₂⟩ := hπ q₂
  obtain ⟨DA, hDA⟩ := hπ dA
  obtain ⟨DB, hDB⟩ := hπ dB
  obtain ⟨N, hN⟩ := hπ n
  have hzc : ∀ {p q : S}, p * z = z * p → q * z = z * q → q⁻¹ * p * q = p * z → ⁅p, q⁆ = z :=
    fun {p q} hpz hqz hpq => by
    have h1 : p * q = q * (p * z) := by rw [← hpq]; group
    rw [commutatorElement_def, h1, hpz]
    calc q * (z * p) * p⁻¹ * q⁻¹ = q * z * q⁻¹ := by group
      _ = z := by rw [hqz]; group
  have hp₀3 : p₀ ^ 3 = 1 := h.heis.xp 0
  have hp₁3 : p₁ ^ 3 = 1 := h.heis.xp 1
  have hp₂3 : p₂ ^ 3 = 1 := h.heis.xp 2
  have hzp₀ : p₀ * z = z * p₀ := h.heis.zx 0
  have hzp₁ : p₁ * z = z * p₁ := h.heis.zx 1
  have hzp₂ : p₂ * z = z * p₂ := h.heis.zx 2
  have hzq₀ : q₀ * z = z * q₀ := h.heis.zy 0
  have hzq₁ : q₁ * z = z * q₁ := h.heis.zy 1
  have hzq₂ : q₂ * z = z * q₂ := h.heis.zy 2
  have hz0 : ⁅p₀, q₀⁆ = z := hzc hzp₀ hzq₀ (h.heis.yx 0)
  have hz1 : ⁅p₁, q₁⁆ = z := hzc hzp₁ hzq₁ (h.heis.yx 1)
  have hz2 : ⁅p₂, q₂⁆ = z := hzc hzp₂ hzq₂ (h.heis.yx 2)
  have hxx01 : p₀ * p₁ = p₁ * p₀ := h.heis.xx 0 1
  have hxx02 : p₀ * p₂ = p₂ * p₀ := h.heis.xx 0 2
  have hxx12 : p₁ * p₂ = p₂ * p₁ := h.heis.xx 1 2
  have hyy01 : q₀ * q₁ = q₁ * q₀ := h.heis.yy 0 1 (by decide)
  have hyy02 : q₀ * q₂ = q₂ * q₀ := h.heis.yy 0 2 (by decide)
  have hyy12 : q₁ * q₂ = q₂ * q₁ := h.heis.yy 1 2 (by decide)
  have hxy01 : p₀ * q₁ = q₁ * p₀ := h.heis.xy 0 1 (by decide)
  have hxy02 : p₀ * q₂ = q₂ * p₀ := h.heis.xy 0 2 (by decide)
  have hxy10 : p₁ * q₀ = q₀ * p₁ := h.heis.xy 1 0 (by decide)
  have hxy12 : p₁ * q₂ = q₂ * p₁ := h.heis.xy 1 2 (by decide)
  have hxy20 : p₂ * q₀ = q₀ * p₂ := h.heis.xy 2 0 (by decide)
  have hxy21 : p₂ * q₁ = q₁ * p₂ := h.heis.xy 2 1 (by decide)
  obtain ⟨c, hc_def⟩ : ∃ c : L, c = ⁅P₀, Q₀⁆ := ⟨_, rfl⟩
  have hπc : π c = z := by rw [hc_def, map_commutatorElement, hP₀, hQ₀]; exact hz0
  have hcommK : ∀ {A B : L} {a b : S}, π A = a → π B = b → a * b = b * a → ⁅A, B⁆ ∈ π.ker := by
    intro A B a b hA hB hab
    rw [MonoidHom.mem_ker, map_commutatorElement, hA, hB]
    exact commutatorElement_eq_one_iff_mul_comm.2 hab
  have hcen : ∀ {A B : L} {a b : S}, π A = a → π B = b → a * b = b * a →
      ∀ g, ⁅A, B⁆ * g = g * ⁅A, B⁆ := fun hA hB hab g => hKc _ (hcommK hA hB hab) g
  have hpowK : ∀ {A : L} {a : S}, π A = a → a ^ 3 = 1 → ∀ g, A ^ 3 * g = g * A ^ 3 := by
    intro A a hA ha g
    refine hKc _ ?_ g
    rw [MonoidHom.mem_ker, map_pow, hA, ha]
  have hπq₀3 : q₀ ^ 3 = 1 := h.hq₀
  have hπq₁3 : q₁ ^ 3 = 1 := h.hq₁
  have hπq₂3 : q₂ ^ 3 = 1 := h.hq₂
  have hcP₀ : ⁅c, P₀⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DB * c) (v := c * DB)
      (by simp only [map_mul, hDB, hπc]; exact h.dBz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₀) (v := P₀ * (P₀ * DB)) (by simp only [map_mul, hDB, hP₀]; exact h.dBp₀)
    exact comm_eq_one_of_sign (c := c) (b := P₀) (d := DB) (e := 1)
      (hKc _ (hcommK hπc hP₀ hzp₀.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right c).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (by rw [one_mul]; exact hke)
  have hcP₁ : ⁅c, P₁⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DB * c) (v := c * DB)
      (by simp only [map_mul, hDB, hπc]; exact h.dBz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₁) (v := P₁ * (P₁ * DB)) (by simp only [map_mul, hDB, hP₁]; exact h.dBp₁)
    exact comm_eq_one_of_sign (c := c) (b := P₁) (d := DB) (e := 1)
      (hKc _ (hcommK hπc hP₁ hzp₁.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right c).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (by rw [one_mul]; exact hke)
  have hcP₂ : ⁅c, P₂⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DA * c) (v := c * DA)
      (by simp only [map_mul, hDA, hπc]; exact h.dAz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * P₂) (v := P₂ * (P₂ * DA)) (by simp only [map_mul, hDA, hP₂]; exact h.dAp₂)
    exact comm_eq_one_of_sign (c := c) (b := P₂) (d := DA) (e := 1)
      (hKc _ (hcommK hπc hP₂ hzp₂.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right c).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (by rw [one_mul]; exact hke)
  have hcQ₀ : ⁅c, Q₀⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DB * c) (v := c * DB)
      (by simp only [map_mul, hDB, hπc]; exact h.dBz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₀) (v := Q₀ * (Q₀ * DB)) (by simp only [map_mul, hDB, hQ₀]; exact h.dBq₀)
    exact comm_eq_one_of_sign (c := c) (b := Q₀) (d := DB) (e := 1)
      (hKc _ (hcommK hπc hQ₀ hzq₀.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right c).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (by rw [one_mul]; exact hke)
  have hcQ₁ : ⁅c, Q₁⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DB * c) (v := c * DB)
      (by simp only [map_mul, hDB, hπc]; exact h.dBz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₁) (v := Q₁ * (Q₁ * (c * DB))) (by simp only [map_mul, hDB, hQ₁, hπc]; exact h.dBq₁)
    exact comm_eq_one_of_sign (c := c) (b := Q₁) (d := DB) (e := c)
      (hKc _ (hcommK hπc hQ₁ hzq₁.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.refl c).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (hke)
  have hcQ₂ : ⁅c, Q₂⁆ = 1 := by
    obtain ⟨k₂, hk₂, hk₂e⟩ := liftrel (u := DA * c) (v := c * DA)
      (by simp only [map_mul, hDA, hπc]; exact h.dAz)
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * Q₂) (v := Q₂ * (Q₂ * (c * (c * DA)))) (by simp only [map_mul, hDA, hQ₂, hπc]; exact h.dAq₂)
    exact comm_eq_one_of_sign (c := c) (b := Q₂) (d := DA) (e := (c * c))
      (hKc _ (hcommK hπc hQ₂ hzq₂.symm)) (hKc k₁ hk₁) (hKc k₂ hk₂) (((Commute.refl c).mul_right (Commute.refl c)).eq)
      (by rw [hk₂e]; exact mul_swap_central (hKc k₂ hk₂)) (by rw [mul_assoc c c DA]; exact hke)
  have hCP₀ : Commute c P₀ := commutatorElement_eq_one_iff_commute.1 hcP₀
  have hCP₁ : Commute c P₁ := commutatorElement_eq_one_iff_commute.1 hcP₁
  have hCP₂ : Commute c P₂ := commutatorElement_eq_one_iff_commute.1 hcP₂
  have hCQ₀ : Commute c Q₀ := commutatorElement_eq_one_iff_commute.1 hcQ₀
  have hCQ₁ : Commute c Q₁ := commutatorElement_eq_one_iff_commute.1 hcQ₁
  have hCQ₂ : Commute c Q₂ := commutatorElement_eq_one_iff_commute.1 hcQ₂
  have hc3 : c ^ 3 = 1 := by
    have hc' : Commute P₀ ⁅P₀, Q₀⁆ := by rw [← hc_def]; exact hCP₀.symm
    have h1 := Commute.commutatorElement_pow_left hc' 3
    have h2 : ⁅P₀ ^ 3, Q₀⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hpowK hP₀ hp₀3 Q₀)
    rw [← hc_def, h2] at h1
    exact h1
  have hce3 : ∀ {e : L}, (e = 1 ∨ e = c ∨ e = c * c) → e ^ 3 = 1 := by
    rintro e (rfl | rfl | rfl)
    · simp
    · exact hc3
    · rw [(Commute.refl c).mul_pow, hc3, one_mul]
  have hP₀3 : P₀ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₀) (v := P₀ * (P₀ * DB)) (by simp only [map_mul, hDB, hP₀]; exact h.dBp₀)
    exact pow_three_eq_one_of_sign (b := P₀) (d := DB) (e := 1) (k := k₁) (hpowK hP₀ hp₀3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inl rfl))
      ((Commute.one_right P₀).eq) (by rw [one_mul]; exact hke)
  have hP₁3 : P₁ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₁) (v := P₁ * (P₁ * DB)) (by simp only [map_mul, hDB, hP₁]; exact h.dBp₁)
    exact pow_three_eq_one_of_sign (b := P₁) (d := DB) (e := 1) (k := k₁) (hpowK hP₁ hp₁3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inl rfl))
      ((Commute.one_right P₁).eq) (by rw [one_mul]; exact hke)
  have hP₂3 : P₂ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * P₂) (v := P₂ * (P₂ * DA)) (by simp only [map_mul, hDA, hP₂]; exact h.dAp₂)
    exact pow_three_eq_one_of_sign (b := P₂) (d := DA) (e := 1) (k := k₁) (hpowK hP₂ hp₂3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inl rfl))
      ((Commute.one_right P₂).eq) (by rw [one_mul]; exact hke)
  have hQ₀3 : Q₀ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₀) (v := Q₀ * (Q₀ * DB)) (by simp only [map_mul, hDB, hQ₀]; exact h.dBq₀)
    exact pow_three_eq_one_of_sign (b := Q₀) (d := DB) (e := 1) (k := k₁) (hpowK hQ₀ hπq₀3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inl rfl))
      ((Commute.one_right Q₀).eq) (by rw [one_mul]; exact hke)
  have hQ₁3 : Q₁ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₁) (v := Q₁ * (Q₁ * (c * DB))) (by simp only [map_mul, hDB, hQ₁, hπc]; exact h.dBq₁)
    exact pow_three_eq_one_of_sign (b := Q₁) (d := DB) (e := c) (k := k₁) (hpowK hQ₁ hπq₁3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inr (Or.inl rfl)))
      ((hCQ₁.symm).eq) (hke)
  have hQ₂3 : Q₂ ^ 3 = 1 := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * Q₂) (v := Q₂ * (Q₂ * (c * (c * DA)))) (by simp only [map_mul, hDA, hQ₂, hπc]; exact h.dAq₂)
    exact pow_three_eq_one_of_sign (b := Q₂) (d := DA) (e := (c * c)) (k := k₁) (hpowK hQ₂ hπq₂3)
      (hKc k₁ hk₁) (hK3 k₁ hk₁) (hce3 (Or.inr (Or.inr rfl)))
      (((hCQ₂.symm).mul_right (hCQ₂.symm)).eq) (by rw [mul_assoc c c DA]; exact hke)
  have hXP₀P₁ : Commute P₀ P₁ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * P₀) (v := P₀ * (P₀ * DA)) (by simp only [map_mul, hDA, hP₀]; exact h.dAp₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DA * P₁) (v := P₁ * DA) (by simp only [map_mul, hDA, hP₁]; exact h.dAp₁)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₀) (b := P₁) (d := DA) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₀ hP₁ hxx01) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right P₁)) (Commute.one_right P₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXP₀Q₁ : Commute P₀ Q₁ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * P₀) (v := P₀ * (P₀ * DA)) (by simp only [map_mul, hDA, hP₀]; exact h.dAp₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DA * Q₁) (v := Q₁ * DA) (by simp only [map_mul, hDA, hQ₁]; exact h.dAq₁)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₀) (b := Q₁) (d := DA) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₀ hQ₁ hxy01) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right Q₁)) (Commute.one_right P₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXQ₀P₁ : Commute Q₀ P₁ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * Q₀) (v := Q₀ * (Q₀ * (c * (c * DA)))) (by simp only [map_mul, hDA, hQ₀, hπc]; exact h.dAq₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DA * P₁) (v := P₁ * DA) (by simp only [map_mul, hDA, hP₁]; exact h.dAp₁)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₀) (b := P₁) (d := DA) (e := (c * c)) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₀ hP₁ hxy10.symm) (hKc k₁ hk₁) (hKc k₂ hk₂) (((hCP₁.symm).mul_right (hCP₁.symm))) (Commute.one_right Q₀) (Commute.one_right _)
      (by rw [mul_assoc c c DA]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXQ₀Q₁ : Commute Q₀ Q₁ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DA * Q₀) (v := Q₀ * (Q₀ * (c * (c * DA)))) (by simp only [map_mul, hDA, hQ₀, hπc]; exact h.dAq₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DA * Q₁) (v := Q₁ * DA) (by simp only [map_mul, hDA, hQ₁]; exact h.dAq₁)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₀) (b := Q₁) (d := DA) (e := (c * c)) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₀ hQ₁ hyy01) (hKc k₁ hk₁) (hKc k₂ hk₂) (((hCQ₁.symm).mul_right (hCQ₁.symm))) (Commute.one_right Q₀) (Commute.one_right _)
      (by rw [mul_assoc c c DA]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXP₀P₂ : Commute P₀ P₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₀) (v := P₀ * (P₀ * DB)) (by simp only [map_mul, hDB, hP₀]; exact h.dBp₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * P₂) (v := P₂ * DB) (by simp only [map_mul, hDB, hP₂]; exact h.dBp₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₀) (b := P₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₀ hP₂ hxx02) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right P₂)) (Commute.one_right P₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXP₀Q₂ : Commute P₀ Q₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₀) (v := P₀ * (P₀ * DB)) (by simp only [map_mul, hDB, hP₀]; exact h.dBp₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * Q₂) (v := Q₂ * DB) (by simp only [map_mul, hDB, hQ₂]; exact h.dBq₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₀) (b := Q₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₀ hQ₂ hxy02) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right Q₂)) (Commute.one_right P₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXQ₀P₂ : Commute Q₀ P₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₀) (v := Q₀ * (Q₀ * DB)) (by simp only [map_mul, hDB, hQ₀]; exact h.dBq₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * P₂) (v := P₂ * DB) (by simp only [map_mul, hDB, hP₂]; exact h.dBp₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₀) (b := P₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₀ hP₂ hxy20.symm) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right P₂)) (Commute.one_right Q₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXQ₀Q₂ : Commute Q₀ Q₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₀) (v := Q₀ * (Q₀ * DB)) (by simp only [map_mul, hDB, hQ₀]; exact h.dBq₀)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * Q₂) (v := Q₂ * DB) (by simp only [map_mul, hDB, hQ₂]; exact h.dBq₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₀) (b := Q₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₀ hQ₂ hyy02) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right Q₂)) (Commute.one_right Q₀) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXP₁P₂ : Commute P₁ P₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₁) (v := P₁ * (P₁ * DB)) (by simp only [map_mul, hDB, hP₁]; exact h.dBp₁)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * P₂) (v := P₂ * DB) (by simp only [map_mul, hDB, hP₂]; exact h.dBp₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₁) (b := P₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₁ hP₂ hxx12) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right P₂)) (Commute.one_right P₁) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXP₁Q₂ : Commute P₁ Q₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * P₁) (v := P₁ * (P₁ * DB)) (by simp only [map_mul, hDB, hP₁]; exact h.dBp₁)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * Q₂) (v := Q₂ * DB) (by simp only [map_mul, hDB, hQ₂]; exact h.dBq₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := P₁) (b := Q₂) (d := DB) (e := 1) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hP₁ hQ₂ hxy12) (hKc k₁ hk₁) (hKc k₂ hk₂) ((Commute.one_right Q₂)) (Commute.one_right P₁) (Commute.one_right _)
      (by rw [one_mul]; exact hke) (by rw [one_mul]; exact hke₂))
  have hXQ₁P₂ : Commute Q₁ P₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₁) (v := Q₁ * (Q₁ * (c * DB))) (by simp only [map_mul, hDB, hQ₁, hπc]; exact h.dBq₁)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * P₂) (v := P₂ * DB) (by simp only [map_mul, hDB, hP₂]; exact h.dBp₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₁) (b := P₂) (d := DB) (e := c) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₁ hP₂ hxy21.symm) (hKc k₁ hk₁) (hKc k₂ hk₂) ((hCP₂.symm)) (Commute.one_right Q₁) (Commute.one_right _)
      (hke) (by rw [one_mul]; exact hke₂))
  have hXQ₁Q₂ : Commute Q₁ Q₂ := by
    obtain ⟨k₁, hk₁, hke⟩ := liftrel (u := DB * Q₁) (v := Q₁ * (Q₁ * (c * DB))) (by simp only [map_mul, hDB, hQ₁, hπc]; exact h.dBq₁)
    obtain ⟨k₂, hk₂, hke₂⟩ := liftrel (u := DB * Q₂) (v := Q₂ * DB) (by simp only [map_mul, hDB, hQ₂]; exact h.dBq₂)
    refine commutatorElement_eq_one_iff_commute.1 (comm_eq_one_of_cross (a := Q₁) (b := Q₂) (d := DB) (e := c) (e' := 1) (k := k₁) (k' := k₂)
      (hcen hQ₁ hQ₂ hyy12) (hKc k₁ hk₁) (hKc k₂ hk₂) ((hCQ₂.symm)) (Commute.one_right Q₁) (Commute.one_right _)
      (hke) (by rw [one_mul]; exact hke₂))
  obtain ⟨k₀, hk₀K, hk₀⟩ := liftrel (u := N * c) (v := c * N)
    (by simp only [map_mul, hN, hπc]; exact h.nz)
  obtain ⟨r, hr⟩ := hgen k₀ hk₀K
  have hnc : N * c = c * ω ^ r * N := by
    rw [hr, hk₀]
    exact mul_swap_central (hKc k₀ hk₀K)
  have hωr : ∀ g : L, ω ^ r * g = g * ω ^ r := fun g => hKc _ (Subgroup.pow_mem _ hωK r) g
  have hNc : N * c * N⁻¹ = c * ω ^ r := by rw [hnc, mul_inv_cancel_right]
  have hπz1 : π ⁅P₁, Q₁⁆ = z := by rw [map_commutatorElement, hP₁, hQ₁]; exact hz1
  have hπz2 : π ⁅P₂, Q₂⁆ = z := by rw [map_commutatorElement, hP₂, hQ₂]; exact hz2
  obtain ⟨k₃, hk₃K, hk₃⟩ := liftrel (u := ⁅P₁, Q₁⁆) (v := c) (by rw [hπz1, hπc])
  obtain ⟨k₄, hk₄K, hk₄⟩ := liftrel (u := ⁅P₂, Q₂⁆) (v := c) (by rw [hπz2, hπc])
  have hz1P : Commute P₁ ⁅P₁, Q₁⁆ := by
    rw [hk₃]; exact hCP₁.symm.mul_right (hKc k₃ hk₃K P₁).symm
  have hz1Q : Commute Q₁ ⁅P₁, Q₁⁆ := by
    rw [hk₃]; exact hCQ₁.symm.mul_right (hKc k₃ hk₃K Q₁).symm
  have hz2P : Commute P₂ ⁅P₂, Q₂⁆ := by
    rw [hk₄]; exact hCP₂.symm.mul_right (hKc k₄ hk₄K P₂).symm
  have hz2Q : Commute Q₂ ⁅P₂, Q₂⁆ := by
    rw [hk₄]; exact hCQ₂.symm.mul_right (hKc k₄ hk₄K Q₂).symm
  have hz13 : ⁅P₁, Q₁⁆ ^ 3 = 1 := by
    rw [hk₃, Commute.mul_pow (hKc k₃ hk₃K c).symm, hc3, hK3 k₃ hk₃K, one_mul]
  have hz23 : ⁅P₂, Q₂⁆ ^ 3 = 1 := by
    rw [hk₄, Commute.mul_pow (hKc k₄ hk₄K c).symm, hc3, hK3 k₄ hk₄K, one_mul]
  have hfour : ∀ {w : L}, w ^ 3 = 1 → w ^ 4 = w := fun {w} hw => by
    rw [show 4 = 3 + 1 by norm_num, pow_add, hw, one_mul, pow_one]
  obtain ⟨ka, hkaK, hka⟩ := liftrel (u := N * P₀) (v := P₁ * (P₁ * N))
    (by simp only [map_mul, hN, hP₀, hP₁]; exact h.np₀)
  obtain ⟨kb, hkbK, hkb⟩ := liftrel (u := N * Q₀) (v := P₁ * (Q₁ * (Q₁ * (c * (c * N)))))
    (by simp only [map_mul, hN, hQ₀, hP₁, hQ₁, hπc]; exact h.nq₀)
  have e1 : N * P₀ * N⁻¹ = P₁ ^ 2 * Q₁ ^ 0 * ka := by
    rw [mul_inv_eq_iff_eq_mul, hka]
    simp only [pow_two, pow_zero, mul_one, mul_assoc]
    rw [hKc ka hkaK N]
  have e2 : N * Q₀ * N⁻¹ = P₁ ^ 1 * Q₁ ^ 2 * (c * c * kb) := by
    rw [mul_inv_eq_iff_eq_mul, hkb]
    simp only [pow_one, pow_two, mul_assoc]
    rw [hKc kb hkbK N]
  have hAE : Commute (P₁ ^ 2 * Q₁ ^ 0) (c * c * kb) := by
    rw [pow_zero, mul_one]
    exact ((hCP₁.symm.pow_left 2).mul_right (hCP₁.symm.pow_left 2)).mul_right
      (hKc kb hkbK (P₁ ^ 2)).symm
  have hcomm1 : ⁅P₁ ^ 2 * Q₁ ^ 0, P₁ ^ 1 * Q₁ ^ 2⁆ = ⁅P₁, Q₁⁆ ^ 4 := by
    have := comm_two_letter (x := P₁) (y := Q₁) (z := ⁅P₁, Q₁⁆) rfl hz1P hz1Q hz13 2 0 1 2
    norm_num at this ⊢
    exact this
  have key1 := conjugate_commutatorElement P₀ Q₀ N
  rw [← hc_def, hNc, e1, e2, comm_mul_central_left (hKc ka hkaK), comm_mul_commute_right hAE,
    hcomm1, hfour hz13] at key1
  have hz1eq : ⁅P₁, Q₁⁆ = c * ω ^ r := key1.symm
  obtain ⟨kc, hkcK, hkc⟩ := liftrel (u := N * P₁) (v := Q₂ * N)
    (by simp only [map_mul, hN, hP₁, hQ₂]; exact h.np₁)
  obtain ⟨kd, hkdK, hkd⟩ := liftrel (u := N * Q₁) (v := P₂ * (P₂ * N))
    (by simp only [map_mul, hN, hQ₁, hP₂]; exact h.nq₁)
  have e3 : N * P₁ * N⁻¹ = P₂ ^ 0 * Q₂ ^ 1 * kc := by
    rw [mul_inv_eq_iff_eq_mul, hkc]
    simp only [pow_zero, pow_one, one_mul, mul_assoc]
    rw [hKc kc hkcK N]
  have e4 : N * Q₁ * N⁻¹ = P₂ ^ 2 * Q₂ ^ 0 * kd := by
    rw [mul_inv_eq_iff_eq_mul, hkd]
    simp only [pow_two, pow_zero, mul_one, mul_assoc]
    rw [hKc kd hkdK N]
  have hcomm2 : ⁅P₂ ^ 0 * Q₂ ^ 1, P₂ ^ 2 * Q₂ ^ 0⁆ = ⁅P₂, Q₂⁆ ^ 4 := by
    have := comm_two_letter (x := P₂) (y := Q₂) (z := ⁅P₂, Q₂⁆) rfl hz2P hz2Q hz23 0 1 2 0
    norm_num at this ⊢
    exact this
  have key2 := conjugate_commutatorElement P₁ Q₁ N
  have hNz1 : N * ⁅P₁, Q₁⁆ * N⁻¹ = c * ω ^ r * ω ^ r := by
    rw [hz1eq, show N * (c * ω ^ r) * N⁻¹ = (N * c * N⁻¹) * (N * ω ^ r * N⁻¹) by group, hNc,
      ← hωr N, mul_inv_cancel_right]
  rw [e3, e4, comm_mul_central_left (hKc kc hkcK) ,
    comm_mul_central_right (hKc kd hkdK), hcomm2, hfour hz23, hNz1] at key2
  have hz2eq : ⁅P₂, Q₂⁆ = c * ω ^ (2 * r) := by
    rw [← key2, mul_assoc, ← pow_add, two_mul]
  refine ⟨P₀, P₁, P₂, Q₀, Q₁, Q₂, c, ω, N, r, hωK, hω1, ?_⟩
  exact
    { ω3 := hK3 ω hωK
      ωc := hKc ω hωK c
      ωp₀ := hKc ω hωK P₀
      ωp₁ := hKc ω hωK P₁
      ωp₂ := hKc ω hωK P₂
      ωq₀ := hKc ω hωK Q₀
      ωq₁ := hKc ω hωK Q₁
      ωq₂ := hKc ω hωK Q₂
      ωn := hKc ω hωK N
      c3 := hc3
      c_ne := fun m hm => by
        have h1 : π c = 1 := by
          rw [hm, map_pow, show π ω = 1 from hωK, one_pow]
        exact h.heis.z1 (hπc ▸ h1)
      p₀3 := hP₀3
      p₁3 := hP₁3
      p₂3 := hP₂3
      q₀3 := hQ₀3
      q₁3 := hQ₁3
      q₂3 := hQ₂3
      cp₀ := hCP₀
      cp₁ := hCP₁
      cp₂ := hCP₂
      cq₀ := hCQ₀
      cq₁ := hCQ₁
      cq₂ := hCQ₂
      p₀p₁ := hXP₀P₁
      p₀p₂ := hXP₀P₂
      p₁p₂ := hXP₁P₂
      q₀q₁ := hXQ₀Q₁
      q₀q₂ := hXQ₀Q₂
      q₁q₂ := hXQ₁Q₂
      p₀q₁ := hXP₀Q₁
      p₀q₂ := hXP₀Q₂
      p₁q₀ := hXQ₀P₁.symm
      p₁q₂ := hXP₁Q₂
      p₂q₀ := hXQ₀P₂.symm
      p₂q₁ := hXQ₁P₂.symm
      z₀ := hc_def.symm
      z₁ := hz1eq
      z₂ := hz2eq
      nc := hnc }

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
