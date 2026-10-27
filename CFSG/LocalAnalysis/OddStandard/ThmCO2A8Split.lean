module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section AZ

open Equiv

def az_s : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.2 (by decide)⟩

def az_t : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 3 4, Perm.mem_alternatingGroup.2 (by decide)⟩

theorem az_s_pow : az_s ^ 3 = 1 := by decide

theorem az_s_ne : az_s ≠ 1 := by decide

theorem az_s_sq_ne : az_s ^ 2 ≠ 1 := by decide

theorem az_t_conj : az_t * az_s * az_t⁻¹ * az_s = 1 := by decide

theorem az_card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem az_card {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (h3 : Nat.card f.ker = 3) : Nat.card K = 180 := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hf, Subgroup.card_top, h3, az_card_A5] at h
  omega

theorem az_comm_ker {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (h3 : Nat.card f.ker = 3) {a b : K} (ha : a ∈ f.ker) (hb : b ∈ f.ker) : a * b = b * a := by
  have : IsCyclic f.ker := isCyclic_of_prime_card h3
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : f.ker) ⟨b, hb⟩)

theorem az_pow_three {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (h3 : Nat.card f.ker = 3) {m : K} (hm : m ∈ f.ker) : m ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := f.ker) (x := ⟨m, hm⟩)
  rw [h3] at h
  exact congrArg Subtype.val h

theorem az_central {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (h3 : Nat.card f.ker = 3) {m : K} (hm : m ∈ f.ker) (k : K) :
    k * m = m * k := by
  have : IsCyclic f.ker := isCyclic_of_prime_card h3
  have : Finite f.ker := Nat.finite_of_card_ne_zero (by omega)
  have hA : Nat.card (MulAut f.ker) = 2 := by
    rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]
  have : Finite (MulAut f.ker) := Nat.finite_of_card_ne_zero (by omega)
  let φ : K →* MulAut f.ker := MulAut.conjNormal
  have hcomm : ∀ x ∈ φ.ker, ∀ y ∈ f.ker, x * y * x⁻¹ = y := by
    intro x hx y hy
    have := congrArg Subtype.val (DFunLike.congr_fun ((MonoidHom.mem_ker).1 hx) ⟨y, hy⟩)
    simpa [φ, MulAut.conjNormal_apply] using this
  have hsq : ∀ x : K, x ^ 2 ∈ φ.ker := fun x => by
    rw [MonoidHom.mem_ker, map_pow, ← hA]
    exact pow_card_eq_one'
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have htop : φ.ker.map f = ⊤ := by
    have : (φ.ker.map f).Normal := φ.normal_ker.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map f) with h | h
    · exfalso
      obtain ⟨c, hc⟩ := hf az_s
      have hc2 : f (c ^ 2) ∈ φ.ker.map f := Subgroup.mem_map_of_mem f (hsq c)
      rw [h, Subgroup.mem_bot, map_pow, hc] at hc2
      exact az_s_sq_ne hc2
    · exact h
  have hk : f k ∈ φ.ker.map f := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.1 hk
  have hn : x⁻¹ * k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfx, inv_mul_cancel]
  have h1 : (x⁻¹ * k) * m = m * (x⁻¹ * k) := az_comm_ker f h3 hn hm
  have h2 : x * m * x⁻¹ = m := hcomm x hx m hm
  calc k * m = x * ((x⁻¹ * k) * m) := by group
    _ = x * (m * (x⁻¹ * k)) := by rw [h1]
    _ = (x * m * x⁻¹) * k := by group
    _ = m * k := by rw [h2]

theorem az_cube {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (h3 : Nat.card f.ker = 3) {c : K} (hc : f c = az_s) :
    c ^ 3 = 1 := by
  obtain ⟨t, ht⟩ := hf az_t
  have hc3 : c ^ 3 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hc, az_s_pow]
  have hw : t * c * t⁻¹ * c ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, ht, hc, az_t_conj]
  have hwc : Commute (t * c * t⁻¹ * c) c⁻¹ := (az_central f hf h3 hw c⁻¹).symm
  have key : c ^ 3 = (c ^ 3)⁻¹ := by
    calc c ^ 3 = t * c ^ 3 * t⁻¹ := by
          rw [az_central f hf h3 hc3 t, mul_assoc, mul_inv_cancel, mul_one]
      _ = (t * c * t⁻¹) ^ 3 := conj_pow.symm
      _ = ((t * c * t⁻¹ * c) * c⁻¹) ^ 3 := by group
      _ = (t * c * t⁻¹ * c) ^ 3 * c⁻¹ ^ 3 := hwc.mul_pow 3
      _ = (c ^ 3)⁻¹ := by rw [az_pow_three f h3 hw, one_mul, inv_pow]
  have hsq : c ^ 3 * c ^ 3 = 1 := by
    nth_rewrite 2 [key]
    exact mul_inv_cancel _
  calc c ^ 3 = c ^ 3 * (c ^ 3 * c ^ 3) := by rw [hsq, mul_one]
    _ = (c ^ 3) ^ 3 := (pow_three _).symm
    _ = 1 := az_pow_three f h3 hc3

theorem az_inf {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5)) {c : K}
    (hc : f c = az_s) (hc3 : c ^ 3 = 1) {x : K} (hx : x ∈ Subgroup.zpowers c)
    (hxk : x ∈ f.ker) : x = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [MonoidHom.mem_ker, map_zpow, hc] at hxk
  have h3 : ((3 : ℕ) : ℤ) ∣ i := by
    rw [← orderOf_eq_prime az_s_pow az_s_ne]
    exact orderOf_dvd_iff_zpow_eq_one.2 hxk
  apply orderOf_dvd_iff_zpow_eq_one.1
  exact (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hc3)).trans h3

theorem az_index {K : Type} [Group K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) : ((Subgroup.zpowers az_s).comap f).index = 20 := by
  rw [Subgroup.index_comap_of_surjective _ hf]
  have h := (Subgroup.zpowers az_s).index_mul_card
  rw [Nat.card_zpowers, orderOf_eq_prime az_s_pow az_s_ne, az_card_A5] at h
  omega

theorem az_chi {K : Type} [Group K] [Finite K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (h3 : Nat.card f.ker = 3) :
    ∃ χ : K →* Multiplicative (ZMod 3), ∀ m ∈ f.ker, m ≠ 1 → χ m ≠ 1 := by
  obtain ⟨c, hc⟩ := hf az_s
  have hc3 : c ^ 3 = 1 := az_cube f hf h3 hc
  have hc1 : c ≠ 1 := fun h => az_s_ne (by rw [← hc, h, map_one])
  set P : Subgroup K := (Subgroup.zpowers az_s).comap f with hP
  have hPi : P.index = 20 := az_index f hf
  have hPc : Nat.card P = 3 ^ 2 := by
    have h := P.card_mul_index
    rw [hPi, az_card f hf h3] at h
    omega
  have hcP : c ∈ P := by
    rw [hP, Subgroup.mem_comap, hc]
    exact Subgroup.mem_zpowers _
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPc
  set Q : Subgroup P := Subgroup.zpowers ⟨c, hcP⟩ with hQ
  have hQc : Nat.card Q = 3 := by
    rw [hQ, Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_eq_prime hc3 hc1]
  have hQi : Nat.card (P ⧸ Q) = 3 := by
    have h := Q.index_mul_card
    rw [hQc, hPc] at h
    change Q.index = 3
    omega
  let e : P ⧸ Q ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hQi (by simp)
  let ϕ : P →* Multiplicative (ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have key : ∀ m ∈ f.ker, ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * m ^ k * g₀ ∈ P →
      g₀⁻¹ * m ^ k * g₀ = m ^ k := fun m hm k g₀ _ => by
    rw [az_central f hf h3 (pow_mem hm k) g₀⁻¹, inv_mul_cancel_right]
  refine ⟨ϕ.transfer, fun m hm hm1 h => ?_⟩
  have ht : ϕ.transfer m = ϕ ⟨m ^ P.index, MonoidHom.transfer_eq_pow_aux m (key m hm)⟩ :=
    MonoidHom.transfer_eq_pow ϕ m (key m hm)
  have h' : ϕ ⟨m ^ P.index, MonoidHom.transfer_eq_pow_aux m (key m hm)⟩ = 1 := ht.symm.trans h
  have hmem : (⟨m ^ P.index, MonoidHom.transfer_eq_pow_aux m (key m hm)⟩ : P) ∈ Q := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [ϕ] using h'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hx : m ^ P.index = 1 := by
    refine az_inf f hc hc3 (Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩) (pow_mem hm _)
    exact congrArg Subtype.val hi
  rw [hPi] at hx
  have h20 := orderOf_dvd_of_pow_eq_one hx
  have h3' := orderOf_dvd_of_pow_eq_one (az_pow_three f h3 hm)
  have h1 : orderOf m = 1 := Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h20 h3')
  exact hm1 (orderOf_eq_one_iff.1 h1)

theorem az_z3 {K : Type} [Group K] [Finite K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (h3 : Nat.card f.ker = 3) :
    Nonempty (K ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  obtain ⟨χ, hχ⟩ := az_chi f hf h3
  have hinj : Function.Injective (χ.prod f) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hk
    by_contra hk1
    exact hχ k hk.2 hk1 hk.1
  have hcard : Nat.card (Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) ≤ Nat.card K := by
    rw [Nat.card_prod, az_card f hf h3, az_card_A5]
    simp
  exact ⟨MulEquiv.ofBijective _ (hinj.bijective_of_nat_card_le hcard)⟩

end AZ

theorem a5_or_z3a5 {K : Type} [Group K] [Finite K] (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (hker : Nat.card f.ker ∣ 3) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (K ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hker with h1 | h3
  · exact Or.inl ⟨MulEquiv.ofBijective f
      ⟨(MonoidHom.ker_eq_bot_iff f).1 (Subgroup.eq_bot_of_card_eq _ h1), hf⟩⟩
  · exact Or.inr (az_z3 f hf h3)

end CFSG.OddStandard.ThmC.O2.A8
