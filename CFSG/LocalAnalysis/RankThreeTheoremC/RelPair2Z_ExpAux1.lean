module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {D : Subgroup X}

theorem zje_transvection_form (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {z n : X}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hn : ∃ k : ℕ, n ^ (p ^ k) = 1)
    (hnD : n ∈ normalizer (D : Set X)) (hnz : n * z = z * n)
    (hnC : n ∉ centralizer (D : Set X)) {d : X} (hd : d ∈ D) (hdz : d ∉ zpowers z) :
    ∃ b : ℕ, (b : ZMod p) ≠ 0 ∧ n * d * n⁻¹ = d * z ^ b := by
  have hzp : z ^ p = 1 := hD.2 z hzD
  have hdp : d ^ p = 1 := hD.2 d hd
  have hcd : d * z = z * d := congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩)
  have hz : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
  have hgen : ∀ {x : X}, x ∈ D → ∃ s t : ℕ, x = d ^ s * z ^ t := fun {x} hx =>
    exists_pow_mul_pow_of_mem_plane hD hDc hzD hz1 hd hdz hx
  obtain ⟨a, b, hab⟩ := hgen ((mem_normalizer_iff.1 hnD d).1 hd)
  obtain ⟨k, hk⟩ := hn
  have ha : (a : ZMod p) = 1 := by
    obtain ⟨β, hβ⟩ := exists_conj_pow_eq_pow_mul_pow hcd hnz hab (p ^ k)
    rw [hk, inv_one, mul_one, one_mul] at hβ
    have h1 := natCast_eq_one_of_eq_pow_mul_pow hdp hdz hβ
    rwa [Nat.cast_pow, ZMod.pow_card_pow] at h1
  have hb' := conj_eq_mul_pow_of_natCast_eq_one hdp hab ha
  refine ⟨b, fun hb0 => hnC ?_, hb'⟩
  have hzb : z ^ b = z ^ 0 :=
    pow_eq_pow_of_natCast_eq_of_pow_eq_one hzp (by rw [hb0, Nat.cast_zero])
  have hnd : n * d * n⁻¹ = d := by rw [hb', hzb, pow_zero, mul_one]
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨s, t, rfl⟩ := hgen hx
  have h1 : n * (d ^ s * z ^ t) * n⁻¹ = d ^ s * z ^ t := by
    calc n * (d ^ s * z ^ t) * n⁻¹ = (n * d * n⁻¹) ^ s * (n * z * n⁻¹) ^ t := by
          rw [conj_pow, conj_pow]; group
      _ = d ^ s * z ^ t := by rw [hnd, hz]
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem zje_mem_zpowers_symm {z z₂ : X} (hz1 : z ≠ 1) (hz₂1 : z₂ ≠ 1) (hzp : z ^ p = 1)
    (hz₂p : z₂ ^ p = 1) (h : z ∈ zpowers z₂) : z₂ ∈ zpowers z := by
  have heq : zpowers z = zpowers z₂ := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1,
      orderOf_eq_prime hz₂p hz₂1])
  exact heq ▸ mem_zpowers z₂

theorem zje_exists_inv (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {z n g₁ : X}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hn : ∃ k : ℕ, n ^ (p ^ k) = 1)
    (hnD : n ∈ normalizer (D : Set X)) (hnz : n * z = z * n)
    (hnC : n ∉ centralizer (D : Set X)) (hg₁ : g₁ ∈ normalizer (D : Set X))
    (hg₁z : g₁ * z * g₁⁻¹ ∉ zpowers z) :
    ∃ g ∈ normalizer (D : Set X), ∀ d ∈ D, g * d * g⁻¹ = d⁻¹ := by
  have hzp : z ^ p = 1 := hD.2 z hzD
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set z₂ : X := g₁ * z * g₁⁻¹ with hz₂
  have hz₂D : z₂ ∈ D := (mem_normalizer_iff.1 hg₁ z).1 hzD
  have hz₂p : z₂ ^ p = 1 := by rw [hz₂, conj_pow, hzp, mul_one, mul_inv_cancel]
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    apply hz1
    have : z = g₁⁻¹ * z₂ * g₁ := by rw [hz₂]; group
    rw [this, h]
    group
  set m : X := g₁ * n * g₁⁻¹ with hm
  have hmD : m ∈ normalizer (D : Set X) := mul_mem (mul_mem hg₁ hnD) (inv_mem hg₁)
  have hmk : ∃ k : ℕ, m ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by rw [hm, conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hmz : m * z₂ = z₂ * m := by
    calc m * z₂ = g₁ * (n * z) * g₁⁻¹ := by rw [hm, hz₂]; group
      _ = g₁ * (z * n) * g₁⁻¹ := by rw [hnz]
      _ = z₂ * m := by rw [hm, hz₂]; group
  have hmC : m ∉ centralizer (D : Set X) := by
    intro hmC
    apply hnC
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : g₁ * d * g₁⁻¹ ∈ D := (mem_normalizer_iff.1 hg₁ d).1 hd
    have h1 := mem_centralizer_iff.mp hmC _ hd'
    calc d * n = g₁⁻¹ * ((g₁ * d * g₁⁻¹) * m) * g₁ := by rw [hm]; group
      _ = g₁⁻¹ * (m * (g₁ * d * g₁⁻¹)) * g₁ := by rw [h1]
      _ = n * d := by rw [hm]; group
  have hzz₂ : z ∉ zpowers z₂ := fun h => hg₁z (zje_mem_zpowers_symm hz1 hz₂1 hzp hz₂p h)
  obtain ⟨b, hb0, hnb⟩ := zje_transvection_form hD hDc hzD hz1 hn hnD hnz hnC hz₂D hg₁z
  obtain ⟨c, hc0, hmc⟩ := zje_transvection_form hD hDc hz₂D hz₂1 hmk hmD hmz hmC hzD hzz₂
  obtain ⟨i, hi⟩ : ∃ i : ℕ, ((i * b : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    ⟨((b : ZMod p)⁻¹).val, by rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hb0,
      Nat.cast_one]⟩
  obtain ⟨i', hi'⟩ : ∃ i' : ℕ, ((i' * c : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    ⟨((c : ZMod p)⁻¹).val, by rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hc0,
      Nat.cast_one]⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ((j * c : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) :=
    ⟨(p - 1) * i', by rw [mul_assoc, Nat.cast_mul, hi', Nat.cast_one, mul_one]⟩
  have hAz : n ^ i * z * (n ^ i)⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((show Commute n z from hnz).pow_left i).eq
  have hAz₂ : n ^ i * z₂ * (n ^ i)⁻¹ = z₂ * z := by
    rw [transvection_conj_pow_eq hnz hnb i, pow_eq_pow_of_natCast_eq_of_pow_eq_one hzp hi, pow_one]
  have hBz₂ : m ^ j * z₂ * (m ^ j)⁻¹ = z₂ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((show Commute m z₂ from hmz).pow_left j).eq
  have hBz : m ^ j * z * (m ^ j)⁻¹ = z * z₂⁻¹ := by
    have h1 : z₂ ^ (p - 1) = z₂⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, hz₂p]
    rw [transvection_conj_pow_eq hmz hmc j, pow_eq_pow_of_natCast_eq_of_pow_eq_one hz₂p hj, h1]
  set A : X := n ^ i with hA
  set B : X := m ^ j with hB
  have hWz : (A * B * A) * z * (A * B * A)⁻¹ = z₂⁻¹ := by
    calc (A * B * A) * z * (A * B * A)⁻¹ = A * (B * (A * z * A⁻¹) * B⁻¹) * A⁻¹ := by group
      _ = A * (B * z * B⁻¹) * A⁻¹ := by rw [hAz]
      _ = (A * z * A⁻¹) * (A * z₂ * A⁻¹)⁻¹ := by rw [hBz]; group
      _ = z₂⁻¹ := by rw [hAz, hAz₂]; group
  have hWz₂ : (A * B * A) * z₂ * (A * B * A)⁻¹ = z := by
    have h1 : z₂ * (z * z₂⁻¹) = z := by
      calc z₂ * (z * z₂⁻¹) = (z₂ * z) * z₂⁻¹ := by group
        _ = (z * z₂) * z₂⁻¹ := by rw [hcomm z₂ hz₂D z hzD]
        _ = z := by group
    calc (A * B * A) * z₂ * (A * B * A)⁻¹ = A * (B * (A * z₂ * A⁻¹) * B⁻¹) * A⁻¹ := by group
      _ = A * ((B * z₂ * B⁻¹) * (B * z * B⁻¹)) * A⁻¹ := by rw [hAz₂]; group
      _ = A * (z₂ * (z * z₂⁻¹)) * A⁻¹ := by rw [hBz₂, hBz]
      _ = z := by rw [h1, hAz]
  have hmem : A * B * A ∈ normalizer (D : Set X) :=
    mul_mem (mul_mem (pow_mem hnD i) (pow_mem hmD j)) (pow_mem hnD i)
  clear_value A B z₂ m
  refine ⟨(A * B * A) * (A * B * A), mul_mem hmem hmem, fun d hd => ?_⟩
  obtain ⟨s, t, rfl⟩ := exists_pow_mul_pow_of_mem_plane hD hDc hz₂D hz₂1 hzD hzz₂ hd
  have hconj : ∀ u v : X, (A * B * A) * (u * v) * (A * B * A)⁻¹ =
      ((A * B * A) * u * (A * B * A)⁻¹) * ((A * B * A) * v * (A * B * A)⁻¹) := by
    intro u v; group
  have hWzs : (A * B * A) * z ^ s * (A * B * A)⁻¹ = z₂⁻¹ ^ s := by
    rw [← conj_pow, hWz]
  have hWz₂t : (A * B * A) * z₂ ^ t * (A * B * A)⁻¹ = z ^ t := by
    rw [← conj_pow, hWz₂]
  have hWz₂s : (A * B * A) * z₂⁻¹ ^ s * (A * B * A)⁻¹ = z⁻¹ ^ s := by
    rw [← conj_pow, show (A * B * A) * z₂⁻¹ * (A * B * A)⁻¹ =
      ((A * B * A) * z₂ * (A * B * A)⁻¹)⁻¹ by group, hWz₂]
  have hWzt : (A * B * A) * z ^ t * (A * B * A)⁻¹ = z₂⁻¹ ^ t := by
    rw [← conj_pow, hWz]
  calc (A * B * A * (A * B * A)) * (z ^ s * z₂ ^ t) * (A * B * A * (A * B * A))⁻¹
      = (A * B * A) * ((A * B * A) * (z ^ s * z₂ ^ t) * (A * B * A)⁻¹) * (A * B * A)⁻¹ := by
        group
    _ = (A * B * A) * (z₂⁻¹ ^ s * z ^ t) * (A * B * A)⁻¹ := by
        rw [hconj (z ^ s) (z₂ ^ t), hWzs, hWz₂t]
    _ = z⁻¹ ^ s * z₂⁻¹ ^ t := by rw [hconj (z₂⁻¹ ^ s) (z ^ t), hWz₂s, hWzt]
    _ = (z ^ s * z₂ ^ t)⁻¹ := by
        rw [mul_inv_rev, inv_pow, inv_pow]
        exact (((show Commute z z₂ from hcomm z hzD z₂ hz₂D).pow_pow s t).inv_inv).eq

end CFSG.LocalAnalysis.RankThreeTheoremC
