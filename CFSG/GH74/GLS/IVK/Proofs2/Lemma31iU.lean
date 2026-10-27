module

public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iCoreA

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels

namespace Lemma31iU

section Abstract

variable {G : Type} [Group G]

theorem mul_self_of_orderOf {x : G} (h : orderOf x = 2) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rw [h, pow_two] at this
  exact this

theorem ne_one_of_orderOf {x : G} (h : orderOf x = 2) : x ≠ 1 := by
  intro hx
  rw [hx, orderOf_one] at h
  exact absurd h (by norm_num)

theorem pow_sq_cases {z : G} (hzz : z * z = 1) (c : ℕ) : z ^ c = 1 ∨ z ^ c = z := by
  rcases Nat.even_or_odd c with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    rw [hr, ← two_mul, pow_mul, sq, hzz, one_pow]
  · right
    rw [hr, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]

theorem zpow_sq_cases {z : G} (hzz : z * z = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ k = 2 * q + r :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  rw [zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with rfl | rfl
  · left; simp
  · right; simp

theorem mem_sup_cases {u z : G} (huu : u * u = 1) (hzz : z * z = 1) (huz : u * z = z * u) {v : G}
    (hv : v ∈ zpowers u ⊔ zpowers z) : v = 1 ∨ v = u ∨ v = z ∨ v = u * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hsa : u * z * u⁻¹ = z⁻¹ := by
    rw [hzi, mul_inv_eq_iff_eq_mul]
    exact huz
  rw [sup_comm] at hv
  rcases Lemma31iCoreA.mem_sup_zpowers_reflected huu hsa hv with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases zpow_sq_cases hzz k with h | h
    · exact Or.inl (hk.trans h)
    · exact Or.inr (Or.inr (Or.inl (hk.trans h)))
  · rcases zpow_sq_cases hzz k with h | h
    · exact Or.inr (Or.inl (by rw [hk, h, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (by rw [hk, h]; exact huz.symm)))

theorem conj_dichotomy {u z x : G} (huu : u * u = 1) (hzz : z * z = 1) (huz : u * z = z * u)
    (hu1 : u ≠ 1) (huz' : u ≠ z) (hxz : x * z = z * x)
    (hmem : x * u * x⁻¹ ∈ zpowers u ⊔ zpowers z) : x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * z := by
  rcases mem_sup_cases huu hzz huz hmem with h | h | h | h
  · exfalso
    apply hu1
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exfalso
    apply huz'
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = x⁻¹ * z * x := by rw [h]
      _ = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  · exact Or.inr h

theorem a_form {z d a : G} {n : ℕ} (hn : 3 ≤ n) (hdo : orderOf d = 2 ^ (n - 1))
    (hdz : d ^ 2 ^ (n - 2) = z) (hzz : z * z = 1) (haa : a * a = z) {i : ℕ} (hai : a = d ^ i) :
    a = d ^ 2 ^ (n - 3) ∨ a = d ^ 2 ^ (n - 3) * z := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 3 := ⟨n - 3, by omega⟩
  have e1 : e + 3 - 3 = e := by omega
  have e2 : e + 3 - 2 = e + 1 := by omega
  have e3 : e + 3 - 1 = e + 2 := by omega
  rw [e3] at hdo
  rw [e2] at hdz
  rw [e1]
  obtain ⟨m, hm⟩ : ∃ m, m = 2 ^ e := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_two_pow
  have h2 : 2 ^ (e + 1) = 2 * m := by rw [hm]; ring
  have h4 : 2 ^ (e + 2) = 2 * (2 * m) := by rw [hm]; ring
  have hz : d ^ (2 * m) = z := by rw [← h2]; exact hdz
  have hii : d ^ (i + i) = d ^ (2 * m) := by
    rw [pow_add, ← hai, haa, hz]
  have hmod : i + i ≡ 2 * m [MOD orderOf d] := pow_eq_pow_iff_modEq.1 hii
  rw [hdo, h4, ← two_mul] at hmod
  have hmod' : i ≡ m [MOD 2 * m] := Nat.ModEq.mul_left_cancel' (by norm_num : (2 : ℕ) ≠ 0) hmod
  have hmi : i % (2 * m) = m := by
    have h5 : i % (2 * m) = m % (2 * m) := hmod'
    rw [h5]
    exact Nat.mod_eq_of_lt (by omega)
  have hi : i = 2 * m * (i / (2 * m)) + m := by
    have h6 := Nat.div_add_mod i (2 * m)
    rw [hmi] at h6
    exact h6.symm
  have hform : a = z ^ (i / (2 * m)) * d ^ m := by
    rw [hai]
    conv_lhs => rw [hi]
    rw [pow_add, pow_mul, hz]
  have hcomm : z * d ^ m = d ^ m * z := by
    rw [← hz]
    exact ((Commute.refl d).pow_pow (2 * m) m).eq
  rcases pow_sq_cases hzz (i / (2 * m)) with hc | hc
  · left
    rw [hform, hc, one_mul, ← hm]
  · right
    rw [hform, hc, ← hm]
    exact hcomm

end Abstract

section Prod

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem z_sq (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) :
    z * z = 1 :=
  mul_self_of_orderOf (h.inter_eq hz hz1).2

theorem sq_of_decomp (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    {a b : H} (ha : a ∈ K₁) (hb : b ∈ K₂) (hu2 : (a * b) * (a * b) = 1) (hu1 : a * b ≠ 1)
    (huz : a * b ≠ z) : a * a = z ∧ b * b = z := by
  have hzz := z_sq h hz hz1
  have hab : a * b = b * a := h.comm a ha b hb
  have e : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu2
  have haaK : a * a ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := mul_eq_one_iff_eq_inv.mp e
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem hb hb)
  rcases h.inter_cases hz hz1 _ haaK with h1 | h1
  · exfalso
    have hbb : b * b = 1 := by
      rw [h1, one_mul] at e
      exact e
    have hz' : z ∈ K₂ ⊓ K₁ := ⟨hz.2, hz.1⟩
    rcases h.eq_one_or_eq_z₁ hz hz1 ha h1 with ha1 | ha1 <;>
      rcases h.symm.eq_one_or_eq_z₁ hz' hz1 hb hbb with hb1 | hb1
    · exact hu1 (by rw [ha1, hb1, one_mul])
    · exact huz (by rw [ha1, hb1, one_mul])
    · exact huz (by rw [ha1, hb1, mul_one])
    · exact hu1 (by rw [ha1, hb1]; exact hzz)
  · refine ⟨h1, ?_⟩
    rw [h1] at e
    have : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz

theorem conj_a (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) {a b x : H} (hb : b ∈ K₂)
    (hx : x ∈ K₁)
    (hxu : x * (a * b) * x⁻¹ = a * b ∨ x * (a * b) * x⁻¹ = (a * b) * z) :
    x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a * z := by
  have hxb : x * b * x⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.comm x hx b hb
  have hzb : z * b = b * z := h.z_comm hz (Subgroup.mem_sup_right hb)
  have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * b := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (x * a * x⁻¹) * b := by rw [hxb]
  rw [e] at hxu
  rcases hxu with h1 | h1
  · exact Or.inl (mul_right_cancel h1)
  · refine Or.inr (mul_right_cancel (b := b) ?_)
    rw [h1]
    calc a * b * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [hzb]
      _ = a * z * b := by group

theorem swap_b (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {t a b : H}
    (htt : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) (ha : a ∈ K₁) (hb : b ∈ K₂)
    (htu : t * (a * b) * t⁻¹ = a * b ∨ t * (a * b) * t⁻¹ = (a * b) * z) :
    b = t * a * t⁻¹ ∨ b = t * a * t⁻¹ * z := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ha' : t * a * t⁻¹ ∈ K₂ := ProdSL2.swap_mem₁ hK ha
  have hb' : t * b * t⁻¹ ∈ K₁ := ProdSL2.swap_mem₂ htt hK hb
  have hc : ∃ c : H, (c = 1 ∨ c = z) ∧ t * (a * b) * t⁻¹ = a * b * c := by
    rcases htu with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1, mul_one]⟩
    · exact ⟨z, Or.inr rfl, h1⟩
  obtain ⟨c, hcz, hc⟩ := hc
  have hcK : c ∈ K₂ := by
    rcases hcz with hcz | hcz
    · rw [hcz]; exact K₂.one_mem
    · rw [hcz]; exact hz.2
  have hba : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b * c := by
    rw [← hc]
    calc (t * b * t⁻¹) * (t * a * t⁻¹) = t * (b * a) * t⁻¹ := by group
      _ = t * (a * b) * t⁻¹ := by rw [← h.comm a ha b hb]
  have hw : a⁻¹ * (t * b * t⁻¹) = b * c * (t * a * t⁻¹)⁻¹ := by
    calc a⁻¹ * (t * b * t⁻¹)
        = a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b * c) * (t * a * t⁻¹)⁻¹ := by rw [hba]
      _ = b * c * (t * a * t⁻¹)⁻¹ := by group
  have hwmem : a⁻¹ * (t * b * t⁻¹) ∈ K₁ ⊓ K₂ := by
    refine ⟨K₁.mul_mem (K₁.inv_mem ha) hb', ?_⟩
    rw [hw]
    exact K₂.mul_mem (K₂.mul_mem hb hcK) (K₂.inv_mem ha')
  rcases h.inter_cases hz hz1 _ hwmem with h1 | h1
  · left
    have h2 : t * b * t⁻¹ = a := by
      calc t * b * t⁻¹ = a * (a⁻¹ * (t * b * t⁻¹)) := by group
        _ = a * 1 := by rw [h1]
        _ = a := mul_one a
    calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
      _ = t⁻¹ * a * t := by rw [h2]
      _ = t * a * t⁻¹ := by rw [hti]
  · right
    have h2 : t * b * t⁻¹ = a * z := by
      calc t * b * t⁻¹ = a * (a⁻¹ * (t * b * t⁻¹)) := by group
        _ = a * z := by rw [h1]
    have htz : t * z * t⁻¹ = z := h.t_comm_z hz hz1 htt hK
    calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
      _ = t⁻¹ * (a * z) * t := by rw [h2]
      _ = t * (a * z) * t⁻¹ := by rw [hti]
      _ = t * a * t⁻¹ * (t * z * t⁻¹) := by group
      _ = t * a * t⁻¹ * z := by rw [htz]

theorem u_form (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    {t D a b : H} (htt : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂)
    (hD : D ∈ K₁) (ha : a = D ∨ a = D * z) (hb : b = t * a * t⁻¹ ∨ b = t * a * t⁻¹ * z) :
    a * b = D * (t * D * t⁻¹) ∨ a * b = D * (t * D * t⁻¹) * z := by
  have hD' : t * D * t⁻¹ ∈ K₂ := ProdSL2.swap_mem₁ hK hD
  have hzD' : z * (t * D * t⁻¹) = (t * D * t⁻¹) * z :=
    h.z_comm hz (Subgroup.mem_sup_right hD')
  have hzz := z_sq h hz hz1
  have htz : t * z * t⁻¹ = z := h.t_comm_z hz hz1 htt hK
  have hta : t * (D * z) * t⁻¹ = (t * D * t⁻¹) * z := by
    calc t * (D * z) * t⁻¹ = (t * D * t⁻¹) * (t * z * t⁻¹) := by group
      _ = (t * D * t⁻¹) * z := by rw [htz]
  rcases ha with ha | ha
  · rw [ha] at hb
    rw [ha]
    rcases hb with hb | hb
    · exact Or.inl (by rw [hb])
    · exact Or.inr (by rw [hb]; group)
  · rw [ha] at hb
    rw [ha]
    rcases hb with hb | hb
    · left
      rw [hb, hta]
      calc D * z * (t * D * t⁻¹ * z) = D * (z * (t * D * t⁻¹)) * z := by group
        _ = D * ((t * D * t⁻¹) * z) * z := by rw [hzD']
        _ = D * (t * D * t⁻¹) * (z * z) := by group
        _ = D * (t * D * t⁻¹) := by rw [hzz, mul_one]
    · right
      rw [hb, hta]
      calc D * z * (t * D * t⁻¹ * z * z) = D * z * (t * D * t⁻¹) * (z * z) := by group
        _ = D * z * (t * D * t⁻¹) := by rw [hzz, mul_one]
        _ = D * (z * (t * D * t⁻¹)) := by group
        _ = D * ((t * D * t⁻¹) * z) := by rw [hzD']
        _ = D * (t * D * t⁻¹) * z := by group

end Prod

end Lemma31iU

end CFSG.GH74.GLS.IVK.Proofs2
