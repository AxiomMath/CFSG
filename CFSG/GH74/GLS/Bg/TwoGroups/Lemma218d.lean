module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218c

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Subgroup

section Main

variable {E : Type} [CommGroup E] [Finite E] {X : Subgroup (MulAut E)} {S : Sylow 2 ↥X}

theorem Ctx.centS_sq (c : Ctx E X S) {x : ↥X} (hx : x ∈ (S : Subgroup ↥X)) (hx1 : x ≠ 1)
    (φ : ↥(Subgroup.centralizer ({x} : Set ↥X)) ≃* Z2xS3) {g : ↥X}
    (hg : ∀ s ∈ (S : Subgroup ↥X), g * s = s * g) : g * g = 1 := by
  obtain ⟨y, hy, hy1, hyx⟩ := c.exists_other x
  have hmemC : ∀ w : ↥X, w ∈ Subgroup.centralizer ({x} : Set ↥X) ↔ w * x = x * w :=
    fun w => Subgroup.mem_centralizer_singleton_iff
  have hxC : x ∈ Subgroup.centralizer ({x} : Set ↥X) := (hmemC x).mpr rfl
  have hyC : y ∈ Subgroup.centralizer ({x} : Set ↥X) := (hmemC y).mpr (c.comm hy hx)
  have hgC : g ∈ Subgroup.centralizer ({x} : Set ↥X) := (hmemC g).mpr (hg x hx)
  have ha2 : φ ⟨x, hxC⟩ * φ ⟨x, hxC⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    exact congrArg φ (Subtype.ext (c.hS2 x hx))
  have hb2 : φ ⟨y, hyC⟩ * φ ⟨y, hyC⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    exact congrArg φ (Subtype.ext (c.hS2 y hy))
  have hab : φ ⟨x, hxC⟩ * φ ⟨y, hyC⟩ = φ ⟨y, hyC⟩ * φ ⟨x, hxC⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (c.comm hx hy))
  have ha1 : φ ⟨x, hxC⟩ ≠ 1 := by
    intro h
    rw [← map_one φ] at h
    exact hx1 (congrArg Subtype.val (φ.injective h))
  have hb1 : φ ⟨y, hyC⟩ ≠ 1 := by
    intro h
    rw [← map_one φ] at h
    exact hy1 (congrArg Subtype.val (φ.injective h))
  have hne : φ ⟨x, hxC⟩ ≠ φ ⟨y, hyC⟩ := by
    intro h
    exact hyx (congrArg Subtype.val (φ.injective h)).symm
  have hca : φ ⟨g, hgC⟩ * φ ⟨x, hxC⟩ = φ ⟨x, hxC⟩ * φ ⟨g, hgC⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hg x hx))
  have hcb : φ ⟨g, hgC⟩ * φ ⟨y, hyC⟩ = φ ⟨y, hyC⟩ * φ ⟨g, hgC⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hg y hy))
  have := z1_check _ _ (φ ⟨g, hgC⟩) ha2 hb2 hab ha1 hb1 hne hca hcb
  rw [← map_mul, ← map_one φ] at this
  exact congrArg Subtype.val (φ.injective this)

omit [Finite E] in
theorem exists_u_t (x : ↥X) (φ : ↥(Subgroup.centralizer ({x} : Set ↥X)) ≃* Z2xS3) :
    ∃ u t : ↥X, u * x = x * u ∧ orderOf u = 3 ∧ t * u * t⁻¹ = u⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hc3 : c3 ^ 3 = 1 := by decide
  have hc31 : c3 ≠ 1 := by decide
  have hτc : τ * c3 * τ⁻¹ = c3⁻¹ := by decide
  let p3 : Z2xS3 := ((1 : Multiplicative (ZMod 2)), c3)
  let pτ : Z2xS3 := ((1 : Multiplicative (ZMod 2)), τ)
  have hp3 : p3 ^ 3 = 1 := Prod.ext (one_pow 3) hc3
  have hp31 : p3 ≠ 1 := fun h => hc31 (congrArg Prod.snd h)
  have hpτ : pτ * p3 * pτ⁻¹ = p3⁻¹ := Prod.ext (by simp [pτ, p3]) hτc
  let uu : ↥(Subgroup.centralizer ({x} : Set ↥X)) := φ.symm p3
  let tt : ↥(Subgroup.centralizer ({x} : Set ↥X)) := φ.symm pτ
  have huu3 : uu ^ 3 = 1 := by
    show (φ.symm p3) ^ 3 = 1
    rw [← map_pow, hp3, map_one]
  have huu1 : uu ≠ 1 := by
    intro h
    apply hp31
    have := congrArg φ h
    simpa [uu] using this
  have htt : tt * uu * tt⁻¹ = uu⁻¹ := by
    show φ.symm pτ * φ.symm p3 * (φ.symm pτ)⁻¹ = (φ.symm p3)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, hpτ]
  refine ⟨uu, tt, Subgroup.mem_centralizer_singleton_iff.mp uu.2, ?_, ?_⟩
  · have hpow : (uu : ↥X) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, huu3]; rfl
    have hne : (uu : ↥X) ≠ 1 := fun h => huu1 (Subtype.ext h)
    exact orderOf_eq_prime hpow hne
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, htt]

theorem Ctx.exists_v (c : Ctx E X S) {x : ↥X} (hx : x ∈ (S : Subgroup ↥X)) (hx1 : x ≠ 1)
    (φ : ↥(Subgroup.centralizer ({x} : Set ↥X)) ≃* Z2xS3)
    (hcon : ∀ a b : ↥X, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → IsConj a b) :
    ∃ v : ↥X, orderOf v = 3 ∧
      (∀ s, s ∈ (S : Subgroup ↥X) ↔ v * s * v⁻¹ ∈ (S : Subgroup ↥X)) ∧
      ∃ s ∈ (S : Subgroup ↥X), v * s * v⁻¹ ≠ s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy, hy1, hyx⟩ := c.exists_other x
  have hz : x * y ∈ (S : Subgroup ↥X) := mul_mem hx hy
  have hz1 : x * y ≠ 1 := by
    intro h
    apply hyx
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right (c.hS2 x hx)]
  have fusion : ∀ a b : ↥X, a ∈ (S : Subgroup ↥X) → b ∈ (S : Subgroup ↥X) → a ≠ 1 → b ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup ↥X) : Set ↥X), n⁻¹ * a * n = b := by
    intro a b ha hb ha1 hb1
    obtain ⟨d, hd⟩ := isConj_iff.mp (hcon a b ha1 (c.hS2 a ha) hb1 (c.hS2 b hb))
    have hg : (d⁻¹)⁻¹ * a * d⁻¹ = b := by simpa using hd
    obtain ⟨n, hn, hnn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S a d⁻¹
      (Subgroup.mem_centralizer_iff.mpr (fun h hh => c.comm hh ha))
      (by rw [hg]; exact Subgroup.mem_centralizer_iff.mpr (fun h hh => c.comm hh hb))
    exact ⟨n, hn, by rw [← hnn, hg]⟩
  let N : Subgroup ↥X := Subgroup.normalizer ((S : Subgroup ↥X) : Set ↥X)
  let ψ := (S : Subgroup ↥X).normalizerMonoidHom
  obtain ⟨n₁, hn₁, hn₁y⟩ := fusion x y hx hy hx1 hy1
  obtain ⟨n₂, hn₂, hn₂z⟩ := fusion x (x * y) hx hz hx1 hz1
  let m₁ : N := ⟨n₁⁻¹, inv_mem hn₁⟩
  let m₂ : N := ⟨n₂⁻¹, inv_mem hn₂⟩
  let sx : (S : Subgroup ↥X) := ⟨x, hx⟩
  have hψ1 : ((ψ m₁) sx : ↥X) = y := by
    show n₁⁻¹ * x * n₁⁻¹⁻¹ = y
    rw [inv_inv]; exact hn₁y
  have hψ2 : ((ψ m₂) sx : ↥X) = x * y := by
    show n₂⁻¹ * x * n₂⁻¹⁻¹ = x * y
    rw [inv_inv]; exact hn₂z
  have hψ0 : ((1 : MulAut (S : Subgroup ↥X)) sx : ↥X) = x := rfl
  have hMA : Nat.card (MulAut (S : Subgroup ↥X)) = 6 := by
    let _ : CommGroup (S : Subgroup ↥X) :=
      { (inferInstance : Group (S : Subgroup ↥X)) with
        mul_comm := fun a b => Subtype.ext (c.comm a.2 b.2) }
    have := card_mulAut_two (E := (S : Subgroup ↥X)) (fun e => Subtype.ext (c.hS2 e e.2)) 2
      (by rw [c.hS4]; norm_num)
    rw [this]
    decide
  have hR3 : 3 ≤ Nat.card ψ.range := by
    have h01 : (1 : ψ.range) ≠ ⟨ψ m₁, ⟨m₁, rfl⟩⟩ := by
      intro h
      have := congrArg (fun r : ψ.range => ((r : MulAut (S : Subgroup ↥X)) sx : ↥X)) h
      simp only [hψ1] at this
      exact hyx (hψ0.symm.trans this).symm
    have h02 : (1 : ψ.range) ≠ ⟨ψ m₂, ⟨m₂, rfl⟩⟩ := by
      intro h
      have := congrArg (fun r : ψ.range => ((r : MulAut (S : Subgroup ↥X)) sx : ↥X)) h
      simp only [hψ2] at this
      apply hy1
      have h3 : x = x * y := hψ0.symm.trans this
      exact (mul_eq_left.mp h3.symm)
    have h12 : (⟨ψ m₁, ⟨m₁, rfl⟩⟩ : ψ.range) ≠ ⟨ψ m₂, ⟨m₂, rfl⟩⟩ := by
      intro h
      have := congrArg (fun r : ψ.range => ((r : MulAut (S : Subgroup ↥X)) sx : ↥X)) h
      simp only [hψ1, hψ2] at this
      apply hx1
      exact (mul_eq_right.mp this.symm)
    have hinj : Function.Injective
        (![(1 : ψ.range), ⟨ψ m₁, ⟨m₁, rfl⟩⟩, ⟨ψ m₂, ⟨m₂, rfl⟩⟩] : Fin 3 → ψ.range) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at hij; first
        | exact h01 hij | exact h02 hij | exact h12 hij | exact h01 hij.symm | exact h02 hij.symm
        | exact h12 hij.symm)
    simpa using Nat.card_le_card_of_injective _ hinj
  have h3R : 3 ∣ Nat.card ψ.range := by
    have hd : Nat.card ψ.range ∣ 6 := hMA ▸ Subgroup.card_subgroup_dvd_card ψ.range
    have hle : Nat.card ψ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card ψ.range <;> omega
  have h3N : 3 ∣ Nat.card N := dvd_trans h3R (Subgroup.card_range_dvd ψ)
  obtain ⟨v₀, hv₀⟩ := exists_prime_orderOf_dvd_card' 3 h3N
  have hv : orderOf (v₀ : ↥X) = 3 := (Subgroup.orderOf_coe v₀).trans hv₀
  have hvN : (v₀ : ↥X) ∈ Subgroup.normalizer ((S : Subgroup ↥X) : Set ↥X) := v₀.2
  have hvn := Subgroup.mem_normalizer_iff.mp hvN
  refine ⟨v₀, hv, hvn, ?_⟩
  by_contra hcon'
  have hall : ∀ s ∈ (S : Subgroup ↥X), (v₀ : ↥X) * s * (v₀ : ↥X)⁻¹ = s := by
    intro s hs
    by_contra h
    exact hcon' ⟨s, hs, h⟩
  have hcomm : ∀ s ∈ (S : Subgroup ↥X), (v₀ : ↥X) * s = s * (v₀ : ↥X) := by
    intro s hs
    have := hall s hs
    calc (v₀ : ↥X) * s = (v₀ : ↥X) * s * (v₀ : ↥X)⁻¹ * (v₀ : ↥X) := by group
      _ = s * (v₀ : ↥X) := by rw [this]
  have hsq := c.centS_sq hx hx1 φ hcomm
  have hv3 : (v₀ : ↥X) ^ 3 = 1 := by rw [← hv]; exact pow_orderOf_eq_one _
  have : (v₀ : ↥X) = 1 := by
    calc (v₀ : ↥X) = (v₀ : ↥X) ^ 3 := by
          rw [pow_succ, pow_two, hsq, one_mul]
      _ = 1 := hv3
  rw [this, orderOf_one] at hv
  omega

end Main

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
