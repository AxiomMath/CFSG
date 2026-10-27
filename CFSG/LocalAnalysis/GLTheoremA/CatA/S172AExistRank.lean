module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut)

theorem card_range_ge {n r : ℕ} (hn : n = 2 * r + 1) (hr : 3 ≤ r) {Ω : Type} [Group Ω] [Finite Ω]
    {B : Subgroup Ω} {x : Ω} (Θ : VecAut n →* Ω) (φ : ↥B →* VecAut n)
    (hΘ : Function.Injective Θ)
    (hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x)
    (hBel : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxS : ∀ g : VecAut n, x * Θ g = Θ g * x)
    (hZ : Subgroup.center (VecAut n) = ⊥)
    (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B) : 3 ^ r ≤ Nat.card φ.range := by
  have hV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = 2 * r + 1 := by
    rw [Module.finrank_fin_fun, hn]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTel, hTcard, v₀, hv₀, hfix⟩ := GL.exists_torus_fixed (V := Fin n → ZMod 2) hV
  obtain ⟨P, hPne, hP2, hPnorm⟩ := GL.exists_twoGroup (V := Fin n → ZMod 2) (by omega) hv₀
  let X : Subgroup Ω := P.map Θ
  have hXne : X ≠ ⊥ := fun h => hPne ((Subgroup.map_eq_bot_iff_of_injective P hΘ).1 h)
  have hX2 : IsPGroup 2 ↥X := IsPGroup.map hP2 Θ
  have hxx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hordx : orderOf x = 3 := orderOf_eq_prime hxx3 hx1
  have hyc : ∀ (y : ↥(Subgroup.zpowers x)) (g : VecAut n), (y : Ω) * Θ g = Θ g * (y : Ω) := by
    intro y g
    obtain ⟨k, hk⟩ := y.2
    rw [← hk]
    exact (Commute.zpow_left (show Commute x (Θ g) from hxS _) k).eq
  have hcomm : ∀ (t : ↥T) (y : ↥(Subgroup.zpowers x)),
      Commute ((Θ.comp T.subtype) t) (Subgroup.subtype (Subgroup.zpowers x) y) := by
    intro t y
    exact (hyc y (t : VecAut n)).symm
  let Ψ : ↥T × ↥(Subgroup.zpowers x) →* Ω :=
    (Θ.comp T.subtype).noncommCoprod (Subgroup.subtype (Subgroup.zpowers x)) hcomm
  have hΨ : ∀ p, Ψ p = Θ (p.1 : VecAut n) * (p.2 : Ω) := fun p => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨t, y⟩ h
    rw [hΨ] at h
    simp only at h
    have hy : Θ (t : VecAut n) = ((y : Ω))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hcen : (t : VecAut n) ∈ Subgroup.center (VecAut n) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hΘ
      rw [map_mul, map_mul, hy]
      have := hyc y g
      calc Θ g * (y : Ω)⁻¹ = (y : Ω)⁻¹ * ((y : Ω) * Θ g) * (y : Ω)⁻¹ := by group
        _ = (y : Ω)⁻¹ * (Θ g * (y : Ω)) * (y : Ω)⁻¹ := by rw [this]
        _ = (y : Ω)⁻¹ * Θ g := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    have ht : t = 1 := Subtype.ext hcen
    rw [ht] at h
    have hy1 : (y : Ω) = 1 := by simpa using h
    refine Prod.ext ?_ (Subtype.ext hy1)
    exact ht
  let E : Subgroup Ω := Ψ.range
  have hEcard : Nat.card E = 3 ^ (r + 1) := by
    have h1 : Nat.card E = Nat.card (↥T × ↥(Subgroup.zpowers x)) :=
      (Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm
    rw [h1, Nat.card_prod, hTcard, Nat.card_zpowers, hordx, pow_succ]
  have hcommP : ∀ p q : ↥T × ↥(Subgroup.zpowers x), p * q = q * p := by
    rintro ⟨t₁, y₁⟩ ⟨t₂, y₂⟩
    refine Prod.ext ?_ ?_
    · exact hTel.1.is_comm.comm t₁ t₂
    · obtain ⟨k₁, hk₁⟩ := y₁.2
      obtain ⟨k₂, hk₂⟩ := y₂.2
      apply Subtype.ext
      show (y₁ : Ω) * y₂ = y₂ * y₁
      rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
  have hEel : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨p, hp⟩ := a.2
      obtain ⟨q, hq⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, hcommP]
    · rintro a ⟨⟨t, y⟩, rfl⟩
      rw [← map_pow]
      have ht3 : (t : VecAut n) ^ 3 = 1 := hTel.2 t t.2
      have hy3 : (y : Ω) ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := y.2
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxx3, one_zpow]
      have : (t, y) ^ 3 = (1 : ↥T × ↥(Subgroup.zpowers x)) := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simpa using ht3
        · simpa using hy3
      rw [this, map_one]
  have hEnorm : E ≤ Subgroup.normalizer (X : Set Ω) := by
    rintro _ ⟨⟨t, y⟩, rfl⟩
    rw [hΨ]
    show Θ (t : VecAut n) * (y : Ω) ∈ Subgroup.normalizer (X : Set Ω)
    apply Subgroup.mul_mem
    · have htN := hPnorm (t : VecAut n) (hfix _ t.2)
      have htN' := hPnorm (t : VecAut n)⁻¹ (GL.inv_apply_of_fix (hfix _ t.2))
      rw [Subgroup.mem_normalizer_iff]
      intro h'
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hp' := (Subgroup.mem_normalizer_iff.1 htN p).1 hp
        refine ⟨(t : VecAut n) * p * (t : VecAut n)⁻¹, hp', ?_⟩
        simp only [map_mul, map_inv]
      · rintro ⟨q, hq, hqe⟩
        have hq' := (Subgroup.mem_normalizer_iff.1 htN' q).1 hq
        refine ⟨(t : VecAut n)⁻¹ * q * (t : VecAut n)⁻¹⁻¹, hq', ?_⟩
        simp only [map_mul, map_inv, inv_inv] at hqe ⊢
        rw [hqe]
        group
    · apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨p, hp, rfl⟩
      exact (hyc y p).symm
  have hle := le_twoLocalPrimeRank_of_normalizer (G := Ω) Nat.prime_three hXne hX2 hEel hEcard hEnorm
  have h3 : 3 ^ (r + 1) ≤ Nat.card B := by
    refine le_trans (Nat.pow_le_pow_right (by norm_num) hle) ?_
    exact hrank
  have hker3 : Nat.card φ.ker = 3 := by
    have : φ.ker = (Subgroup.zpowers x).subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hxB)).toEquiv,
      Nat.card_zpowers, hordx]
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hker3] at hmul
  have h4 : 3 * 3 ^ r ≤ 3 * Nat.card φ.range := by
    rw [hmul, ← pow_succ']
    exact h3
  exact Nat.le_of_mul_le_mul_left h4 (by norm_num)


end CFSG.LocalAnalysis.GLTheoremA.S172A

end
