module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitAffine
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitAct

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem tau_facts (ε : Eps) :
    (∀ x < 64, qfB ε (bmulVec 6 6 (CPrime.reflRows ε 1) x ^^^ 1) = qfB ε x) ∧
      bmul 6 6 (CPrime.reflRows ε 1) (CPrime.reflRows ε 1) = id6 ∧
      bmulVec 6 6 (CPrime.reflRows ε 1) 1 = 1 := by
  cases ε <;> decide +kernel

@[expose] def tauMat (ε : Eps) : Matrix (Fin 6) (Fin 6) (ZMod 2) := toMat 6 6 (CPrime.reflRows ε 1)

theorem tauMat_mul_self (ε : Eps) : tauMat ε * tauMat ε = 1 := by
  rw [tauMat, ← toMat_bmul, (tau_facts ε).2.1, toMat_id6]

theorem tauMat_e₀ (ε : Eps) : tauMat ε *ᵥ (Pi.single 0 1 : V6) = Pi.single 0 1 := by
  have h1 : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
  rw [h1, tauMat, mulVec_toVec, (tau_facts ε).2.2]

theorem qfV_tau_add (ε : Eps) (v : V6) :
    qfV ε (tauMat ε *ᵥ v + Pi.single 0 1) = qfV ε v := by
  have h1 : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
  conv_lhs => rw [← toVec_vecBits v, h1, tauMat, mulVec_toVec, ← toVec_xor]
  have hx := vecBits_lt v
  have hlt : bmulVec 6 6 (CPrime.reflRows ε 1) (vecBits v) ^^^ 1 < 64 :=
    Nat.xor_lt_two_pow (n := 6) (by simpa using bmulVec_lt _ _) (by norm_num)
  rw [qfV_toVec ε hlt, (tau_facts ε).1 _ hx, qfV]

theorem qfV_inv_tau {ε : Eps} {σ : Equiv.Perm V6} (hσ : ∀ v, qfV ε (σ v + Pi.single 0 1) = qfV ε v)
    (v : V6) : qfV ε (σ⁻¹ (tauMat ε *ᵥ v)) = qfV ε v := by
  have := hσ (σ⁻¹ (tauMat ε *ᵥ v))
  rw [perm_apply_inv, qfV_tau_add] at this
  exact this.symm

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A) (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
include hS hC hinv

theorem trichotomyX [Finite G] :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ A ⊔ (P ⊔ zpowers x₀ ⊔ zpowers t) ∨
    (∀ v : V6, ∃ g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G),
      (∀ q ∈ Q, g * q = q * g) ∧ cOf ψ t k g = v) ∨
    ∃ g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G),
      cOf ψ t k g = Pi.single 0 1 ∧ ∀ v, lin ψ g v = tauMat ε *ᵥ v := by
  set Θ := hC.affHomNX hS hinv
  have hlin0 : ∀ g : normalizer ((A ⊔ zpowers t : Subgroup G) : Set G), lin ψ g 0 = 0 :=
    fun g => map_zero_of_mem_linGroup
      (hS.rad.linHom_mem_linGroup ⟨g, hC.normalizes_QX hS hinv g.2⟩)
  have hΓaff : ∀ γ ∈ Θ.range, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z := by
    rintro _ ⟨g, rfl⟩ x y z
    have hgQ := hC.normalizes_QX hS hinv g.2
    simp only [Θ, affHomN_applyX]
    rw [hS.rad.lin_add hgQ, hS.rad.lin_add hgQ]
    have e : ∀ c u v w : V6, c + (u + v + w) = c + u + (c + v) + (c + w) := by
      intro c u v w
      have := v6_add_self c
      calc c + (u + v + w) = c + u + v + w + (c + c) := by rw [this, add_zero]; abel
        _ = c + u + (c + v) + (c + w) := by abel
    exact e _ _ _ _
  have hΘK : ∀ (y : G) (hy : y ∈ P ⊔ zpowers x₀),
      Θ ⟨y, hC.K_le_N1X hS hy⟩ = hS.linK ⟨y, hy⟩ := by
    intro y hy
    refine Equiv.ext fun v => ?_
    rw [affHomN_applyX, cOf_eq_zero_of_commuteX hS (hS.commute_of_mem_K hy), zero_add]
    rfl
  have hΓ0 : ∀ γ ∈ Θ.range, γ 0 = 0 → γ ∈ hS.linK.range := by
    rintro _ ⟨g, rfl⟩ h0
    have hc : cOf ψ t k g = 0 := by
      have := h0
      rwa [affHomN_applyX, hlin0, add_zero] at this
    have hgNA := hC.mem_NA_of_cOf_eq_zeroX hS hinv g.2 hc
    obtain ⟨b, hb, x, hx, hbx⟩ := exists_mul_of_mem_sup_normalizer hC.PT_le_normalizer hgNA
    obtain ⟨y, hy, hxy⟩ := (hS.mem_supT_iff hS.K_le_H₀).1 hx
    have htQ : t ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun q hq => by
      rw [← hS.shape.commute_of_mem (hS.rad.Q_le_L hq), mul_inv_cancel_right]
      exact hq
    have hyQ := hS.K_le_normalizer_Q hy
    have hbQ : b ∈ normalizer (Q : Set G) := hC.mem_normalizer_Q_of_mem_A hb
    refine ⟨⟨y, hy⟩, Equiv.ext fun v => ?_⟩
    change lin ψ y v = cOf ψ t k g + lin ψ g v
    have hxQ : x ∈ normalizer (Q : Set G) := by
      rcases hxy with h | h <;> rw [h]
      · exact hyQ
      · exact mul_mem hyQ htQ
    rw [hc, zero_add, show (g : G) = b * x from hbx, hS.rad.lin_mul hbQ hxQ,
      hC.lin_of_mem_AX hS hb]
    rcases hxy with h | h
    · rw [h]
    · rw [h, hS.rad.lin_mul hyQ htQ]
      congr 1
      refine ((hS.rad.lin_eq_iff htQ v v).2 ?_).symm
      rw [← hS.shape.commute_of_mem (hS.rad.Q_le_L (hS.rad.ψ_mem v)), mul_inv_cancel_right]
  have hKΓ : hS.linK.range ≤ Θ.range := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨y, hC.K_le_N1X hS hy⟩, hΘK y hy⟩
  rcases affine_trichotomy hS hΓ0 hKΓ hΓaff with h | h | hO
  · left
    intro g hg
    have := h (Θ ⟨g, hg⟩) ⟨_, rfl⟩
    rw [affHomN_applyX, hlin0, add_zero] at this
    exact hC.mem_NA_of_cOf_eq_zeroX hS hinv hg this
  · right; left
    intro w
    obtain ⟨_, ⟨g, rfl⟩, hγ⟩ := h w
    have hc : cOf ψ t k g = w := by
      have := hγ 0
      rwa [affHomN_applyX, hlin0, add_zero, zero_add] at this
    refine ⟨g, g.2, fun q hq => ?_, hc⟩
    obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    have h1 : lin ψ g v = v := by
      have := hγ v
      rw [affHomN_applyX, hc, add_comm] at this
      exact add_right_cancel this
    rw [hS.rad.lin_eq_iff (hC.normalizes_QX hS hinv g.2)] at h1
    calc (g : G) * ψ v = g * ψ v * (g : G)⁻¹ * g := by group
      _ = ψ v * g := by rw [h1]
  · right; right
    have hq : ∀ γ ∈ Θ.range, ∀ v, qfV ε (γ v) = qfV ε v := by
      intro γ hγ v
      rcases qfV_cases ε v with h0 | h1
      · rw [h0]
        exact (hO _).1 (perm_mem_orbit ((hO v).2 h0) hγ)
      · rw [h1]
        rcases qfV_cases ε (γ v) with h0' | h1'
        · exfalso
          have := perm_mem_orbit ((hO _).2 h0') (inv_mem hγ)
          rw [perm_inv_apply γ v, hO, h1] at this
          exact one_ne_zero this
        · exact h1'
    have he₀ : qfV ε (Pi.single 0 1 : V6) = 0 := by
      have h1 : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
      rw [h1, qfV_toVec ε (by norm_num)]
      cases ε <;> rfl
    obtain ⟨_, ⟨g₁, rfl⟩, hg₁⟩ := mem_orbit_iff.1 ((hO _).2 he₀)
    have hc₁ : cOf ψ t k g₁ = Pi.single 0 1 := by
      rw [affHomN_applyX, hlin0, add_zero] at hg₁
      exact hg₁
    have hg₁Q := hC.normalizes_QX hS hinv g₁.2
    set σ := hS.rad.linHom ⟨g₁, hg₁Q⟩
    have hσ : ∀ v, qfV ε (σ v + Pi.single 0 1) = qfV ε v := by
      intro v
      have := hq _ ⟨g₁, rfl⟩ v
      rwa [affHomN_applyX, hc₁, add_comm] at this
    set ω : Equiv.Perm V6 := σ⁻¹ *
      { toFun := fun v => tauMat ε *ᵥ v
        invFun := fun v => tauMat ε *ᵥ v
        left_inv := fun v => by dsimp only; rw [mulVec_mulVec, tauMat_mul_self, one_mulVec]
        right_inv := fun v => by dsimp only; rw [mulVec_mulVec, tauMat_mul_self, one_mulVec] }
    have hω : ω ∈ orthGroup ε := by
      refine ⟨fun x y => ?_, fun v => qfV_inv_tau hσ v⟩
      change σ⁻¹ (tauMat ε *ᵥ (x + y)) = σ⁻¹ (tauMat ε *ᵥ x) + σ⁻¹ (tauMat ε *ᵥ y)
      rw [mulVec_add]
      exact linGroup.inv_mem (hS.rad.linHom_mem_linGroup ⟨g₁, hg₁Q⟩) _ _
    obtain ⟨h, hhH, hhN, hh⟩ := hS.inputs.orth ω hω
    have hhK := hS.inputs.outer.normalizer_Q h hhH hhN
    have hhN1 := hC.K_le_N1X hS hhK
    refine ⟨g₁ * h, mul_mem g₁.2 hhN1, ?_, fun v => ?_⟩
    · rw [hC.cOf_mulX hS hinv g₁.2 hhN1, cOf_eq_zero_of_commuteX hS (hS.commute_of_mem_K hhK),
        hlin0 g₁, add_zero, hc₁]
    · rw [hS.rad.lin_mul hg₁Q hhN, hh]
      change σ (σ⁻¹ (tauMat ε *ᵥ v)) = tauMat ε *ᵥ v
      exact perm_apply_inv σ _

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
