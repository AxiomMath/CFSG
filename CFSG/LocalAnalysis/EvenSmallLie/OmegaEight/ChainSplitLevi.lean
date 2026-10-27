module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitRho

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G] [Finite G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G}
  {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
include hS

theorem t_mem_normalizer_Q : t ∈ normalizer (Q : Set G) :=
  mem_normalizer_of_conj_mem fun q hq => by
    rw [← hS.shape.commute_of_mem (hS.rad.Q_le_L hq), mul_inv_cancel_right]
    exact hq

theorem TH_le_normalizer_Q : U ⊔ zpowers x₀ ⊔ zpowers t ≤ normalizer (Q : Set G) :=
  sup_le (hS.S₀_le_K.trans hS.K_le_normalizer_Q) (zpowers_le.2 hS.t_mem_normalizer_Q)

theorem lin_mem_orth {y : G} (hy : y ∈ U ⊔ zpowers x₀ ⊔ zpowers t) :
    hS.rad.linHom ⟨y, hS.TH_le_normalizer_Q hy⟩ ∈ orthGroup ε := by
  have hR := hS.rad
  set N := normalizer (Q : Set G)
  set O : Subgroup G := ((orthGroup ε).comap hR.linHom).map N.subtype
  have hle : U ⊔ zpowers x₀ ⊔ zpowers t ≤ O := by
    refine sup_le (sup_le (fun x hx => ⟨⟨x, hR.P_le_normalizer (hR.U_le_P hx)⟩, ?_, rfl⟩)
      (zpowers_le.2 ⟨⟨x₀, hS.x₀_mem_normalizer_Q⟩, ?_, rfl⟩))
      (zpowers_le.2 ⟨⟨t, hS.t_mem_normalizer_Q⟩, ?_, rfl⟩)
    · exact ⟨hR.linHom_mem_linGroup _, fun v => hR.qfV_lin (hR.U_le_P hx) v⟩
    · refine ⟨hR.linHom_mem_linGroup _, fun v => ?_⟩
      change qfV ε (lin ψ x₀ v) = qfV ε v
      rw [(hR.lin_eq_iff hS.x₀_mem_normalizer_Q v _).2 (hS.inputs.outer.act v), qfV_refl_n0]
    · refine ⟨hR.linHom_mem_linGroup _, fun v => ?_⟩
      change qfV ε (lin ψ t v) = qfV ε v
      rw [(hR.lin_eq_iff hS.t_mem_normalizer_Q v v).2
        (by rw [← hS.commute_ψ v, mul_inv_cancel_right])]
  obtain ⟨y', hy', e⟩ := hle hy
  have : y' = ⟨y, hS.TH_le_normalizer_Q hy⟩ := Subtype.ext e
  rw [← this]
  exact hy'

variable {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀)
include hρ

theorem mem_TH_rho {y : G} (hy : y ∈ U ⊔ zpowers x₀ ⊔ zpowers t) :
    ∃ m ∈ U ⊔ zpowers ρ, y = m ∨ y = m * t := by
  have htN : t ∈ normalizer ((U ⊔ zpowers ρ : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun m hm => by
      rw [← hS.commute_of_mem_TH (hS.Urho_le_TH hρ hm), mul_inv_cancel_right]
      exact hm
  have hx₀ : x₀ ∈ U ⊔ zpowers ρ ⊔ zpowers t := by
    rcases hρ with rfl | rfl
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · have h1 : t * (t * x₀) ∈ U ⊔ zpowers (t * x₀) ⊔ zpowers t :=
        mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mem_sup_right (mem_zpowers _)))
      rwa [← mul_assoc, hS.shape.mul_self, one_mul] at h1
  have hle : U ⊔ zpowers x₀ ⊔ zpowers t ≤ U ⊔ zpowers ρ ⊔ zpowers t :=
    sup_le (sup_le (le_sup_left.trans le_sup_left) (zpowers_le.2 hx₀)) le_sup_right
  obtain ⟨m, hm, n, rfl⟩ := (Stage0.mem_sup_zpowers_iff htN).1 (hle hy)
  rcases hS.shape.mem_zpowers_iff.1 (zpow_mem (mem_zpowers t) n) with h | h <;> rw [h]
  · exact ⟨m, hm, Or.inl (mul_one m)⟩
  · exact ⟨m, hm, Or.inr rfl⟩

theorem exists_levi :
    ∃ X₂ : Subgroup G, X₂ ≤ U ⊔ zpowers ρ ∧ (∀ k ∈ X₂, k ∈ Q ⊔ zpowers t → k = 1) ∧
      ∀ y ∈ U ⊔ zpowers x₀ ⊔ zpowers t, ∃ q ∈ Q, ∃ k ∈ X₂, y = q * k ∨ y = q * k * t := by
  have hR := hS.rad
  obtain ⟨X, hXle, hXinf, hXonto⟩ := hS.inputs.levi
  have hXC : ∀ x ∈ X, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hXle hx)).1
  have htX : t ∈ normalizer (X : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    rw [← hXC x hx, mul_inv_cancel_right]
    exact hx
  have hXE : ∀ x ∈ X, x ∈ Q ⊔ zpowers t → x = 1 := fun x hx hxE => by
    have : x ∈ X ⊓ (Q ⊔ zpowers t) := Subgroup.mem_inf.2 ⟨hx, hxE⟩
    rw [hXinf] at this
    exact this
  have htE : t ∈ Q ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  refine ⟨(X ⊔ zpowers t) ⊓ (U ⊔ zpowers ρ), inf_le_right, ?_, ?_⟩
  · intro k hk hkE
    obtain ⟨hkX, hkU⟩ := Subgroup.mem_inf.1 hk
    obtain ⟨x, hx, n, rfl⟩ := (Stage0.mem_sup_zpowers_iff htX).1 hkX
    rcases hS.shape.mem_zpowers_iff.1 (zpow_mem (mem_zpowers t) n) with h | h <;>
      rw [h] at hkE hkU ⊢
    · rw [mul_one] at hkE ⊢
      exact hXE x hx hkE
    · have hxE : x ∈ Q ⊔ zpowers t := by
        have := mul_mem hkE (inv_mem htE)
        rwa [mul_inv_cancel_right] at this
      have hx1 := hXE x hx hxE
      rw [hx1, one_mul] at hkU
      exact absurd hkU (hS.t_not_mem_Urho hρ)
  · intro y hy
    obtain ⟨x, hx, hxl⟩ := hXonto _ (hS.lin_mem_orth hy)
    have hxN : x ∈ normalizer (Q : Set G) := (Subgroup.mem_inf.1 (hXle hx)).2
    have hyN := hS.TH_le_normalizer_Q hy
    have hyt := hS.commute_of_mem_TH hy
    have hz : x⁻¹ * y ∈ Q ⊔ zpowers t := by
      rw [← hS.shape.centralizer_eq]
      refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_iff.2 fun q hq => ?_⟩
      · have hxt := hXC x hx
        have hxt' : x⁻¹ * t = t * x⁻¹ := (Commute.inv_left hxt).eq
        rw [mul_assoc, hyt, ← mul_assoc, hxt', mul_assoc]
      · obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
        have h1 : lin ψ (x⁻¹ * y) v = v := by
          rw [hR.lin_mul (inv_mem hxN) hyN]
          have : lin ψ y v = lin ψ x v := (hxl v).symm
          rw [this, hR.lin_inv' hxN]
        have h2 := (hR.lin_eq_iff (mul_mem (inv_mem hxN) hyN) v v).1 h1
        calc ψ v * (x⁻¹ * y) = x⁻¹ * y * ψ v * (x⁻¹ * y)⁻¹ * (x⁻¹ * y) := by rw [h2]
          _ = x⁻¹ * y * ψ v := by group
    have hET : Q ⊔ zpowers t ≤ U ⊔ zpowers x₀ ⊔ zpowers t :=
      sup_le_sup_right (hR.Q_le_U.trans le_sup_left) _
    have hxT : x ∈ U ⊔ zpowers x₀ ⊔ zpowers t := by
      have := mul_mem hy (inv_mem (hET hz))
      rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    obtain ⟨q, hq, hqe | hqe⟩ := (hS.shape.mem_sup_iff hR.Q_le_L).1 hz
    all_goals
      have hy' : y = x * (x⁻¹ * y) := by group
      have hq' : x * q * x⁻¹ ∈ Q := (mem_normalizer_iff.1 hxN q).1 hq
      have hqt := hS.shape.commute_of_mem (hR.Q_le_L hq)
      obtain ⟨m, hm, hxm | hxm⟩ := hS.mem_TH_rho hρ hxT
    ·
      refine ⟨x * q * x⁻¹, hq', m, Subgroup.mem_inf.2 ⟨?_, hm⟩, Or.inl ?_⟩
      · rw [← hxm]; exact mem_sup_left hx
      · rw [hy', hqe, hxm]; group
    ·
      have hmX : m ∈ X ⊔ zpowers t := by
        have : m = x * t := by rw [hxm, mul_assoc, hS.shape.mul_self, mul_one]
        rw [this]; exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers t))
      refine ⟨x * q * x⁻¹, hq', m, Subgroup.mem_inf.2 ⟨hmX, hm⟩, Or.inr ?_⟩
      rw [hy', hqe, hxm]
      calc m * t * q = m * (q * t) := by rw [mul_assoc, ← hqt]
        _ = m * t * q * (m * t)⁻¹ * m * t := by rw [hqt]; group
    ·
      refine ⟨x * q * x⁻¹, hq', m, Subgroup.mem_inf.2 ⟨?_, hm⟩, Or.inr ?_⟩
      · rw [← hxm]; exact mem_sup_left hx
      · rw [hy', hqe, hxm]; group
    ·
      have hmX : m ∈ X ⊔ zpowers t := by
        have : m = x * t := by rw [hxm, mul_assoc, hS.shape.mul_self, mul_one]
        rw [this]; exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers t))
      refine ⟨x * q * x⁻¹, hq', m, Subgroup.mem_inf.2 ⟨hmX, hm⟩, Or.inl ?_⟩
      rw [hy', hqe, hxm]
      calc m * t * (q * t) = m * q := by
            rw [hqt, ← mul_assoc, mul_assoc m t t, hS.shape.mul_self, mul_one]
        _ = m * t * q * (m * t)⁻¹ * m := by
            rw [show m * t * q * (m * t)⁻¹ * m = m * (t * q) * t⁻¹ by group, ← hqt]; group

end CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX
