module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainStart

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem mem_of_relIndex_three [Finite G] {C H : Subgroup G}
    (hn : ∀ c ∈ C, ∀ h ∈ H, c * h * c⁻¹ ∈ H) (h3 : H.relIndex C = 3) {x y : G} (hx : x ∈ C)
    (hy : y ∈ C) (hxH : x ∉ H) (hyH : y ∉ H) (hxy : x⁻¹ * y ∉ H) : x⁻¹ * x⁻¹ * y ∈ H := by
  have hN : (H.subgroupOf C).Normal :=
    ⟨fun n hn' g => by
      rw [mem_subgroupOf] at hn' ⊢
      exact hn g g.2 n hn'⟩
  have hcard : Nat.card (C ⧸ H.subgroupOf C) = 3 := h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x' : C ⧸ H.subgroupOf C := ((⟨x, hx⟩ : C) : C ⧸ H.subgroupOf C)
  set y' : C ⧸ H.subgroupOf C := ((⟨y, hy⟩ : C) : C ⧸ H.subgroupOf C)
  have hx1 : x' ≠ 1 := fun h => hxH (by
    have := (QuotientGroup.eq_one_iff (N := H.subgroupOf C) (⟨x, hx⟩ : C)).1 h
    rwa [mem_subgroupOf] at this)
  have hy1 : y' ≠ 1 := fun h => hyH (by
    have := (QuotientGroup.eq_one_iff (N := H.subgroupOf C) (⟨y, hy⟩ : C)).1 h
    rwa [mem_subgroupOf] at this)
  have hxy' : x' ≠ y' := fun h => hxy (by
    have := QuotientGroup.eq.1 h
    rwa [mem_subgroupOf] at this)
  have hfin : Finite (C ⧸ H.subgroupOf C) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hx3 : x' ^ 3 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1
    ((zpowers_eq_top_of_prime_card hcard hx1).symm ▸ mem_top y' : y' ∈ zpowers x')
  have hk' : y' = x' ^ (k % 3) := by
    rw [← hk]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
      hx3, _root_.one_zpow, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hyx : y' = x' ^ 2 := by
    rcases hr with h | h | h
    · rw [h, zpow_zero] at hk'; exact absurd hk' hy1
    · rw [h, zpow_one] at hk'; exact absurd hk'.symm hxy'
    · rw [h] at hk'; rw [hk', zpow_two, sq]
  have := QuotientGroup.eq.1 (show ((⟨x, hx⟩ ^ 2 : C) : C ⧸ H.subgroupOf C) = y' by
    rw [hyx]; rfl)
  rw [mem_subgroupOf] at this
  simpa [sq, mul_assoc] using this

variable {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}

theorem exists_n3_sq [Finite G] {Q₃ P₃ : Subgroup G}
    {ψ₃ : V6 → G} {p₃ : Fin 6 → G} (hS₃ : Setup .plus t L U Q₃ P₃ a ψ₃ p₃) {W₃ : Subgroup G}
    (hW₃ : Premises t Q₃ W₃) {S : Set G} (hSQ : S ⊆ Q₃) (haU : ∀ x ∈ U, x * a * x⁻¹ = a) :
    ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a ∧
      n * n ∈ U ∧ ∀ y ∈ closure S, n * y = y * n := by
  have hR₃ := hS₃.rad
  have haQ : a ∈ Q₃ := hR₃.a_eq ▸ hR₃.ψ_mem _
  have hat : a * t = t * a := hS₃.shape.commute_of_mem (hR₃.Q_le_L haQ)
  obtain ⟨n, hn, hcm⟩ := hW₃.exists_cm_eq hS₃ haQ
  have hnt : n * t * n⁻¹ = t * a := by
    have : n * t * n⁻¹ = cm t n * t := by simp only [cm]; group
    rw [this, hcm, hat]
  refine ⟨n, mem_normalizer_of_conj_mem fun x hx => ?_, hnt,
    hR₃.Q_le_U (hW₃.mul_self_mem_Q hS₃ hn), fun y hy => ?_⟩
  · have hU : ∀ x ∈ U, n * x * n⁻¹ ∈ U := by
      intro x hx
      have hxP := hR₃.U_le_P hx
      have hxn := hW₃.P_conj_mem hS₃ hxP hn
      have h1 : cm t (x * n * x⁻¹) = a := by rw [cm_conj hS₃ hxP, hcm, haU x hx]
      have h2 : cm t (x * n * x⁻¹ * n⁻¹) = 1 := by
        rw [hW₃.cm_mul hxn (inv_mem hn), hW₃.cm_inv hn, h1, hcm, mul_inv_cancel]
      have h3 := (hW₃.cm_eq_one_iff hS₃ (mul_mem hxn (inv_mem hn))).1 h2
      have e : n * x * n⁻¹ = (x * n * x⁻¹ * n⁻¹)⁻¹ * x := by group
      rw [e]
      exact mul_mem (inv_mem (hR₃.Q_le_U h3)) hx
    obtain ⟨z, hz, hxz | hxz⟩ := (hS₃.shape.mem_sup_iff hR₃.U_le_L).1 hx
    · rw [hxz]
      exact mem_sup_left (hU z hz)
    · rw [hxz, show n * (z * t) * n⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) by group, hnt]
      exact mul_mem (mem_sup_left (hU z hz))
        (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hR₃.Q_le_U haQ)))
  · have hyQ : y ∈ Q₃ := (closure_le Q₃).2 hSQ hy
    exact hW₃.comm n hn y (hW₃.Q_le hyQ)

theorem exists_inner_of_inv {T : Subgroup G} (ha2 : a * a = 1)
    (hac : ∀ g ∈ T, g * a = a * g) {n x z : G}
    (hcomm : ∀ g ∈ T, n * g * n⁻¹ = g ∨ n * g * n⁻¹ = g * a)
    (hxN : ∀ g ∈ T, x * g * x⁻¹ ∈ T) (hxN' : ∀ g ∈ T, x⁻¹ * g * x ∈ T) (hxa : x * a * x⁻¹ = a)
    (hx3 : x ^ 3 ∈ T) (hz : z ∈ T) (hrel : n * x * n⁻¹ = x⁻¹ * z) :
    ∃ y₀ ∈ T, ∀ g ∈ T, x * g * x⁻¹ = y₀ * g * y₀⁻¹ ∨ x * g * x⁻¹ = y₀ * g * y₀⁻¹ * a := by
  have hxa' : x⁻¹ * a * x = a := by
    calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hxa]
      _ = a := by group
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hstar : ∀ g ∈ T, x * g * x⁻¹ = x⁻¹ * z * g * z⁻¹ * x ∨
      x * g * x⁻¹ = x⁻¹ * z * g * z⁻¹ * x * a := by
    intro g hg
    have e : n * (x * g * x⁻¹) * n⁻¹ =
        (n * x * n⁻¹) * (n * g * n⁻¹) * (n * x * n⁻¹)⁻¹ := by group
    rw [hrel] at e
    have hza : z * a * z⁻¹ = a := by rw [hac z hz, mul_inv_cancel_right]
    have e2 : x⁻¹ * z * (g * a) * (x⁻¹ * z)⁻¹ = x⁻¹ * z * g * z⁻¹ * x * a := by
      calc x⁻¹ * z * (g * a) * (x⁻¹ * z)⁻¹ =
          x⁻¹ * z * g * z⁻¹ * x * (x⁻¹ * (z * a * z⁻¹) * x) := by group
        _ = _ := by rw [hza, hxa']
    have e3 : x⁻¹ * z * g * (x⁻¹ * z)⁻¹ = x⁻¹ * z * g * z⁻¹ * x := by group
    rcases hcomm _ (hxN g hg) with h1 | h1 <;> rcases hcomm g hg with h2 | h2 <;>
      rw [h1, h2] at e
    · left; rw [e, e3]
    · right; rw [e, e2]
    · right
      have : x * g * x⁻¹ = x⁻¹ * z * g * (x⁻¹ * z)⁻¹ * a := by
        rw [← e, mul_assoc (x * g * x⁻¹), ha2, mul_one]
      rw [this, e3]
    · left
      have : x * g * x⁻¹ = x⁻¹ * z * (g * a) * (x⁻¹ * z)⁻¹ * a := by
        rw [← e, mul_assoc (x * g * x⁻¹), ha2, mul_one]
      rw [this, e2, mul_assoc (x⁻¹ * z * g * z⁻¹ * x), ha2, mul_one]
  refine ⟨x ^ 3 * z⁻¹, mul_mem hx3 (inv_mem hz), fun g hg => ?_⟩
  set g' := x⁻¹ * x⁻¹ * g * x * x with hg'
  have hg'T : g' ∈ T := by
    have := hxN' _ (hxN' g hg)
    rw [hg']
    convert this using 1
    group
  have e1 : x * (x * g' * x⁻¹) * x⁻¹ = g := by simp only [hg']; group
  have hx1 := hstar g' hg'T
  have hzc : ∀ w ∈ T, z * w * z⁻¹ ∈ T := fun w hw => mul_mem (mul_mem hz hw) (inv_mem hz)
  have hconj : x * g * x⁻¹ = x ^ 3 * g' * (x ^ 3)⁻¹ := by
    simp only [hg', pow_succ, pow_zero, one_mul]; group
  have hxg'T : x * g' * x⁻¹ ∈ T := hxN _ hg'T
  have hy0 : (x ^ 3 * z⁻¹) * g * (x ^ 3 * z⁻¹)⁻¹ = x ^ 3 * (z⁻¹ * g * z) * (x ^ 3)⁻¹ := by group
  have hg2 : g = z * g' * z⁻¹ ∨ g = z * g' * z⁻¹ * a := by
    rcases hx1 with h | h
    · left
      calc g = x * (x * g' * x⁻¹) * x⁻¹ := e1.symm
        _ = x * (x⁻¹ * z * g' * z⁻¹ * x) * x⁻¹ := by rw [h]
        _ = z * g' * z⁻¹ := by group
    · right
      calc g = x * (x * g' * x⁻¹) * x⁻¹ := e1.symm
        _ = x * (x⁻¹ * z * g' * z⁻¹ * x * a) * x⁻¹ := by rw [h]
        _ = z * g' * z⁻¹ * (x * a * x⁻¹) := by group
        _ = z * g' * z⁻¹ * a := by rw [hxa]
  have hx3a : x ^ 3 * a * (x ^ 3)⁻¹ = a := by rw [hac _ hx3, mul_inv_cancel_right]
  rcases hg2 with h | h
  · left
    rw [hconj, hy0]
    congr 2
    rw [h]; group
  · right
    rw [hconj, hy0]
    have : g' = z⁻¹ * g * z * a := by
      rw [h]
      calc g' = g' * (a * a) := by rw [ha2, mul_one]
        _ = z⁻¹ * (z * g' * z⁻¹ * a) * z * a := by
          rw [show z⁻¹ * (z * g' * z⁻¹ * a) * z = g' * (z⁻¹ * a * z) by group,
            show z⁻¹ * a * z = a by rw [mul_assoc, ← hac z hz, inv_mul_cancel_left]]
          group
    rw [this]
    calc x ^ 3 * (z⁻¹ * g * z * a) * (x ^ 3)⁻¹ =
        x ^ 3 * (z⁻¹ * g * z) * (x ^ 3)⁻¹ * (x ^ 3 * a * (x ^ 3)⁻¹) := by group
      _ = _ := by rw [hx3a]

theorem mem_sup_zpowers_of_le (hK : Stage0.StepK t L) {X : Subgroup G} (hXL : X ≤ L) {z : G}
    (hz : z ∈ X ⊔ zpowers t) : ∃ y ∈ X, z = y ∨ z = y * t := by
  obtain ⟨y, hy, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun y hy c hc => by
      rcases hK.mem_zpowers_iff.1 hc with rfl | rfl
      · rw [mul_one, one_mul]
      · exact hK.commute_of_mem (hXL hy)) hz
  rcases hK.mem_zpowers_iff.1 hc with rfl | rfl
  · exact ⟨y, hy, Or.inl (mul_one y)⟩
  · exact ⟨y, hy, Or.inr rfl⟩

theorem mem_TH_of_mem_K [Finite G] (hK : Stage0.StepK t L) (hUL : U ≤ L)
    (hNL : ∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U) {x : G} (hxK : x ∈ L ⊔ zpowers t)
    (hxN : x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G)) : x ∈ U ⊔ zpowers t := by
  have hsup : ∀ z ∈ (U ⊔ zpowers t : Subgroup G), z ∈ L → z ∈ U := by
    intro z hz hzL
    obtain ⟨y, hy, rfl | rfl⟩ := mem_sup_zpowers_of_le hK hUL hz
    · exact hy
    · exfalso
      apply hK.not_mem
      have := mul_mem (inv_mem (hUL hy)) hzL
      rwa [inv_mul_cancel_left] at this
  have htN : t ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
    le_normalizer (mem_sup_right (mem_zpowers t))
  obtain ⟨l, hl, hxl⟩ := hK.mem_sup_iff.1 hxK
  have hlN : l ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) := by
    rcases hxl with rfl | rfl
    · exact hxN
    · have := mul_mem hxN (inv_mem htN)
      rwa [mul_inv_cancel_right] at this
  have hlU : l ∈ normalizer (U : Set G) :=
    mem_normalizer_of_conj_mem fun y hy =>
      hsup _ ((mem_normalizer_iff.1 hlN y).1 (mem_sup_left hy))
        (mul_mem (mul_mem hl (hUL hy)) (inv_mem hl))
  have hlU' := hNL l hl hlU
  rcases hxl with rfl | rfl
  · exact mem_sup_left hlU'
  · exact mul_mem (mem_sup_left hlU') (mem_sup_right (mem_zpowers t))

end CFSG.EvenSmallLie.OmegaEight.Chain
