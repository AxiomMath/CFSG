module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLink

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G] {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G}

theorem exists_n3_of_premises [Finite G] {Q₃ P₃ : Subgroup G}
    {ψ₃ : V6 → G} {p₃ : Fin 6 → G} (hS₃ : Setup .plus t L U Q₃ P₃ a ψ₃ p₃) {W₃ : Subgroup G}
    (hW₃ : Premises t Q₃ W₃) {S : Set G} (hSQ : S ⊆ Q₃) (haU : ∀ x ∈ U, x * a * x⁻¹ = a) :
    ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a ∧
      ∀ y ∈ closure S, n * y = y * n := by
  have hR₃ := hS₃.rad
  have haQ : a ∈ Q₃ := hR₃.a_eq ▸ hR₃.ψ_mem _
  have hat : a * t = t * a := hS₃.shape.commute_of_mem (hR₃.Q_le_L haQ)
  obtain ⟨n, hn, hcm⟩ := hW₃.exists_cm_eq hS₃ haQ
  have hnt : n * t * n⁻¹ = t * a := by
    have : n * t * n⁻¹ = cm t n * t := by simp only [cm]; group
    rw [this, hcm, hat]
  refine ⟨n, mem_normalizer_of_conj_mem fun x hx => ?_, hnt, fun y hy => ?_⟩
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

theorem a_central
    (hS : Setup .plus t L U Q P a ψ p) (hu : UData .plus U Q ψ u) {x : G} (hx : x ∈ U) :
    x * a * x⁻¹ = a := by
  have hR := hS.rad
  obtain ⟨i, hi, hxi⟩ := hu.exists_s0 hR hx
  have h := e0Check_spec
  simp only [e0Check, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := mulVec_toVec (s0Get .plus i) 1
  rw [h i hi, show (1 : ℕ) = 2 ^ ((0 : Fin 6) : ℕ) from rfl, toVec_two_pow'] at h1
  rw [hR.a_eq]
  exact (hR.lin_eq_iff (hR.P_le_normalizer (hR.U_le_P hx)) _ _).1 (by rw [hxi]; exact h1)

theorem l9_of_link_plus [Finite G]
    (hS : Setup .plus t L U Q P a ψ p) (hu : UGens .plus U Q ψ u)
    (_hF : LinkFacts .plus L U Q P a ψ p u) (_hA : AutCent L Q)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥)
    (hNH : ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x * t = t * x →
      x ∈ U ⊔ zpowers t)
    (hn3 : ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a ∧
      ∀ y ∈ closure ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} :
        Set G), n * y = y * n) : L9 t Q := by
  intro W hQW htW hcard hcomm hnorm
  have hW : Premises t Q W := ⟨hQW, htW, hcard, hcomm, hnorm⟩
  rcases hW.sq_eq_one_or_inv hS (endF2 .plus) with h | hinv
  · exact h
  · exact (homocyclic_false_plus hS (uData_of_uGens hu) hU6 hn3 hNH hW hinv).elim

theorem l9_of_link_plus' [Finite G]
    (hS : Setup .plus t L U Q P a ψ p) (hu : UGens .plus U Q ψ u)
    (hF : LinkFacts .plus L U Q P a ψ p u) (hA : AutCent L Q)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥)
    (hNH : ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x * t = t * x →
      x ∈ U ⊔ zpowers t)
    (hQ₃ : ∃ (Q₃ P₃ : Subgroup G) (ψ₃ : V6 → G) (p₃ : Fin 6 → G) (W₃ : Subgroup G),
      Setup .plus t L U Q₃ P₃ a ψ₃ p₃ ∧ Q₃ ≤ W₃ ∧ t ∉ W₃ ∧ Nat.card W₃ = 4096 ∧
      (∀ x ∈ W₃, ∀ y ∈ W₃, x * y = y * x) ∧
      (∀ n ∈ normalizer ((Q₃ ⊔ zpowers t : Subgroup G) : Set G), ∀ w ∈ W₃, n * w * n⁻¹ ∈ W₃) ∧
      ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G) ⊆ Q₃) :
    L9 t Q := by
  obtain ⟨Q₃, P₃, ψ₃, p₃, W₃, hS₃, h1, h2, h3, h4, h5, hsub⟩ := hQ₃
  exact l9_of_link_plus hS hu hF hA hU6 hNH (exists_n3_of_premises hS₃ ⟨h1, h2, h3, h4, h5⟩
    hsub fun x hx => a_central hS (uData_of_uGens hu) hx)

end CFSG.EvenSmallLie.OmegaEight.Chain
