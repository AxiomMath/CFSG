module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusPlane
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r : ℕ}

theorem tailTorus_comm (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (x y : ↥(tailTorus r (minusTailForm K b c))) : x * y = y * x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    finite_orthLinearEquiv
  have hodd : Odd (Nat.card (tailTorus r (minusTailForm K b c))) := by
    have := orthogonal_geometry_tail_small_anisotropic_Levi_p_prime (p := 2) hr hani hreg
      (Or.inr finrank_fin_two_fun)
    exact Nat.odd_iff.2 (by omega)
  have key : ∀ z : ↥(tailTorus r (minusTailForm K b c)), ∃ (t : Fin r → Kˣ)
      (h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)), IsOmegaTwisted b c h 0 ∧
        h ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) ∧
        tailDiag r t h = (z : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) := by
    intro z
    obtain ⟨-, t, h, hh, hz⟩ := mem_tailTorus.1 z.2
    refine ⟨t, h, ?_, hh, hz⟩
    have hpow : tailDiag r (t ^ Nat.card (tailTorus r (minusTailForm K b c)))
        (h ^ Nat.card (tailTorus r (minusTailForm K b c))) = 1 := by
      rw [← tailDiag_pow, hz, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
    refine plane_isOmegaTwisted_zero hirr hodd h 1 (fun a => by
        have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hh a
        rw [one_mul]
        exact this) (s := 1) (fun a => ?_)
    have h1 := LinearEquiv.congr_fun hpow ((0 : Fin r ⊕ Fin r → K), a)
    rw [tailDiag_apply] at h1
    have h2 := congrArg Prod.snd h1
    rw [one_smul]
    simpa using h2
  obtain ⟨t₁, h₁, p₁, -, hx⟩ := key x
  obtain ⟨t₂, h₂, p₂, -, hy⟩ := key y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, tailDiag_mul, tailDiag_mul, mul_comm t₁ t₂,
    commute_of_isOmegaTwisted_zero p₁ p₂]

theorem commutator_mem_tailUnipotent (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    {b₁ b₂ : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (h₁ : b₁ ∈ tailBorel r (minusTailForm K b c)) (h₂ : b₂ ∈ tailBorel r (minusTailForm K b c)) :
    ⁅b₁, b₂⁆ ∈ tailUnipotent r (minusTailForm K b c) := by
  classical
  have hani := anisotropic_minusTailForm hirr
  haveI := tailUnipotent_normal hani (r := r) (qA := minusTailForm K b c)
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := r) (qA := minusTailForm K b c)
  have hcomm : ∀ x y : ↥(tailBorel r (minusTailForm K b c)) ⧸
      (tailUnipotent r (minusTailForm K b c)).subgroupOf (tailBorel r (minusTailForm K b c)),
      x * y = y * x := fun x y =>
    e.injective (by rw [map_mul, map_mul]; exact tailTorus_comm hr hirr _ _)
  have h1 : (QuotientGroup.mk' ((tailUnipotent r (minusTailForm K b c)).subgroupOf
      (tailBorel r (minusTailForm K b c)))) ⁅(⟨b₁, h₁⟩ : ↥(tailBorel r (minusTailForm K b c))),
        ⟨b₂, h₂⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
