module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Four
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAlternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed
  CFSG.LocalAnalysis.EvenBN.GMSK

variable {Y : Type} [Group Y] {τ : Y}

private abbrev rhoZero : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * (Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5)

private theorem rhoZero_mem : rhoZero ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private theorem rhoZero_comm : rhoZero * Equiv.swap 0 1 = Equiv.swap 0 1 * rhoZero := by decide

private theorem rhoZero_orderOf : orderOf rhoZero = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (x := rhoZero) (p := 2) (n := 1) (by decide) (by decide)
  norm_num at h
  exact h

theorem exists_even_comm_swap_orderOf_four {a b : Fin 7} (hab : a ≠ b) :
    ∃ ρ : Equiv.Perm (Fin 7), ρ ∈ alternatingGroup (Fin 7) ∧
      ρ * Equiv.swap a b = Equiv.swap a b * ρ ∧ orderOf ρ = 4 := by
  set π : Equiv.Perm (Fin 7) := Equiv.swap 0 a * Equiv.swap 1 (Equiv.swap 0 a b) with hπ
  have hc : Equiv.swap (0 : Fin 7) a b ≠ 0 := by
    intro h0
    have h1 : b = a := by
      have := congrArg (Equiv.swap (0 : Fin 7) a) h0
      simpa [Equiv.swap_apply_self] using this
    exact hab h1.symm
  have hπ0 : π 0 = a := by
    rw [hπ]
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 7) ≠ 1) hc.symm,
      Equiv.swap_apply_left]
  have hπ1 : π 1 = b := by
    rw [hπ]
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
  have hswap : Equiv.swap a b = π * Equiv.swap 0 1 * π⁻¹ := by
    rw [← Equiv.swap_apply_apply π 0 1, hπ0, hπ1]
  refine ⟨π * rhoZero * π⁻¹, alternatingGroup.normal.conj_mem rhoZero rhoZero_mem π, ?_, ?_⟩
  · rw [hswap]
    calc (π * rhoZero * π⁻¹) * (π * Equiv.swap 0 1 * π⁻¹)
        = π * (rhoZero * Equiv.swap 0 1) * π⁻¹ := by group
      _ = π * (Equiv.swap 0 1 * rhoZero) * π⁻¹ := by rw [rhoZero_comm]
      _ = (π * Equiv.swap 0 1 * π⁻¹) * (π * rhoZero * π⁻¹) := by group
  · have hord := SemiconjBy.orderOf_eq π
      (show π * rhoZero = (π * rhoZero * π⁻¹) * π by group)
    rw [← hord, rhoZero_orderOf]

theorem z2a5_not_A7 [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    ¬ Nonempty (↥S ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨η⟩
  haveI := hS.normal
  obtain ⟨k, _, _, d⟩ := z2a5_datum h hS
  obtain ⟨-, -, -, σ, hσ, -, ⟨a, b, hab, hσab⟩, -, -⟩ :=
    alternating_involution_normal_even_SL2_fixed_support_rankOne_selector
      (n := 2) (m := 7) (by decide) k (by rw [Nat.card_eq_fintype_card, d.card_eq]) (by decide)
      (by decide) η (MulAut.conjNormal τ) d.orderOf_eq
      ((oTwoRes (centralizer ({τ} : Set Y))).subgroupOf S) d.le_fixed d.normal
      d.nonempty_mulEquiv.some d.rankOne
  obtain ⟨ρ, hρA, hρcomm, hρ4⟩ := exists_even_comm_swap_orderOf_four hab
  have hρσ : ρ * σ = σ * ρ := by rw [hσab]; exact hρcomm
  let g : alternatingGroup (Fin 7) := ⟨ρ, hρA⟩
  have hg : (g : Equiv.Perm (Fin 7)) = ρ := rfl
  refine z2a5_eqLocus_no_four h (η.symm g) ?_ ?_
  · change MulAut.conjNormal τ (η.symm g) = η.symm g
    apply η.injective
    apply Subtype.ext
    have h1 := hσ g
    rw [h1, MulEquiv.apply_symm_apply, hg, ← hρσ]
    group
  · rw [MulEquiv.orderOf_eq]
    change orderOf (⟨ρ, hρA⟩ : alternatingGroup (Fin 7)) = 4
    rw [Subgroup.orderOf_mk, hρ4]

end CFSG.OddStandard.SmallF3.Omega
