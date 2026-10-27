module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {C : Type} [Group C] [Finite C]

theorem exists_diag_piece {B : Subgroup C} (hB : IsPComponent 2 B) {t : C} (ht : t * t = 1)
    (hne : B.map (MulAut.conj t).toMonoidHom ≠ B) {u : C} (huB : u ∈ B) {w : C}
    (hw : w = u * (t * u * t⁻¹)) (hwc : ∀ c : C, c * w = w * c) (hw2 : w * w = 1) :
    ∃ Δ : Subgroup C, Δ ≤ centralizer ({t} : Set C) ∧
      IsPComponent 2 (Δ.subgroupOf (centralizer ({t} : Set C))) ∧ w ∈ Δ := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set B' : Subgroup C := B.map (MulAut.conj t).toMonoidHom with hB'
  have hB'pc : IsPComponent 2 B' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj t) hB
  have hK₁c : IsComponent (B.map π) := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hB
    exact hKeq ▸ hK
  set g : C ⧸ pPrimeCore 2 C := π t with hg
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, ht, map_one]
  have hKK' : (B.map π).map (MulAut.conj g).toMonoidHom = B'.map π := by
    rw [Subgroup.map_map, hB', Subgroup.map_map]
    congr 1
  have hne' : (B.map π).map (MulAut.conj g).toMonoidHom ≠ B.map π := by
    rw [hKK']
    intro h
    exact hne (eq_of_map_pPrimeCore_eq hB'pc hB h)
  obtain ⟨D, δ, hDq, hDC, hDs, hDl, hδsur, hδv⟩ := diag_isComponent hK₁c hg2 hne'
  have hDmem : ∀ v ∈ B.map π, v * (g * v * g⁻¹) ∈ D := fun v hv => by
    have h1 := (δ ⟨v, hv⟩).2
    rw [hδv ⟨v, hv⟩] at h1
    exact h1
  obtain ⟨Δ, hΔC, hΔpc, hΔmap, -⟩ := exists_isPComponent_lift ht hDq hDC hDs
  refine ⟨Δ, hΔC, hΔpc, ?_⟩
  have hπw : π w ∈ D := by
    have h1 : π w = π u * (g * π u * g⁻¹) := by
      rw [hw, map_mul, map_mul, map_mul, map_inv]
    rw [h1]
    exact hDmem _ (Subgroup.mem_map_of_mem π huB)
  have hπw' : π w ∈ Δ.map π := by
    rw [hΔmap]
    exact hπw
  obtain ⟨d, hd, hdw⟩ := hπw'
  set ε : C := w⁻¹ * d with hε
  have hεO : ε ∈ pPrimeCore 2 C := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 C), MonoidHom.mem_ker, hε, map_mul, map_inv, hdw,
      inv_mul_cancel]
  have hεodd : Odd (orderOf ε) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.1 pPrimeCore_coprime_card)
      (Subgroup.orderOf_dvd_natCard _ hεO)
  have hd' : d = w * ε := by
    rw [hε]
    group
  have hcomm : Commute w ε := (hwc ε).symm
  have hw2' : w ^ 2 = 1 := by
    rw [sq]
    exact hw2
  obtain ⟨j, hj⟩ := hεodd
  have hdpow : d ^ (orderOf ε) = w := by
    rw [hd', hcomm.mul_pow, pow_orderOf_eq_one, mul_one, hj, pow_succ, pow_mul, hw2', one_pow,
      one_mul]
  rw [← hdpow]
  exact Δ.pow_mem hd _

end CFSG.OddStandard.Solomon75
