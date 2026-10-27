module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cent

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_perfect_subgroup_of_cover {E : Type} [Group E] [Finite E] {R : Subgroup E}
    [R.Normal] (hR : Odd (Nat.card R)) (hcov : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ ⊔ R = ⊤)
    {x : E} (hx : ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    ∃ P : Subgroup E, ⁅P, P⁆ = P ∧ x ∈ P := by
  obtain ⟨k, hk⟩ := hx
  have hsup : ∀ (A : Subgroup E) [A.Normal], ⁅A ⊔ R, A ⊔ R⁆ ≤ ⁅A, A⁆ ⊔ R := by
    intro A _
    rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
      Subgroup.commutator_sup_left]
    exact sup_le (sup_le le_sup_left (le_sup_of_le_right (Subgroup.commutator_le_right A R)))
      (sup_le (le_sup_of_le_right (Subgroup.commutator_le_left R A))
        (le_sup_of_le_right (Subgroup.commutator_le_left R R)))
  have key : ∀ n : ℕ, ∀ H : Subgroup E, H.Normal → Nat.card H = n → x ∈ H →
      H ≤ ⁅H, H⁆ ⊔ R → ∃ P : Subgroup E, ⁅P, P⁆ = P ∧ x ∈ P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H hH hn hxH hHcov
      by_cases hperf : ⁅H, H⁆ = H
      · exact ⟨H, hperf, hxH⟩
      · have hle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_left H H
        have hlt : Nat.card (⁅H, H⁆ : Subgroup E) < n := by
          rw [← hn]
          exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hperf)
        have hxH' : x ∈ ⁅H, H⁆ := by
          obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hHcov hxH)
          let π := QuotientGroup.mk' (⁅H, H⁆ : Subgroup E)
          have hker : ∀ g : E, π g = 1 ↔ g ∈ ⁅H, H⁆ := fun g => by
            rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          have h1 : π x = π z := by
            rw [← hyz, map_mul, (hker y).mpr hy, one_mul]
          have h2 : orderOf (π x) ∣ 2 ^ k :=
            orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
          have h3 : orderOf (π x) ∣ Nat.card R := by
            rw [h1]
            exact (orderOf_map_dvd π z).trans (Subgroup.orderOf_dvd_natCard R hz)
          have h4 : orderOf (π x) = 1 := by
            have hodd : Odd (orderOf (π x)) := Odd.of_dvd_nat hR h3
            exact Nat.Coprime.eq_one_of_dvd
              (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) h2
          exact (hker x).mp (orderOf_eq_one_iff.mp h4)
        have hcov' : ⁅H, H⁆ ≤ ⁅⁅H, H⁆, ⁅H, H⁆⁆ ⊔ R :=
          (Subgroup.commutator_mono hHcov hHcov).trans (hsup ⁅H, H⁆)
        exact ih _ (hn ▸ hlt) ⁅H, H⁆ inferInstance rfl hxH' hcov'
  exact key _ ⊤ inferInstance rfl (Subgroup.mem_top x) hcov.ge

theorem commutator_top_sup_pPrimeCore {Q : Type} [Group Q] (hq : IsTwoGenQuasi Q) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ⊔ pPrimeCore 2 Q = ⊤ := by
  let π : Q →* Q ⧸ pPrimeCore 2 Q := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hperf : ⁅(⊤ : Subgroup (Q ⧸ pPrimeCore 2 Q)), (⊤ : Subgroup (Q ⧸ pPrimeCore 2 Q))⁆ = ⊤ := by
    have := hq.2.1.1
    rwa [_root_.commutator_def] at this
  rw [eq_top_iff]
  intro x _
  have h1 : π x ∈ (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆).map π := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, hperf]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcx⟩ := h1
  have ho : c⁻¹ * x ∈ pPrimeCore 2 Q := (QuotientGroup.eq (a := c) (b := x)).1 hcx
  have hx : x = c * (c⁻¹ * x) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup hc ho

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.map_le_altFix_of_perfect {C : CoverSetup n K} {α : MulAut K} {k : ℕ}
    {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk)) {P : Subgroup K}
    (hPF : P ≤ fixSub α) (hPperf : ⁅P, P⁆ = P)
    (hPY : ∀ p ∈ P, ∀ y ∈ fixSub α,
      C.ρ y ∈ invSwapGrp (stdInv n k hk) stdInv_mul_self → p * y = y * p) :
    P.map C.ρ ≤ altFix n k hk := by
  have hσ' : ∀ g ∈ P.map C.ρ, g * stdInv n k hk = stdInv n k hk * g := by
    rintro g ⟨p, hp, rfl⟩
    exact h.ρ_comm_of_mem_fixSub (hPF hp)
  have hδ : ∀ g ∈ P.map C.ρ, ∀ i l : Fin k, i ≠ l →
      g * dblPair n k hk i l = dblPair n k hk i l * g := by
    rintro g ⟨p, hp, rfl⟩ i l hil
    obtain ⟨x, hxX, hxρ⟩ := h.exists_dblPair_mem_fixSub i l hil
    have hc := hPY p hp x hxX (by rw [hxρ]; exact dblPair_mem_invSwapGrp i l)
    have := congrArg C.ρ hc
    simp only [map_mul] at this
    rw [hxρ] at this
    exact this
  have hPperf' : ⁅P.map C.ρ, P.map C.ρ⁆ = P.map C.ρ := by
    rw [← Subgroup.map_commutator, hPperf]
  by_cases hk3 : 3 ≤ k
  · exact perfect_le_altFix_of_preserves hPperf' (fun g hg i j =>
      preserves_pairs_of_comm_dbl hk3 (hσ' g hg) (hδ g hg) i j)
  · exact perfect_le_altFix_of_small (by omega) hPperf' hσ'

theorem CoverSetup.Induces.false_of_perfect {C : CoverSetup n K} {α : MulAut K} {k : ℕ}
    {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk)) {P : Subgroup K}
    (hPF : P ≤ fixSub α) (hPperf : ⁅P, P⁆ = P)
    (hPY : ∀ p ∈ P, ∀ y ∈ fixSub α,
      C.ρ y ∈ invSwapGrp (stdInv n k hk) stdInv_mul_self → p * y = y * p)
    {x : K} (hxP : x ∈ P) (hxρ : C.ρ x = stdInv n k hk) (hk1 : 1 ≤ k) : False := by
  have hmem : stdInv n k hk ∈ P.map C.ρ := ⟨x, hxP, hxρ⟩
  have hfix := (h.map_le_altFix_of_perfect hPF hPperf hPY hmem).1
  let p : Fin k × Fin 2 := (⟨0, by omega⟩, 0)
  have hne : stdInv n k hk (pairEmb n k hk p) ≠ pairEmb n k hk p := by
    rw [stdInv_apply_pair]
    intro heq
    have := (pairEmb n k hk).injective heq
    simp [p] at this
  exact hne (hfix _ ((stdInv_ne_self_iff _).1 hne))

end AhatData

end CFSG.OddStandard.Solomon75
