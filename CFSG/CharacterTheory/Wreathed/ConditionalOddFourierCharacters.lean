module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalOddFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G] {basis : FiniteIrreducibleCharacterBasis G}
  {principal : basis.index}

theorem two_le_basisDegree [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hprincipal : (basis.representation principal).character = 1) {ψ : basis.index}
    (hψ : ψ ≠ principal) : 2 ≤ basisDegree basis ψ := by
  have hpos := basisDegree_pos basis ψ
  rw [basisDegree] at hpos ⊢
  by_contra hlt
  have hdeg : Module.finrank ℂ (basis.representation ψ).vector = 1 := by omega
  apply hψ
  set ρ := (basis.representation ψ).representation
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    intro a b
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdeg (ρ a)
    obtain ⟨c', hc', -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdeg (ρ b)
    rw [hc, hc']
    ext v
    simp [smul_smul, mul_comm]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker ρ) with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply (MonoidHom.ker_eq_bot_iff ρ).mp hbot
    rw [map_mul, map_mul, hcomm]
  · apply basis.distinct
    change (basis.representation ψ).character = (basis.representation principal).character
    rw [hprincipal]
    ext g
    have hg : g ∈ MonoidHom.ker ρ := by
      rw [htop]
      trivial
    rw [MonoidHom.mem_ker] at hg
    change LinearMap.trace ℂ _ (ρ g) = 1
    rw [hg, LinearMap.trace_one, hdeg, Nat.cast_one]

theorem basisCombination_eq_fun (B : Finset basis.index) (e : basis.index → ℤ) :
    basisCombination basis B e =
      fun g => ∑ ψ ∈ B, (e ψ : ℂ) * (basis.representation ψ).character g := by
  funext g
  rw [basisCombination_apply, Finset.sum_apply]
  rfl

theorem basisCombination_principal_add_sum
    (hprincipal : (basis.representation principal).character = 1) {B : Finset basis.index}
    (hp : principal ∈ B) {α : Fin 3 → basis.index} (hα : ∀ i, α i ∈ B) (β : Fin 3 → ℤ) :
    basisCombination basis B (unitVector principal + ∑ i, β i • unitVector (α i)) =
      1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character := by
  have hαc : ∀ i, basisCombination basis B (unitVector (α i)) =
      (basis.representation (α i)).character := fun i => basisCombination_unitVector B (hα i)
  rw [map_add, map_sum, basisCombination_unitVector B hp, hprincipal]
  simp only [map_zsmul, hαc, ← Int.cast_smul_eq_zsmul ℂ]

theorem basisCombination_neg_principal_add_sum_add
    (hprincipal : (basis.representation principal).character = 1) {B : Finset basis.index}
    (hp : principal ∈ B) {α : Fin 3 → basis.index} (hα : ∀ i, α i ∈ B) {r : basis.index}
    (hr : r ∈ B) (η : Fin 3 → ℤ) (b : ℤ) :
    basisCombination basis B (-unitVector principal + ∑ i, η i • unitVector (α i) +
        b • unitVector r) =
      -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
        (b : ℂ) • (basis.representation r).character := by
  have hαc : ∀ i, basisCombination basis B (unitVector (α i)) =
      (basis.representation (α i)).character := fun i => basisCombination_unitVector B (hα i)
  rw [map_add, map_add, map_neg, map_sum, map_zsmul, basisCombination_unitVector B hp,
    basisCombination_unitVector B hr, hprincipal]
  simp only [map_zsmul, hαc, ← Int.cast_smul_eq_zsmul ℂ]

end CFSG.Wreathed.ConditionalOddFourier
