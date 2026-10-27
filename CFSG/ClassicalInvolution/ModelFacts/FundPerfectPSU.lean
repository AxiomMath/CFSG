module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectStd

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan

theorem le_commutator_of_map_le {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    {R : Subgroup X} (h : R.map φ.toMonoidHom ≤ ⁅R.map φ.toMonoidHom, R.map φ.toMonoidHom⁆) :
    R ≤ ⁅R, R⁆ := by
  rw [← Subgroup.map_commutator] at h
  exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp h

section Rank

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem rankOne_psu_perfect (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    {n : ℕ} (hn : 2 ≤ n) {k : Fin (n / 2)} {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = 2 • weight n (lowIdx k))
    (hγ' : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k))) :
    rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
        rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ) ≤
      ⁅rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
          rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ),
        rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
          rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ)⁆ := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_map_rankOne hF hp2 hn hγ hγ' P hP
  have hperf := (hi.isClassicalSL2 hF hp2).isPerfect (by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
    exact h4)
  refine le_commutator_of_map_le (conjEquiv P hP) ?_
  have := fundPerfect_range_le_commutator hperf (Subgroup.subtype _)
  rwa [Subgroup.range_subtype] at this

end Rank

section Model

variable {p : ℕ} [hp : Fact p.Prime]

theorem fundPerfect_PSU (n e : ℕ) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p e)
    (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have hf : 1 ≤ e := hadm.2.1
  have hM := modelUniv_PSU (n := n) (p := p) (f := e) hf
  have hsc := fundamentalSingleClass .PSU n p e hp.out trivial hadm (by simp) (by simp)
  rw [hM] at hsc ⊢
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e hf
  obtain ⟨k, γ₀, h₀, hγ, hγ'⟩ := exists_longest_root_psu hp.out hadm
  have hmem : (Unitary.rootDatum hF n).rootGroup γ₀ ⊔ (Unitary.rootDatum hF n).rootGroup (-γ₀) ∈
      fundamentalSubgroups .PSU (Unitary.rootDatum hF n) :=
    ⟨1, γ₀, Or.inl h₀, (map_conj_one _).symm⟩
  have hperf0 := rankOne_psu_perfect (F := GaloisField p (2 * e)) (p := p) (f := e) hF hp2 h4
    (by have := hadm.2.2.1; omega) hγ hγ'
  intro R hR
  obtain ⟨g, rfl⟩ := hsc _ hmem R hR
  exact fundPerfect_map_conj_le_commutator hperf0 g

end Model

end CFSG.ClassicalInvolution.ModelFacts
