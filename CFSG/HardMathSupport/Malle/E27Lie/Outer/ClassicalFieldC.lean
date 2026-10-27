module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Transport
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.Classical.SteinbergBY (symplectic_prime_semilinear_field_descent)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (mem_of_pow_eq_one_of_relIndex_dvd_two
  mem_of_pow_eq_one_of_index_dvd_two)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem exists_fixed_perfect_three_PSp {n : ℕ} (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {F : Type} [Field F] (hF : Nat.card F = ℓ ^ f)
    (β : MulAut (StatedProj (StatedSp n F))) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp n F))) :
    ∃ D : Subgroup (StatedProj (StatedSp n F)), (∀ x ∈ D, β x = x) ∧ ⁅D, D⁆ = D ∧
      3 ∣ Nat.card D := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent (r := n) hℓ hf (by omega) hF
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hβE : β ∈ spSemilinearAutGroup n F :=
    mem_of_pow_eq_one_of_index_dvd_two hidx Nat.prime_three (by norm_num) hβ3
  by_cases hD : β ∈ spLinearAutGroup n F
  · exfalso
    have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp n F))
    exact hβout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n F)))
      (D := spLinearAutGroup n F)
      (hDH.trans (Nat.gcd_dvd_left 2 _)) Nat.prime_three (by norm_num) hD hβ3)
  obtain ⟨-, σ, hσord, -, h, hh, hβh⟩ := hdesc 3 Nat.prime_three β hβE hD hβord
  have hfix : ∀ x : StatedProj (StatedSp n F), fieldAut n F σ x = x ↔
      x ∈ (subfieldSpProj n (descentField σ)).range := fun x =>
    fieldAut_apply_eq_self_iff (by omega) (by rw [hσord]; decide) x
  have hinj := subfieldSpProj_injective (K := F) (r := n) (by omega) (descentField σ)
  have : Finite (descentField σ) := Subtype.finite
  let hh' : MulAut (StatedProj (StatedSp n F)) := h
  let D0 := (subfieldSpProj n (descentField σ)).range
  let D := D0.map hh'.toMonoidHom
  have hnk : ¬ (n = 2 ∧ Nat.card (descentField σ) = 2) := fun h => by omega
  have hperf : Group.IsPerfect (StatedProj (StatedSp n (descentField σ))) :=
    CFSG.LieType.SeitzGeneration.isPerfect_statedProj_statedSp_of_two_le (by omega) hnk
  let eD : ↥D ≃* StatedProj (StatedSp n (descentField σ)) :=
    (D0.equivMapOfInjective hh'.toMonoidHom hh'.injective).symm.trans
      (MonoidHom.ofInjective hinj).symm
  refine ⟨D, ?_, commutator_eq_self_of_equiv_perfect D eD, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : fieldAut n F σ y = y := (hfix y).2 hy
    rw [hβh]
    show hh' (fieldAut n F σ (hh'.symm (hh' y))) = hh' y
    rw [hh'.symm_apply_apply, hy']
  · rw [Nat.card_congr eD.toEquiv]
    exact CFSG.Quasithin.three_dvd_card_psp (K := descentField σ) (by omega)

end CFSG.HardMathSupport.Malle.E27Lie
