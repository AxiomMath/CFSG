module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Transport
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.Classical.SteinbergBY (symplectic_prime_semilinear_field_descent)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (mem_of_pow_eq_one_of_relIndex_dvd_two
  mem_of_pow_eq_one_of_index_dvd_two)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem exists_fixed_perfect_three_PSp_two_even {ℓ f : ℕ} (hℓ : ℓ = 2) (hf : 1 ≤ f) {F : Type}
    [Field F] (hF : Nat.card F = ℓ ^ f) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))) :
    ∃ D : Subgroup (StatedProj (StatedSp 2 F)), (∀ x ∈ D, β x = x) ∧ ⁅D, D⁆ = D ∧
      3 ∣ Nat.card D := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓp : ℓ.Prime := hℓ ▸ Nat.prime_two
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact (pow_pos hℓp.pos f).ne')
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent (r := 2) hℓp hf le_rfl hF
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hβE : β ∈ spSemilinearAutGroup 2 F :=
    mem_of_pow_eq_one_of_index_dvd_two hidx Nat.prime_three (by norm_num) hβ3
  by_cases hD : β ∈ spLinearAutGroup 2 F
  · exfalso
    have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp 2 F))
    exact hβout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)))
      (D := spLinearAutGroup 2 F)
      (hDH.trans (Nat.gcd_dvd_left 2 _)) Nat.prime_three (by norm_num) hD hβ3)
  obtain ⟨-, σ, hσord, hσcard, h, hh, hβh⟩ := hdesc 3 Nat.prime_three β hβE hD hβord
  have hfix : ∀ x : StatedProj (StatedSp 2 F), fieldAut 2 F σ x = x ↔
      x ∈ (subfieldSpProj 2 (descentField σ)).range := fun x =>
    fieldAut_apply_eq_self_iff (by omega) (by rw [hσord]; decide) x
  have hinj := subfieldSpProj_injective (K := F) (r := 2) (by omega) (descentField σ)
  have : Finite (descentField σ) := Subtype.finite
  let hh' : MulAut (StatedProj (StatedSp 2 F)) := h
  let D0 := (subfieldSpProj 2 (descentField σ)).range
  let D := D0.map hh'.toMonoidHom
  let eD : ↥D ≃* StatedProj (StatedSp 2 (descentField σ)) :=
    (D0.equivMapOfInjective hh'.toMonoidHom hh'.injective).symm.trans
      (MonoidHom.ofInjective hinj).symm
  have hDfix : ∀ x ∈ D, β x = x := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : fieldAut 2 F σ y = y := (hfix y).2 hy
    rw [hβh]
    show hh' (fieldAut 2 F σ (hh'.symm (hh' y))) = hh' y
    rw [hh'.symm_apply_apply, hy']
  by_cases hk2 : Nat.card (descentField σ) = 2
  ·
    have : Fintype (descentField σ) := Fintype.ofFinite _
    have hk2' : Fintype.card (descentField σ) = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk2
    have : CharP (descentField σ) 2 := charP_of_card_eq_prime hk2'
    obtain ⟨e6⟩ := nonempty_statedSp_two_mulEquiv_perm hk2'
    let e6' : ↥D ≃* Equiv.Perm (Fin 6) :=
      eD.trans ((MulEquiv.ofBijective (proj 2 (descentField σ))
        UnitaryHigher.proj_bijective_of_charTwo).symm.trans e6)
    obtain ⟨eA⟩ := nonempty_commutator_mulEquiv_alternating e6'
    have hA : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (α := Fin 6) (by simp)⟩
    refine ⟨⁅D, D⁆, fun x hx => hDfix x ?_, commutator_eq_self_of_equiv_perfect _ eA, ?_⟩
    · exact (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)) hx
    · rw [Nat.card_congr eA.toEquiv]
      have h3 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        have := two_mul_nat_card_alternatingGroup (α := Fin 6)
        rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at this
        have h6 : Nat.factorial 6 = 720 := by decide
        rw [h6] at this
        omega
      rw [h3]
      norm_num
  · have hnk : ¬ (2 = 2 ∧ Nat.card (descentField σ) = 2) := fun h => hk2 h.2
    have hperf : Group.IsPerfect (StatedProj (StatedSp 2 (descentField σ))) :=
      CFSG.LieType.SeitzGeneration.isPerfect_statedProj_statedSp_of_two_le (by omega) hnk
    refine ⟨D, hDfix, commutator_eq_self_of_equiv_perfect D eD, ?_⟩
    rw [Nat.card_congr eD.toEquiv]
    exact CFSG.Quasithin.three_dvd_card_psp (K := descentField σ) (by omega)

end CFSG.HardMathSupport.Malle.E27Lie
