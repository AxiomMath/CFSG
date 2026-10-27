module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Basic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Even
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.PGlue
public import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.Sec66T (fixSub fixSubEquiv congr_self_eq)
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)

theorem threeTwoWitness_primeFormP_three {ℓ e : ℕ} {k : Type} [Field k] [Finite k]
    (h : UnitaryFieldData ℓ e k) (hq : ℓ ^ e % 3 = 1) :
    ThreeTwoWitness (primeFormP h ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
  have hW : ThreeTwoWitness (StatedProj (StatedSU 3 (ℓ ^ e) k)) := by
    have hcard : Nat.card k = (ℓ ^ e) ^ 2 := by rw [h.card, pow_mul']
    by_cases h2 : ℓ = 2
    · subst h2
      refine threeTwoWitness_psu_three_two_pow_even (f := e) hcard ?_
      rcases Nat.even_or_odd e with he | ho
      · exact he
      · exfalso
        have : 2 ^ e % 3 = 2 := by
          obtain ⟨m, rfl⟩ := ho
          rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        omega
    · have hqo : Odd (ℓ ^ e) := (h.prime.odd_of_ne_two h2).pow
      exact threeTwoWitness_psu_three_odd (pow_pos h.prime.pos e).ne' hqo
        (neg_one_ne_one_of_card h.prime h2 (m := 2 * e) (by rw [h.card]))
  have hq3 : ¬(3 = 3 ∧ ℓ ^ e = 2) := fun hh => by omega
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.isPrimeFormGram_idGL le_rfl hq3
  exact hW.of_mulEquiv ((unitaryPSUEquiv h (by norm_num)).symm.trans eT.symm)

theorem outerFixedWitness_psu_three {X : Type} [Group X] {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f % 3 = 1)
    (e : X ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    OuterFixedWitness X := by
  have hfin : Finite K := h.finite
  refine OuterFixedWitness.of_mulEquiv e ?_
  intro β hβ3 hβi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpℓ : (3 : ℕ) ≠ ℓ := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    omega
  have hZ : ¬ 3 ∣ Nat.gcd 3 (ℓ ^ f + 1) := by
    intro hd
    have := hd.trans (Nat.gcd_dvd_right _ _)
    omega
  have hβ1 : β ≠ 1 := fun h1 => hβi (h1 ▸ (CFSG.RankThree.PartOne.Sec66T.innerAut _).one_mem)
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  have hC1 : IsPrimeFormGram (1 : GL (Fin 3) K) :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.isPrimeFormGram_idGL
  set σ := primeFormFieldFactor h hC1 hn hne β with hσdef
  have hσp : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne]
      exact hσ1
    exact hβi (CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn hne
      Nat.prime_three hZ hD hβ3)
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne
      Nat.prime_three hp2 hpℓ β hord σ hσdef.symm hσord
  have hZ' : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)]
    exact hZ
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package h Nat.prime_three hp2 hσord 3 hn hne hZ'
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three hp2 hσord with hh₀
  have hfin₀ : Finite (fixSubfield σ) := inferInstance
  have hq₀ : ℓ ^ (f / 3) % 3 = 1 := by
    obtain ⟨m, hm⟩ := hpf
    have hdiv : f / 3 = m := by omega
    have h1 : (ℓ ^ m) ^ 3 = ℓ ^ f := by rw [← pow_mul, hm, mul_comm]
    rw [hdiv]
    have h2 : (ℓ ^ m) ^ 3 % 3 = (ℓ ^ m % 3) ^ 3 % 3 := Nat.pow_mod _ _ _
    rw [h1, hq] at h2
    have h3 : ℓ ^ m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize ℓ ^ m % 3 = a at h2 h3 ⊢
    interval_cases a <;> omega
  have hW := threeTwoWitness_primeFormP_three h₀ hq₀
  let ι : primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ))
      →* ↥(fixSub (primeFormFieldHom h hC1 σ)) :=
    (primeSubfieldPSU h Nat.prime_three hp2 hσord 3).codRestrict _ (fun x => by
      have hx : primeSubfieldPSU h Nat.prime_three hp2 hσord 3 x ∈
          (primeSubfieldPSU h Nat.prime_three hp2 hσord 3).range := ⟨x, rfl⟩
      rw [hrange] at hx
      exact hx)
  have hιinj : Function.Injective ι := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hWf : ThreeTwoWitness ↥(fixSub (primeFormFieldHom h hC1 σ)) := hW.of_injective ι hιinj
  set u := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M with hu
  set fσ := primeFormFieldHom h hC1 σ with hfσ
  have hβu : β = u * fσ * u⁻¹ := by
    have : u⁻¹ * β * u = fσ := hM
    rw [← this]
    group
  have hcongr : MulAut.congr u fσ = β := (congr_self_eq u fσ).trans hβu.symm
  let e1 : ↥(fixSub fσ) ≃* ↥(fixSub β) :=
    (fixSubEquiv u fσ).trans (MulEquiv.subgroupCongr (congrArg fixSub hcongr))
  exact hWf.of_mulEquiv e1

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
