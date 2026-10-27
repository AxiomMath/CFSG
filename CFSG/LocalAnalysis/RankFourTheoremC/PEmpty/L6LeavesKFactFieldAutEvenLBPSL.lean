module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

theorem card_fixed_PSL_three {K : Type} [Group K] [Finite K] {n ℓ f : ℕ} (hn : 3 ≤ n)
    (hcl : StatedClassicalModel K .PSL n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .PSL n (ℓ ^ f₀) =
        Nat.gcd n (ℓ ^ f₀ - 1) * Nat.card (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  have : CharP F ℓ := charP_of_card_eq_prime_pow hFcard'
  have hdiv' : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := by rw [hFcard]; exact hdiv
  let θ : K ≃* projectiveSL n F := e.trans (statedProjSLEquiv n F)
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n F) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  rw [← card_fixedSubgroup_congr θ α]
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ semilinearAutGroup n F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow hn
      (hp.odd_of_ne_two hp2) hβp
  by_cases hD : β ∈ linearAutGroup n F
  · exfalso
    exact hβout (CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiv' β hD 1
      (by
        rw [pow_one, hβp]
        exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem))
  obtain ⟨hpf, σ, hσord, ⟨h, hh, hβh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf hn hFcard hp β hβE hD hβord
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup (fieldAut n F σ)) := by
    obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
    refine (card_fixedSubgroup_eq_of_intertwine (conjAut n F H : MulAut _) (fieldAut n F σ) β
      fun x => ?_).symm
    rw [hβh]
    simp [MulAut.mul_apply]
  have hfix : fixedSubgroup (fieldAut n F σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :=
    SetLike.coe_injective (fixedSubgroup_fieldAut_eq_range hp hn hdiv' σ hσord)
  have hinj := linearSubfieldInclusion_injective (K := F) (n := n) (by omega)
    (semilinearFixedSubfield σ)
  have hcard2 : Nat.card (fixedSubgroup (fieldAut n F σ)) =
      Nat.card (projectiveSL n (semilinearFixedSubfield σ)) := by
    rw [hfix]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hf0 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have : Finite (semilinearFixedSubfield σ) := Subtype.finite
  have hmodel : StatedClassicalModel (projectiveSL n (semilinearFixedSubfield σ)) .PSL n ℓ
      (f / p) :=
    ⟨⟨hℓ, hf0, hn2, fun h => by simp at h; omega, fun h => by simp at h; omega⟩,
      semilinearFixedSubfield σ, inferInstance, inferInstance, hcardk,
      ⟨(statedProjSLEquiv n (semilinearFixedSubfield σ)).symm⟩⟩
  have hkl5 := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psl hn2 hmodel
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2, mul_comm]
  simpa [lieOrderNumerator] using hkl5.symm

theorem card_fixed_PSL_two {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL 2 ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .PSL 2 (ℓ ^ f₀) =
        Nat.gcd 2 (ℓ ^ f₀ - 1) * Nat.card (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  let ψ : K ≃* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG F :=
    (e.trans (statedProjSLEquiv 2 F)).trans
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).symm.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG F))
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαin (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner K).one_mem)
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ := CFSG.RankThree.PartOne.FOC.psl_two_fixSub_equiv_gen hℓ hp hp2
    hf hFcard ψ hαord hαin
  have h1 : Nat.card (fixedSubgroup α) = Nat.card (CFSG.RankThree.PartOne.Sec66T.fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have h2 : Nat.card (CFSG.RankThree.PartOne.Sec66T.fixSub α) =
      Nat.card (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG k) :=
    Nat.card_congr eX.toEquiv
  have h3 : Nat.card (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG k) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    (Nat.card_congr
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG k).toEquiv).symm
  have : Finite k := Subtype.finite
  have h4 := CFSG.RankThree.PartTwo.KFacts.card_psl_mul_gcd (K := k) (n := 2) (by norm_num)
  rw [hkcard] at h4
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [h1, h2, h3, mul_comm]
  simpa [lieOrderNumerator, Nat.gcd_comm (ℓ ^ (f / p) - 1) 2] using h4.symm

theorem fixedLowerBoundAt_PSL : FixedLowerBoundAt .PSL := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .PSL n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hdiv' : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := hdiv
  have hn2 : 2 ≤ n := hcl.1.2.2.1
  have hpos : 0 < p := hp.pos
  by_cases hn3 : 3 ≤ n
  · obtain ⟨f₁, hf₁, heq⟩ := card_fixed_PSL_three hn3 hcl hp hp2 hdiv' α hαp hαin
    have : f₁ = f₀ := by
      have := hf.symm.trans hf₁
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    subst this
    exact dvd_of_eq heq
  · obtain rfl : n = 2 := by omega
    obtain ⟨f₁, hf₁, heq⟩ := card_fixed_PSL_two hcl hp hp2 α hαp hαin
    have : f₁ = f₀ := by
      have := hf.symm.trans hf₁
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    subst this
    exact dvd_of_eq heq

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
