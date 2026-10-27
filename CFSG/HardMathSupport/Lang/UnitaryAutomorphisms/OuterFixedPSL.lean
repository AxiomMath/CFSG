module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldLinear
public import CFSG.GH74.Generic.S1.KL5Ord
import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSL)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.HardMathSupport.Lang.Coordinator

noncomputable def statedProjSLEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)


variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem fixedSubgroup_fieldAut_eq_range {p : ℕ} (hp : p.Prime) (hn : 3 ≤ n)
    (hdiv : ¬ p ∣ Nat.gcd n (Nat.card F - 1)) (σ : F ≃+* F) (hσ : orderOf σ = p) :
    (fixedSubgroup (fieldAut n F σ) : Set (projectiveSL n F)) =
      ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range : Set (projectiveSL n F)) := by
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hdesc : ∀ a : Fˣ, (a : F) ∈ semilinearFixedSubfield σ → (∃ u : Fˣ, u ^ n = a) →
      ∃ w : Fˣ, (w : F) ∈ semilinearFixedSubfield σ ∧ w ^ n = a := by
    by_cases hpn : p ∣ n
    · have hpK : ¬ p ∣ Nat.card Fˣ := by
        rw [Nat.card_units]
        intro h
        exact hdiv (Nat.dvd_gcd hpn h)
      exact root_descent_of_not_dvd hp hk hσp hpK
    · exact root_descent_of_coprime hk hσp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm
  exact fixed_points_eq_range hk (by omega) hdesc


theorem outerFixedOrder_PSL_three_le {K : Type} [Group K] [Finite K] {n ℓ f : ℕ} (hn : 3 ≤ n)
    (hcl : StatedClassicalModel K .PSL n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .PSL n (ℓ ^ f₀) := by
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
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n F) := fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  rw [← card_fixedSubgroup_congr θ α]
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ semilinearAutGroup n F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow hn (hp.odd_of_ne_two hp2) hβp
  by_cases hD : β ∈ linearAutGroup n F
  · exfalso
    exact hβout (CFSG.RankThree.PartOne.OutStructure.linear_D2 hp hn hdiv' β hD 1
      (by rw [pow_one, hβp]; exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem))
  obtain ⟨hpf, σ, hσord, ⟨h, hh, hβh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf hn hFcard hp β hβE hD hβord
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup (fieldAut n F σ)) := by
    obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
    refine (card_fixedSubgroup_eq_of_intertwine (conjAut n F H : MulAut _ ) (fieldAut n F σ) β
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
  have hmodel : StatedClassicalModel (projectiveSL n (semilinearFixedSubfield σ)) .PSL n ℓ (f / p) :=
    ⟨⟨hℓ, hf0, hn2, fun h => by simp at h; omega, fun h => by simp at h; omega⟩,
      semilinearFixedSubfield σ, inferInstance, inferInstance, hcardk,
      ⟨(statedProjSLEquiv n (semilinearFixedSubfield σ)).symm⟩⟩
  have hkl5 := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psl hn2 hmodel
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2]
  exact Dvd.intro _ (by simpa [lieOrderNumerator] using hkl5)



theorem outerFixedOrder_PSL_two {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL 2 ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .PSL 2 (ℓ ^ f₀) := by
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
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ := CFSG.RankThree.PartOne.FOC.psl_two_fixSub_equiv_gen hℓ hp hp2 hf
    hFcard ψ hαord hαin
  have h1 : Nat.card (fixedSubgroup α) = Nat.card (CFSG.RankThree.PartOne.Sec66T.fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have h2 : Nat.card (CFSG.RankThree.PartOne.Sec66T.fixSub α) =
      Nat.card (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG k) :=
    Nat.card_congr eX.toEquiv
  have h3 : Nat.card (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG k) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    (Nat.card_congr (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG k).toEquiv).symm
  have : Finite k := Subtype.finite
  have h4 := CFSG.RankThree.PartTwo.KFacts.card_psl_mul_gcd (K := k) (n := 2) (by norm_num)
  rw [hkcard] at h4
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [h1, h2, h3]
  exact Dvd.intro _ (by simpa [lieOrderNumerator] using h4)


theorem outerFixedOrderBoundAt_PSL : OuterFixedOrderBoundAt .PSL := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv _ α hαp hαin
  left
  have hcl : StatedClassicalModel K .PSL n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hdiv' : ¬ p ∣ Nat.gcd n (ℓ ^ f - 1) := hdiv
  have hn2 : 2 ≤ n := hcl.1.2.2.1
  by_cases hn3 : 3 ≤ n
  · exact outerFixedOrder_PSL_three_le hn3 hcl hp hp2 hdiv' α hαp hαin
  · obtain rfl : n = 2 := by omega
    exact outerFixedOrder_PSL_two hcl hp hp2 α hαp hαin

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
