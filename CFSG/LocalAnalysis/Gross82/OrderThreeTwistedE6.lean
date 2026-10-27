module

public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.LocalAnalysis.Gross82.OrderThreeArith
import CFSG.LocalAnalysis.Gross82.OrderThreeTools
import CFSG.LocalAnalysis.Gross82.ExceptionalFieldOrder
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7f

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.Gross82.OrderThree

set_option linter.unusedSectionVars false

section


private theorem field_descent_twistedE6 {F : Type} [Field F] [Finite F] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hcard : Nat.card F = (ℓ ^ f) ^ 2)
    {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup F σ) →* RingAut F)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 F σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    {β : MulAut (twistedE6RootGroup F σ)} (hβp : β ^ 3 = 1) (hη1 : Θ β ≠ 1) :
    ∃ d : ℕ, f = 3 * d ∧
      Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .twistedE6 0 (ℓ ^ d) := by
  have hK2 : Nat.card F = ℓ ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd0, r, ε, hε, ψ, hψ⟩ :=
    twisted_E6_field_descent_of_prime_order hℓ hf F hK2 σ hσ Θ hΘ Nat.prime_three
      (by norm_num) β hβp hη1
  have hK : Nat.card F = ℓ ^ (2 * (d * 3)) := by
    rw [hK2, hd, show 2 * (3 * d) = 2 * (d * 3) by ring]
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ, hd, mul_comm]
  have hle : fixedSubgroup β ≤ fixedSubgroup (β ^ r) := fixedSubgroup_le_pow β r
  have hconj : Nat.card (fixedSubgroup (β ^ r)) =
      Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    card_fixedSubgroup_eq_of_intertwine
      (ψ : twistedE6RootGroup F σ ≃* twistedE6RootGroup F σ) (β ^ r) _ fun x => by
      have h := congrArg (fun g : MulAut (twistedE6RootGroup F σ) => g (ψ x)) hψ
      simpa [MulAut.mul_apply] using h.symm
  have hdvd := card_fixedSubgroup_fieldActor_dvd hℓ hd0 (by norm_num) F hK σ ε hσ' hε
  exact ⟨d, hd, (Subgroup.card_dvd_of_le hle).trans (hconj ▸ hdvd)⟩

private theorem false_of_not_inner_twistedE6 (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .twistedE6 n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .twistedE6 n (ℓ ^ f)) {α : MulAut K} (hα3 : α ^ 3 = 1)
    {P : Sylow 3 K} (hfix : ∀ x ∈ (P : Subgroup K), α x = x) (hαin : α ∉ inner K) : False := by
  obtain ⟨hℓ, hf, hn⟩ := id hadm
  subst hn
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel K .twistedE6 ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h3' : 3 ∣ ℓ ^ f + 1 := h3.trans (Nat.gcd_dvd_right 3 (ℓ ^ f + 1))
  obtain ⟨K', _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  set β : MulAut (twistedE6RootGroup K' σ) := MulAut.congr e α with hβdef
  have hβp : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : β ∉ twistedE6Inn K' σ :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  obtain ⟨P', hfix'⟩ := exists_sylow_fix_congr e P hfix
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K' hcard σ hσ
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ twistedE6Inn K' σ ⊔ twistedE6Diag K' σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hβout (InputsMisc7e.twistedE6InndiagSylowThree_of_E6
      InputsMisc7f.e6InndiagSylowThree_holds ℓ f hℓ hf h3' K' hcard σ hσ P' β hmem
      ⟨1, by simpa using hβp⟩ hfix')
  obtain ⟨d, hd, hdvd⟩ := field_descent_twistedE6 hℓ hf hcard hσ Θ hΘ hβp hη1
  have hC : Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .twistedE6 0 (ℓ ^ d) := by
    rw [← card_fixedSubgroup_congr e α, ← hβdef]
    exact hdvd
  have hs : ℓ ^ f = (ℓ ^ d) ^ 3 := by rw [hd, pow_mul']
  have hd1 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    omega
  have hs2 : 2 ≤ ℓ ^ d := hℓ.two_le.trans (Nat.le_self_pow hd1 ℓ)
  have ha : lieOrderNumerator .twistedE6 0 (ℓ ^ d) ≠ 0 :=
    CFSG.AGLEmbedding.OuterSylow.lieOrderNumerator_ne_zero (by decide)
      (CFSG.AGLEmbedding.OuterSylow.one_le_lieSylowExponent hadm) hs2
  exact false_of_card_fixedSubgroup_dvd hLie hadm hmodel P hfix hs ha hC
    (ExceptionalFieldOrder.padicValNat_three_lieOrder_twistedE6_cube_lt hs2)

theorem grossThreeInnerOrderThree_twistedE6 (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .twistedE6 n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .twistedE6 n (ℓ ^ f)) : GrossThreeInnerOrderThree K := by
  intro α hα P hfix
  by_contra hαin
  exact false_of_not_inner_twistedE6 hLie hadm hmodel h3 hα hfix hαin

end

end CFSG.LocalAnalysis.Gross82
