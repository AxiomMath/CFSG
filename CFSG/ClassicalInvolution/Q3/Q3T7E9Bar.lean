module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarComp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarNbr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}


theorem exists_model_conj_u (D : OmegaLieU p f Ω) (i : Fin D.card) {g : G}
    (hg : g ∈ omegaGen Ω) :
    ∃ q : (D.kind i).G, ∀ x ∈ D.comp i, g * x * g⁻¹ = D.hom i q * x * (D.hom i q)⁻¹ := by
  rw [← D.iSup_comp] at hg
  induction hg using Subgroup.iSup_induction' with
  | hp k y hy =>
    by_cases hki : k = i
    · subst hki
      obtain ⟨q, rfl⟩ := hy
      exact ⟨q, fun x _ => rfl⟩
    · refine ⟨1, fun x hx => ?_⟩
      have := D.comp_commute hki y hy x hx
      rw [map_one, one_mul, inv_one, mul_one, this, mul_assoc, mul_inv_cancel, mul_one]
  | h1 => exact ⟨1, fun x _ => by simp⟩
  | hmul a b ha hb ha' hb' =>
    obtain ⟨qa, hqa⟩ := ha'
    obtain ⟨qb, hqb⟩ := hb'
    refine ⟨qa * qb, fun x hx => ?_⟩
    have hbx : b * x * b⁻¹ ∈ D.comp i := D.mem_comp_conj (by rw [← D.iSup_comp]; exact hb) hx
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = D.hom i qa * (b * x * b⁻¹) * (D.hom i qa)⁻¹ := hqa _ hbx
      _ = D.hom i (qa * qb) * x * (D.hom i (qa * qb))⁻¹ := by
          rw [hqb x hx]
          simp [map_mul, mul_assoc]

end Model

section Bar

variable {Y : Type} [Group Y] [Finite Y]


theorem e189_bar_three {n : ℕ} (hbelow : CITBelowT (.sl2 3 1) n) (hih : IH8T 3 1 n)
    (hcard : Nat.card Y < n) (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)}
    (hΛm : HypOmegaModU (.sl2 3 1) Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤) (hA : ∀ L ∈ Λ, AEmpty Λ L)
    {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₂ K'' ∧
        Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
    (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
        ∀ w ∈ conjSub x K ⊔ M', w * (z * t) = (z * t) * w) := by
  obtain ⟨D⟩ := exists_omegaLieU hbelow hΛm ⟨K, hK⟩ hO hcard
  have hs : (MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  have hex : ExactMembers Λ := by
    intro L hL
    obtain ⟨z', hz'⟩ := hΛm.classical L hL
    exact hz'.oddCore_eq_bot_of_natCard_eq hs (D.card_eq rfl L hL)
  obtain ⟨g, hg⟩ : ∃ g : Y, conjSub g K = J := by
    by_contra hnc
    have hc := hih.thm4 (by norm_num) (by norm_num) Y hcard Λ hΛm hO hA K hK J hJ hnc
    exact hne (conjSub_eq_of_mem_of_commutes ht.mem hc.symm)
  have htg : t = g * z * g⁻¹ := ht.eq (hg ▸ hz.conj g)
  have hgΩ : g ∈ omegaGen Λ := by
    have : omegaGen Λ = ⊤ := hgen
    rw [this]
    exact Subgroup.mem_top g
  obtain ⟨i, F₁, hF₁, hKF⟩ := D.fundamental K hK
  obtain ⟨q, hq'⟩ := exists_model_conj_u D i hgΩ
  have hzK : z ∈ D.comp i := by
    have : z ∈ F₁.map (D.hom i) := hKF ▸ hz.mem
    exact Subgroup.map_le_range _ _ this
  have hqt : t = D.hom i q * z * (D.hom i q)⁻¹ := htg.trans (hq' z hzK)
  have hK' : conjSub t K ∈ Λ := hΛm.conjInvariant t K hK
  have hzK' : IsUniqueInvolution (conjSub t K) z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  have hcomm : Commutes K (conjSub t K) :=
    commutes_of_twin3 hΛm hex hK hK' (Ne.symm hne) hz hzK'
  have hnb : ∀ L ∈ Λ, ((L = K ∨ Commutes L K) ↔
      (L = conjSub t K ∨ Commutes L (conjSub t K))) :=
    nbhd_eq_of_twin3 hΛm hex hK hK' hz hzK' hcomm
  exact e189_bar_comp hΛm.conjInvariant (D.kind i) (D.valid i) (D.hom i) (D.ker_le_center i) hF₁
    hKF hK hz q hqt hzt hne hcomm hnb

end Bar

end CFSG.ClassicalInvolution.Q3.Q3T7E9
