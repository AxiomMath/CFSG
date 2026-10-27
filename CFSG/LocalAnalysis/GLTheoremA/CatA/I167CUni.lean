module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CUniClash
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthLabelU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni (held_unitary_components_gu_sized isComponentOf_centralizer_gu_of_su)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU SUComponentsTrivial_holds SLComponentsTrivial_holds)

set_option linter.unusedSectionVars false

private theorem i167CUni_holds_aux1 {X : Type} [Group X] [Finite X] {labK lab : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput) {a dd : ℕ} {E : Type} [Field E] [Finite E]
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (ha2 : 2 ≤ a)
    (hτ'Q : ∀ x : E, τ' x = x ^ ((2 ^ labK.n) ^ dd))
    (hEcard : Nat.card E = ((2 ^ labK.n) ^ dd) ^ 2)
    (hlab : HasLabel X (fun l : GLALabel => l = lab))
    (e : X ⧸ Subgroup.center X ≃*
      heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) :
    ∃ a m : ℕ, labK.n ∣ m ∧
      (canonLabel lab = ⟨.twA, a - 1, m⟩ ∨ canonLabel lab = ⟨.A, 1, m⟩) := by
  have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (labK.n * dd) := by
    intro x
    rw [pow_mul]
    exact hτ'Q x
  have hcardm : Nat.card E = (2 ^ (labK.n * dd)) ^ 2 := by
    rw [pow_mul]
    exact hEcard
  rcases CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC.uniLabel_cases hRig τ' hτ' ha2 hτ'm hcardm hlab
      ⟨e⟩ with h | h
  · exact ⟨a, labK.n * dd, Dvd.intro dd rfl, Or.inl h⟩
  · exact ⟨a, labK.n * dd, Dvd.intro dd rfl, Or.inr h⟩

private theorem i167CUni_holds_aux2 {X : Type} [Group X] [Finite X] {labK lab : GLALabel}
    (hRig : CFSG.StandardType.GGLabelRigidInput) {b ee : ℕ} {E : Type} [Field E] [Finite E]
    (hb2 : 2 ≤ b) (hEcard : Nat.card E = (2 ^ labK.n) ^ (2 * ee))
    (hlab : HasLabel X (fun l : GLALabel => l = lab))
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL b E)) :
    ∃ b e : ℕ, 1 ≤ e ∧ canonLabel lab = ⟨.A, b - 1, labK.n * (2 * e)⟩ := by
  have hcardm : Nat.card E = 2 ^ (labK.n * (2 * ee)) := by
    rw [pow_mul]
    exact hEcard
  have hee : 1 ≤ ee := by
    by_contra hee0
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hEcard, show ee = 0 by omega] at h1
    norm_num at h1
  exact ⟨b, ee, hee, CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig
    X lab b (labK.n * (2 * ee)) E hb2 hcardm hlab ⟨e⟩⟩

private theorem i167CUni_holds_aux3 {K : Type} [Finite K] [Nontrivial K] {labK : GLALabel}
    (hKcard : Nat.card K = (2 ^ labK.n) ^ 2) : 1 ≤ labK.n := by
  by_contra hn0
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hKcard, show labK.n = 0 by omega] at h1
  norm_num at h1


theorem i167CUni_holds : I167CUni := by
  intro S _ _ p Bb α J labK hp hp2 hFam hcen hBb hαB hord hin hSc hCJ hhalf hJ htype
  exfalso
  have hRig : CFSG.StandardType.GGLabelRigidInput := CFSG.StandardType.ggLabelRigidInput_holds
  have hnum : p ∣ 2 ^ (2 * labK.n) - 1 := i167CU_halfSplit_dvd hFam hhalf
  obtain ⟨K, hK, hKf, d, τ, hτ, A, u, J', hτQ, hKcard, hd, hdQ, hA, hu, hpow, hJ', ⟨ePQ⟩⟩ :=
    i167CU_data hp hcen hFam (by rw [← hord]; exact pow_orderOf_eq_one α) hin hJ
  obtain ⟨hord', M, hM, ⟨ePS⟩⟩ := i167CU_lift hp hp2 hτ hτQ hKcard hd hdQ A hA u hu hpow J' hJ'
  have hn0 : 1 ≤ labK.n := i167CUni_holds_aux3 hKcard
  have hdich := held_unitary_components_gu_sized SUComponentsTrivial_holds SLComponentsTrivial_holds hτ hτQ
    hKcard A hA hord' M (isComponentOf_centralizer_gu_of_su hτ A hM)
  have hQ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  obtain ⟨lab, hlab, hT⟩ : ∃ lab : GLALabel, HasLabel (PQuot p J) (fun l : GLALabel => l = lab) ∧
      ((p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
       (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
       (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
         canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩)) := by
    rcases htype with ⟨h3, n, -, hn5, h⟩ | ⟨h3, n, -, hn6, h⟩ | ⟨n, k, -, hn3, hnk, hk, hpk, h⟩
    · subst h3
      obtain ⟨lab, hl, hc⟩ := i167COrth_label_isLnA hQ hn5 h
      exact ⟨lab, hl, Or.inl ⟨rfl, n, hn5, hc⟩⟩
    · subst h3
      obtain ⟨lab, hl, hc⟩ := i167COrth_label_isOmMA hQ (n := n) (k := 1) (by omega) le_rfl (by rw [pow_one]; exact h)
      exact ⟨lab, hl, Or.inr (Or.inl ⟨rfl, n, hn6, hc⟩)⟩
    · obtain ⟨lab, hl, hc⟩ := i167COrth_label_isOmPA hQ hn3 hk
        (fun h3 => by
          by_contra hk2
          have := hnk (by omega)
          omega) h
      exact ⟨lab, hl, Or.inr (Or.inr ⟨n, k, hn3, hk, hpk, hc⟩)⟩
  refine i167CU_clash hp hp2 hnum hn0 hT ?_
  rcases hdich with ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hEcard, ⟨eM⟩⟩ |
    ⟨b, ee, E, hE, hEf, hb2, hEcard, ⟨eM⟩⟩
  · left
    refine i167CUni_holds_aux1 (X := PQuot p J) hRig (a := a) (dd := dd) (E := E) τ' hτ' ha2
      hτ'Q hEcard hlab ?_
    exact (QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)).trans (ePS.trans eM)
  · right
    refine i167CUni_holds_aux2 (X := PQuot p J) hRig (b := b) (ee := ee) (E := E) hb2
      hEcard hlab ?_
    exact (QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)).trans (ePS.trans eM)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
