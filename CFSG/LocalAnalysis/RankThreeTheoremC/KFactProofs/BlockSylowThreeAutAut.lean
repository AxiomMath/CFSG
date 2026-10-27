module

public import CFSG.RankThree.SubgroupLists2.OmegaThree
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

section Aut

theorem finite_mulAut (X : Type*) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun e : MulAut X => (e : X → X)) fun a b h => MulEquiv.ext (congrFun h)

theorem card_mulAut_eq_of_center_bot {X : Type*} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) : Nat.card (MulAut X) = Nat.card (Outer X) * Nat.card X := by
  have : Finite (MulAut X) := finite_mulAut X
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (MonoidHom.ker_eq_bot_iff _).1 (eq_bot_iff.2 fun x hx => ?_)
    have hcentral : x ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have hconj := congrArg (fun f : MulAut X => f y) hx
      change x * y * x⁻¹ = y at hconj
      have heq := congrArg (fun z : X => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rw [hc] at hcentral
    exact hcentral
  have h1 : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X), h1]

theorem not_27_dvd_card_mulAut_of_outer {X : Type*} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) (hO : ¬ 3 ∣ Nat.card (Outer X)) (hX : ¬ 27 ∣ Nat.card X) :
    ¬ 27 ∣ Nat.card (MulAut X) := by
  rw [card_mulAut_eq_of_center_bot hc]
  intro h
  have hcop : Nat.Coprime 27 (Nat.card (Outer X)) := by
    have : Nat.Coprime (3 ^ 3) (Nat.card (Outer X)) := Nat.Coprime.pow_left 3
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hO)
    simpa using this
  exact hX (hcop.dvd_of_dvd_mul_left h)

theorem card_mulAut_dvd_of_perfect (L : Type*) [Group L] [Finite L] [Group.IsPerfect L] :
    Nat.card (MulAut L) ∣ Nat.card (MulAut (L ⧸ Subgroup.center L)) := by
  have : Finite (MulAut (L ⧸ Subgroup.center L)) := finite_mulAut _
  exact Subgroup.card_dvd_of_injective _
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective L)

end Aut

section Small

theorem card_outer_dvd_two_of_model_psl_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) : Nat.card (Outer X) ∣ 2 := by
  obtain ⟨⟨-, -, hn, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by
    by_contra h3
    exact hn2 (by rw [show n = 2 by omega]; rfl)
  have e' : X ≃* LinearFlag.projectiveSL n K := e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hdvd := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two
    le_rfl hn3 hK
  rw [Nat.card_congr (equivalence e').toEquiv]
  simpa using hdvd

theorem not_27_dvd_card_mulAut_of_model_psl_two {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) {n : ℕ} (h : StatedClassicalModel X .PSL n 2 1) (hn : n ≤ 5) :
    ¬ 27 ∣ Nat.card (MulAut X) := by
  have hn3 : 3 ≤ n := by
    obtain ⟨⟨-, -, hn2, hn22, -⟩, -⟩ := h
    by_contra h3
    exact hn22 (by rw [show n = 2 by omega]; rfl)
  have hO : ¬ 3 ∣ Nat.card (Outer X) := fun h3 => by
    have := h3.trans (card_outer_dvd_two_of_model_psl_two h)
    omega
  refine not_27_dvd_card_mulAut_of_outer hc hO ?_
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
  interval_cases n <;> decide +kernel

theorem not_27_dvd_card_mulAut_of_equiv_alt {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 8)
    (e : X ≃* alternatingGroup (Fin m)) : ¬ 27 ∣ Nat.card (MulAut X) := by
  have hm5 : 5 ≤ m := by omega
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hO : ¬ 3 ∣ Nat.card (Outer X) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact not_dvd_card_outer_alternatingGroup m hm5 3 Nat.prime_three (by norm_num)
  refine not_27_dvd_card_mulAut_of_outer hc hO ?_
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rcases hm with rfl | rfl | rfl <;> decide

theorem not_27_dvd_card_mulAut_of_model_psl_seven {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) (h : StatedClassicalModel X .PSL 2 7 1) :
    ¬ 27 ∣ Nat.card (MulAut X) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have hF7 : Nat.card F = 7 := by simpa using hcard
  have hdvd := (linear_two_outer_order_divisor (p := 7) (f := 1) (by norm_num) F
    (by simpa using hcard)).2 X ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  have hO : ¬ 3 ∣ Nat.card (Outer X) := fun h3 => by
    have := h3.trans hdvd
    norm_num at this
  refine not_27_dvd_card_mulAut_of_outer hc hO ?_
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.SubgroupLists.card_statedProj_statedSL_two
    (by decide) hF7]
  norm_num

end Small

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
