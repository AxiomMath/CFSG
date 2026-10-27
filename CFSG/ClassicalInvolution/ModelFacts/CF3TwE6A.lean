module

public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6Cent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Asc77.T3CII (eq_three_of_pow_eq_three ne_two_of_pow_eq_three)


section Cent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

variable {p e : ℕ} [Fact p.Prime]

theorem twistedE6_rankOne_gen3_or_perfect (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (j : Fin (Tag.rank .F4)) :
    e6RankOne p e j ≤ ⁅e6RankOne p e j, e6RankOne p e j⁆ ∨ Gen3 (e6RankOne p e j) := by
  have hθ := frobQ_frobQ p e he
  have h4K : 4 ≤ Nat.card (GaloisField p (2 * e)) := by
    rw [card_galoisField_two_mul' p e he, hq3]
    show 4 ≤ 3 ^ 2
    norm_num
  have hcardF : Nat.card
      (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField (frobQ p e)) = 3 := by
    rw [CFSG.ClassicalInvolution.WeakCT.card_fixedField_frobQ p e he]
    exact hq3
  have hchar : CharP (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField (frobQ p e)) 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField (frobQ p e)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardF]; norm_num)
    haveI := Fintype.ofFinite (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField (frobQ p e))
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hcardF)
  fin_cases j
  · right
    have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_zero (frobQ p e)
    have hr : Gen3 (CFSG.ClassicalInvolution.WeakCT.nodeHom0 (frobQ p e)).range := by
      have := (gen3_top_sl2 (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
        (frobQ p e))).map (CFSG.ClassicalInvolution.WeakCT.nodeHom0 (frobQ p e))
      rwa [← MonoidHom.range_eq_map] at this
    rw [← h] at hr
    exact hr
  · right
    have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one (frobQ p e)
    have hr : Gen3 (CFSG.ClassicalInvolution.WeakCT.nodeHom1 (frobQ p e)).range := by
      have := (gen3_top_sl2 (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
        (frobQ p e))).map (CFSG.ClassicalInvolution.WeakCT.nodeHom1 (frobQ p e))
      rwa [← MonoidHom.range_eq_map] at this
    rw [← h] at hr
    exact hr
  · left
    have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two (frobQ p e) hθ
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4K)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom2 (frobQ p e) hθ)
    rw [← h] at hr
    exact hr
  · left
    have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_three (frobQ p e) hθ
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4K)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom3 (frobQ p e) hθ)
    rw [← h] at hr
    exact hr

theorem twistedE6_rootPair_gen3_or_perfect (he : 1 ≤ e) (hq3 : p ^ e = 3)
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) :
    (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) ≤
      ⁅twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
          twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ),
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
          twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ)⁆) ∨
    Gen3 (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ)) := by
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨Fact.out, he, rfl⟩
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .twistedE6 0 p e Fact.out trivial hadm
  have hδ' : δ ∈ (modelUniv .twistedE6 0 p e Fact.out).D.roots := by
    show δ ∈ (twistedE6Datum p e).roots
    rw [twistedDatum_roots]
    exact hδ
  obtain ⟨g, i, h⟩ := twistedE6_exists_rankOne_eq_map_conj hct rfl hδ'
  have h' : twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) =
      (e6RankOne p e i).map (MulAut.conj g).toMonoidHom := h
  rw [h']
  rcases twistedE6_rankOne_gen3_or_perfect he hq3 i with hp | hg
  · exact Or.inl (fundPerfect_map_conj_le_commutator hp g)
  · exact Or.inr (hg.map _)

theorem twistedE6_commute_of_phi_sign3 (he : 1 ≤ e) (hq3 : p ^ e = 3)
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    {u : twistedE6Group p e}
    (hu : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) u =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))
    {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ) (hb : rootChar b δ = 1) :
    ∀ r ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ), u * r = r * u := by
  have hb' : rootChar b (-δ) = 1 := by rw [twistedE6_rootChar_neg, hb, inv_one]
  have hle : twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ) ≤ (Subgroup.centralizer
        {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_rootChar p e hb hg
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_rootChar p e hb' hg
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨Fact.out, he, rfl⟩
  have hp2 : p ≠ 2 := ne_two_of_pow_eq_three hq3
  rcases twistedE6_rootPair_gen3_or_perfect he hq3 hδ with hperf | hG3
  · have hc : ∀ r ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ ⊔
        twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-δ), ⁅u, r⁆ ∈ Subgroup.center _ := by
      intro r hr
      refine ker_twistedE6Phi_le_center p e (AlgebraicClosure (GaloisField p (2 * e))) ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hu]
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hle hr))
      calc rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
            twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
            (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
            (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹
          = (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
            rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))) *
            (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
            (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹ := by rw [h]
        _ = 1 := by group
    exact CFSG.ClassicalInvolution.RouteD.Exotic.commutes_of_commutator_mem_center hperf hc
  · have hk3 : ∀ x ∈ (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))).ker,
        x ^ 3 = 1 → x = 1 := by
      intro x hx hx3
      have hxc := ker_twistedE6Phi_le_center p e (AlgebraicClosure (GaloisField p (2 * e))) hx
      obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three hq3
      exact CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime .twistedE6 0 3 1
        Nat.prime_three hp2 trivial hadm x hxc hx3
    intro r hr
    exact (commute_of_map_commute_of_gen3 (twistedE6Phi p e (AlgebraicClosure
      (GaloisField p (2 * e)))) (ker_twistedE6Phi_le_center p e _) hk3 hG3 (b := u)
      (fun a ha => by
        have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hle ha))
        rw [hu]
        exact h) r hr).symm

end Cent

end CFSG.ClassicalInvolution.ModelFacts
