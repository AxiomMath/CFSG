module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonOm4Core
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonOm4

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem fixSubgroup_conj_eq {S : Type} [Group S] (a : S) :
    fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set S) := by
  ext s
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc s * a = (a * s * a⁻¹) * a := by rw [h]
      _ = a * s := by group
  · intro h
    calc a * s * a⁻¹ = (s * a) * a⁻¹ := by rw [h]
      _ = s := by group

private theorem card_quot_of_label_a {X : Type} [Group X] (h : HasLabel X (· = ⟨.A, 5, 2⟩)) :
    Nat.card (X ⧸ Subgroup.center X) = ordA 5 4 := by
  obtain ⟨hΛ, -, hX⟩ := Y10GInnLin.ggHasLabel_of_hasLabel h
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.StandardType.statedClassicalModel_of_hasLabel_typeA hΛ hX)).1 rfl

private theorem card_quot_of_label_twD {X : Type} [Group X]
    (h : HasLabel X (· = ⟨.twD, 4, 2⟩)) :
    Nat.card (X ⧸ Subgroup.center X) = ordTwistedD 4 4 := by
  obtain ⟨-, -, hX⟩ := Y10GInnLin.ggHasLabel_of_hasLabel h
  obtain ⟨F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := (hX : CFSG.Assembly.LargeEvenRecipeOmegaMinus 3 4
    (fun R' _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R')))
  have hM := CFSG.StandardType.statedClassicalModel_omegaMinus 4 2 (hF.trans (by norm_num)) b c
    hbc ⟨Nat.prime_two, by norm_num, le_rfl⟩
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).2.2.2.2 rfl

private theorem card_lt_of_label_twD_small {S : Type} [Group S] {lab : GLALabel}
    (htag : lab.tag = .twD) (hn : lab.n = 2) (hr2 : 2 ≤ lab.rank) (hr4 : lab.rank < 4)
    (hS : CFSG.StandardType.GGHasLabel lab S) : Nat.card S < ordTwistedD 4 4 := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hn hr2 hr4
  subst htag hn
  interval_cases r
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (hS : CFSG.Assembly.LargeEvenRecipeLinear 2 16
      (fun R' _ _ _ => Nonempty (S ≃* R')))
    have hM := CFSG.StandardType.statedClassicalModel_linear 2 4 (hF.trans (by norm_num))
      (by norm_num [StatedLieAdmissible])
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).1 rfl]
    decide
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (hS : CFSG.Assembly.LargeEvenRecipeUnitary 4 4
      (fun R' _ _ _ => Nonempty (S ≃* R')))
    have hM := CFSG.StandardType.statedClassicalModel_unitary 4 2 (hF.trans (by norm_num))
      (by norm_num [StatedLieAdmissible])
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hM)).2.1 rfl]
    decide

private theorem card_quot_of_label_twD_large {S : Type} [Group S] {lab : GLALabel}
    (htag : lab.tag = .twD) (hn : lab.n = 2) (hN : 4 ≤ lab.rank)
    (hS : CFSG.StandardType.GGHasLabel lab S) (a : S) (ha : a ^ 5 = 1) (ha1 : a ≠ 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set S))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ ordA 5 4 ∧
      (Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedD 4 4 → 6 ≤ lab.rank) := by
  have h2 : lab.rank ≠ 2 := by omega
  have h3 : lab.rank ≠ 3 := by omega
  unfold CFSG.StandardType.GGHasLabel CFSG.StandardType.LargeEvenRawDatum at hS
  simp only [htag, h2, h3, hn, ↓reduceIte] at hS
  obtain ⟨F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := (hS : CFSG.Assembly.LargeEvenRecipeOmegaMinus
    (lab.rank - 1) 4 (fun R' _ _ _ => Nonempty (S ≃* R')))
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadMinus lab.rank F b c)
  let ψ := (e.trans (CFSG.StandardType.omegaMinusProjEquiv lab.rank b c)).trans e₂
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus hN hbc
  have hminus := CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega : 1 ≤ lab.rank) hbc
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.HSubT.isComponentOf_image_centralizer ψ.toMonoidHom
    ψ.surjective (fun x hx => by
      rw [show x = 1 from ψ.injective (by rw [map_one]; exact hx)]
      exact one_mem _) hJ
  have ha5 : ψ.toMonoidHom a ^ 5 = 1 := by rw [← map_pow, ha, map_one]
  have ha1' : ψ.toMonoidHom a ≠ 1 := fun h => ha1 (ψ.injective (by rw [map_one]; exact h))
  obtain ⟨hA, hD⟩ := om4_core hF hQ hT hminus _ ha5 ha1' _ hJ'
  have hc : Nat.card (↥(J.map ψ.toMonoidHom) ⧸ Subgroup.center ↥(J.map ψ.toMonoidHom)) =
      Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    let eJ : ↥J ≃* ↥(J.map ψ.toMonoidHom) := J.equivMapOfInjective ψ.toMonoidHom ψ.injective
    exact (Nat.card_congr (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).toEquiv).symm
  have hdim : Module.finrank F (Fin (lab.rank - 1) ⊕ Fin (lab.rank - 1) ⊕ Fin 2 → F) =
      2 * lab.rank := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  rw [hc] at hA hD
  rw [hdim] at hD
  exact ⟨hA, fun h => by have := hD h; omega⟩

private theorem exists_quot_bound {Γ : Type} [Group Γ] [Finite Γ] {L K : Subgroup Γ} {y : Γ}
    {labL : GLALabel} (hy : y ∈ Subgroup.normalizer (L : Set Γ)) (hy5 : y ^ 5 = 1)
    (hyL : y ∉ Subgroup.centralizer (L : Set Γ)) (htag : labL.tag = .twD) (hn : labL.n = 2)
    (hM : MarkedInnDiag L y labL)
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)))
    {labK : GLALabel} (hlabK : LabelOf K labK) :
    ∃ (X : Type) (_ : Group X), HasLabel X (· = labK) ∧
      Nat.card (X ⧸ Subgroup.center X) ≠ ordA 5 4 ∧
      (Nat.card (X ⧸ Subgroup.center X) = ordTwistedD 4 4 → 6 ≤ labL.rank) := by
  have hLl : HasLabel ↥L (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hM
  obtain ⟨hlamL, -, hgL⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hLl
  have hβ1 := CanonSubcomp.centerQuotAut_conjAut_ne_one hy hyL (hasLabel_isQuasisimple hLl).1
  obtain ⟨hcen, hin, hpow, hKb, hlb⟩ :=
    CanonInn.marked_bridge hy hy5 hM hK ((labelOf_iff_hasLabel K labK).1 hlabK)
  refine ⟨_, _, hlb, ?_⟩
  have hr2 : 2 ≤ labL.rank := by
    have h := hlamL.2
    simp only [htag] at h
    exact h
  rcases Nat.lt_or_ge labL.rank 4 with hN4 | hN4
  ·
    have hS := card_lt_of_label_twD_small htag hn hr2 hN4 hgL
    have h1 := Subgroup.card_le_card_group ((K.subgroupOf L).map
      (QuotientGroup.mk' (Subgroup.center ↥L)))
    have h2 : Nat.card (↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) ≤
        Nat.card ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h3 : ordTwistedD 4 4 < ordA 5 4 := by decide
    exact ⟨by omega, fun h => by omega⟩
  ·
    obtain ⟨-, a, ha⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen
      (Or.inr ⟨htag, by omega, by omega⟩) hin
    rw [← ha, fixSubgroup_conj_eq] at hKb
    have ha5 : a ^ 5 = 1 := by
      have h1 : MulAut.conj (a ^ 5) = 1 := by rw [map_pow, ha, hpow]
      have hz : a ^ 5 ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro s
        have h2 := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ s) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc s * a ^ 5 = (a ^ 5 * s * (a ^ 5)⁻¹) * a ^ 5 := by rw [h2]
          _ = a ^ 5 * s := by group
      rw [hcen] at hz
      exact Subgroup.mem_bot.1 hz
    have ha1 : a ≠ 1 := fun h => hβ1 (by rw [← ha, h, map_one])
    exact card_quot_of_label_twD_large htag hn hN4 hgL a ha5 ha1 hKb

theorem omegaMinus4Comp_holds : OmegaMinus4Comp := by
  intro Γ _ _ L K y labL hy hy5 hyL htag hn hM hK
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨X, _, hX, -, hD⟩ := exists_quot_bound hy hy5 hyL htag hn hM hK h
    exact hD (card_quot_of_label_twD hX)
  · obtain ⟨X, _, hX, hA, -⟩ := exists_quot_bound hy hy5 hyL htag hn hM hK h
    exact hA (card_quot_of_label_a hX)

end CFSG.LocalAnalysis.GLTheoremA.CanonOm4

end
