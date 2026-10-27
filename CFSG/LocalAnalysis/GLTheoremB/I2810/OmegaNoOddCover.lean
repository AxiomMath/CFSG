module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaCentre
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalCentre
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.Alternating.Multipliers.Main
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

open CFSG.Open CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Cooperstein.StructureLie

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCentre

theorem statedScalars_zmod_two (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hx
  have hu : u = 1 := by
    apply Units.ext
    have h0 : (u : ZMod 2) ≠ 0 := u.ne_zero
    revert h0
    generalize (u : ZMod 2) = a
    revert a
    decide
  rw [hu, map_one]
  exact Subgroup.one_mem _

noncomputable def statedProjMulEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : H ≃* StatedProj H :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (by rw [statedScalars_zmod_two, Subgroup.bot_subgroupOf]))

theorem card_dvd_card_hopfMultiplier {G X : Type} [Group G] [Group X] (hG : Group.IsPerfect G)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (e : G ⧸ Z ≃* X) :
    Nat.card Z ∣ Nat.card (hopfMultiplier X) := by
  haveI := hG
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' Z)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ Z
    rw [e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h := Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective _ hsurj (hker.le.trans hZ))
  rwa [hker] at h

theorem lieModel_plus {n : ℕ} (hn : 4 ≤ n) {G : Type} [Group G]
    (e : G ≃* StatedOmega (StatedQuadPlus n (ZMod 2))) :
    Models.LieModel G .POmegaPlus n 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, hn⟩, Or.inl ⟨⟨Nat.prime_two, le_rfl, hn⟩, ZMod 2, inferInstance,
    inferInstance, by simp, ⟨e.trans (statedProjMulEquiv _)⟩⟩⟩

theorem lieModel_minus {n : ℕ} (hn : 4 ≤ n) {G : Type} [Group G]
    (e : G ≃* StatedOmega (StatedQuadMinus n (ZMod 2) 1 1)) :
    Models.LieModel G .POmegaMinus n 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, hn⟩, Or.inl ⟨⟨Nat.prime_two, le_rfl, hn⟩, ZMod 2, inferInstance,
    inferInstance, by simp, 1, 1, by decide, ⟨e.trans (statedProjMulEquiv _)⟩⟩⟩

theorem lieModel_psu_four {G : Type} [Group G]
    (e : G ≃* StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) :
    Models.LieModel G .PSU 4 2 1 := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hsimpleT : IsSimpleGroup (StatedSU 4 (2 ^ 1) E) := by
    have := hsimple
    exact eSU.symm.isSimpleGroup
  have hnaT : ¬ ∀ x y : StatedSU 4 (2 ^ 1) E, x * y = y * x := fun hc =>
    hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hcenter : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    have := hsimpleT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedSU 4 (2 ^ 1) E)) with h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hnaT
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenter]
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, hnq⟩, Or.inl ⟨⟨Nat.prime_two, le_rfl, by norm_num, hnq⟩,
    E, inferInstance, h.finite, hE, ⟨(e.trans eSU).trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hscal.symm))⟩⟩⟩

theorem omegaNoOddCover_holds
    : OmegaNoOddCover := by
  intro n hn G _ _ hG Z _ hZc hodd he
  have hperf : Group.IsPerfect G := Group.isPerfect_def.2 hG
  haveI : Finite (G ⧸ Z) := Finite.of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hdvd := card_dvd_card_hopfMultiplier hperf Z hZc (MulEquiv.refl (G ⧸ Z))
  have h4 : Nat.card Z ∣ 4 := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      rcases Nat.lt_or_ge n 3 with h | h
      · obtain rfl : n = 2 := by omega
        have h2 := card_dvd_card_hopfMultiplier hperf Z hZc
          (e.trans CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8)
        rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num : 8 ≤ 8)] at h2
        exact h2.trans (by norm_num)
      · exact hdvd.trans (card_hopfMultiplier_dvd_four_of_model (t := .POmegaPlus) (n := n + 1)
          (lieModel_plus (by omega) e) (genericOrders_POmegaPlus_two (n + 1)))
    · obtain ⟨e⟩ := he
      rcases Nat.lt_or_ge n 3 with h | h
      · obtain rfl : n = 2 := by omega
        exact hdvd.trans (card_hopfMultiplier_dvd_four_of_model (t := .PSU) (n := 4)
          (lieModel_psu_four e) genericOrders_PSU_four_two)
      · exact hdvd.trans (card_hopfMultiplier_dvd_four_of_model (t := .POmegaMinus) (n := n + 1)
          (lieModel_minus (by omega) e) (genericOrders_POmegaMinus_two (by omega)))
  have h1 : Nat.card Z = 1 :=
    eq_one_of_odd_of_dvd_two_pow (k := 2) hodd (by simpa using h4)
  exact Subgroup.eq_bot_of_card_eq Z h1

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCentre
