module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79f

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem y7c_schur_gl3
    (hM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2)
    {R Z N : Subgroup G} (hZ : IsGL3Ext R Z) (hNZ : N ≤ Z) (hNR : R ≤ normalizer (N : Set G))
    (hcentral : ⁅R, Z⁆ ≤ N) : Nat.card ↥((⁅R, R⁆ ⊓ Z) ⊔ N) ≤ 2 * Nat.card N := by
  classical
  obtain ⟨hZR, hZn, hZiso⟩ := hZ
  set H : Subgroup G := (⁅R, R⁆ ⊓ Z) ⊔ N with hH
  have hNR' : (N.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNR
  letI : (N.subgroupOf R).Normal := hNR'
  letI : (Z.subgroupOf R).Normal := hZn
  let Q := ↥R ⧸ N.subgroupOf R
  let π : ↥R →* Q := QuotientGroup.mk' (N.subgroupOf R)
  haveI : ((Z.subgroupOf R).map π).Normal :=
    hZn.map π (QuotientGroup.mk'_surjective (N.subgroupOf R))
  have hsub : ⁅Z.subgroupOf R, (⊤ : Subgroup ↥R)⁆ ≤ N.subgroupOf R := by
    change ⁅Z.subgroupOf R, (⊤ : Subgroup ↥R)⁆ ≤ N.comap R.subtype
    rw [← Subgroup.map_le_iff_le_comap]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hZR,
      Subgroup.map_top, Subgroup.range_subtype, Subgroup.commutator_comm]
    exact hcentral
  have hZbcenter : (Z.subgroupOf R).map π ≤ Subgroup.center Q := by
    rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
    have htop : (⊤ : Subgroup ↥R).map π = (⊤ : Subgroup Q) :=
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (N.subgroupOf R))
    rw [← htop, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hsub
  have hNZ' : N.subgroupOf R ≤ Z.subgroupOf R := Subgroup.subgroupOf_mono R hNZ
  have hQZiso : Nonempty ((Q ⧸ (Z.subgroupOf R).map π) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
    rcases hZiso with ⟨e⟩
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient (N.subgroupOf R) (Z.subgroupOf R)
      hNZ').trans e⟩
  have hcomm : ((⁅R, R⁆).subgroupOf R).map π ≤ commutator Q := by
    have hle : (⁅R, R⁆).subgroupOf R ≤ _root_.commutator ↥R := by
      rw [← Subgroup.map_le_map_iff_of_injective R.subtype_injective]
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self R),
        Subgroup.map_subtype_commutator]
    calc ((⁅R, R⁆).subgroupOf R).map π
        ≤ (_root_.commutator ↥R).map π := Subgroup.map_mono hle
      _ = (⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆).map π := rfl
      _ = commutator Q := by
          rw [Subgroup.map_commutator,
            Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (N.subgroupOf R))]
          exact (_root_.commutator_def Q).symm
  have hH'sup : H.subgroupOf R
      = (⁅R, R⁆ ⊓ Z).subgroupOf R ⊔ N.subgroupOf R := by
    rw [hH, Subgroup.subgroupOf_sup (inf_le_left.trans (Subgroup.commutator_le_self R))
      (hNZ.trans hZR)]
  have hNbot : (N.subgroupOf R).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq ((QuotientGroup.ker_mk' (N.subgroupOf R)).symm)
  have hmap_le : (H.subgroupOf R).map π ≤ commutator Q ⊓ (Z.subgroupOf R).map π := by
    rw [hH'sup, Subgroup.map_sup, hNbot, sup_bot_eq]
    refine le_inf ?_ ?_
    · calc ((⁅R, R⁆ ⊓ Z).subgroupOf R).map π
          ≤ ((⁅R, R⁆).subgroupOf R).map π :=
            Subgroup.map_mono (Subgroup.subgroupOf_mono R inf_le_left)
        _ ≤ commutator Q := hcomm
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono R inf_le_right)
  have hHR : H ≤ R := by
    rw [hH]
    exact sup_le (inf_le_left.trans (Subgroup.commutator_le_self R)) (hNZ.trans hZR)
  have hN'le : N.subgroupOf R ≤ H.subgroupOf R := by
    rw [hH'sup]; exact le_sup_right
  have hrel : (N.subgroupOf R).relIndex (H.subgroupOf R)
      = Nat.card ↥((H.subgroupOf R).map π) := by
    rw [← Subgroup.relIndex_ker (H.subgroupOf R) π, QuotientGroup.ker_mk']
  have hcardH' : Nat.card ↥(H.subgroupOf R)
      = Nat.card ↥((H.subgroupOf R).map π) * Nat.card ↥(N.subgroupOf R) := by
    have h1 := Subgroup.relIndex_mul_card (N.subgroupOf R) (H.subgroupOf R)
    rw [inf_eq_left.mpr hN'le] at h1
    rw [← h1, hrel]
  have hcardH : Nat.card ↥H = Nat.card ↥(H.subgroupOf R) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHR).toEquiv).symm
  have hcardN' : Nat.card ↥(N.subgroupOf R) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNZ.trans hZR)).toEquiv
  have hcard : Nat.card ↥H = Nat.card N * Nat.card ↥((H.subgroupOf R).map π) := by
    rw [hcardH, hcardH', hcardN']
    exact Nat.mul_comm _ _
  have hschur : Nat.card ↥(commutator Q ⊓ (Z.subgroupOf R).map π) ∣ 2 :=
    y7c_schur_quot hM hZbcenter hQZiso
  have hle2 : Nat.card ↥((H.subgroupOf R).map π) ≤ 2 := by
    have hdvd : Nat.card ↥((H.subgroupOf R).map π) ∣ 2 :=
      (Subgroup.card_dvd_of_le hmap_le).trans hschur
    exact Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card ↥H
      = Nat.card N * Nat.card ↥((H.subgroupOf R).map π) := hcard
    _ ≤ Nat.card N * 2 := Nat.mul_le_mul_left _ hle2
    _ = 2 * Nat.card N := Nat.mul_comm _ _

end CFSG.OddStandard.HigherRank.YamadaG23
