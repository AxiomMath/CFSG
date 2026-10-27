module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5IsoA
import CFSG.GroupTheory.PLayer.Transfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 T Pt : Subgroup G}

theorem sec8t84d5_iso (ht : t * t = 1) (hE : IsElemAb2 E 8) (hc : Sec8T84XCore G t E Y1 Y2)
    (hT : IsSylow2Of T (normalizer (E : Set G))) (htT : t ∈ T) (hPt : Pt ≤ T)
    (hPtc : ∀ p ∈ Pt, t * p = p * t) (htPt : t ∉ Pt) (hcard : Nat.card ↥Pt = 2 ^ 7)
    (hS1 : Nat.card ↥(T ⊓ Y1) = 2 ^ 7) : Nonempty (↥(T ⊓ Y1) ≃* ↥Pt) := by
  obtain ⟨hT0syl, hTcard, hTeq, hS1syl, hS2syl, hT0eq, hcomm, hinf, hsw1, hsw2,
    hET, hE1T, hE2T, hn1, hn2⟩ := sec8t84_tstruct ht hE hc hT htT
  let φ : ↥(T ⊓ Y1) →* G := sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm
  let D : Subgroup G := φ.range
  let Z : Subgroup G := Subgroup.zpowers t
  have htT0 : t ∉ T ⊓ (Y1 ⊔ Y2) := fun h => hc.t_not (Subgroup.mem_inf.mp h).2
  have ht1 : t ≠ 1 := by
    intro h
    exact hc.t_not (by rw [h]; exact Subgroup.one_mem _)
  have hφinj : Function.Injective φ := sec8t84d5_iotaHom_injective hsw1 hcomm hinf
  have hD_le_T0 : D ≤ T ⊓ (Y1 ⊔ Y2) := sec8t84d5_range_iotaHom_le_T0 hsw1 hcomm
  have hD_cent_t : D ≤ Subgroup.centralizer ({t} : Set G) :=
    sec8t84d5_range_iotaHom_le_centralizer ht hsw1 hcomm
  have htD : t ∉ D := fun h => htT0 (hD_le_T0 h)
  have hcardD : Nat.card ↥D = 2 ^ 7 := by
    change Nat.card ↥(φ.range) = 2 ^ 7
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact hS1
  have hcardZ : Nat.card ↥Z = 2 := by
    change Nat.card ↥(Subgroup.zpowers t) = 2
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ht) ht1]
  have hDZ_bot : D ⊓ Z = ⊥ := by
    change D ⊓ Subgroup.zpowers t = ⊥
    rw [inf_comm]
    exact CFSG.zpowers_inf_eq_bot_of_not_mem Nat.prime_two (by rw [pow_two]; exact ht) ht1 htD
  have hPtZ_bot : Pt ⊓ Z = ⊥ := by
    change Pt ⊓ Subgroup.zpowers t = ⊥
    rw [inf_comm]
    exact CFSG.zpowers_inf_eq_bot_of_not_mem Nat.prime_two (by rw [pow_two]; exact ht) ht1 htPt
  have hD_comm_t : ∀ d ∈ D, t * d = d * t := fun d hd =>
    Subgroup.mem_centralizer_iff.mp (hD_cent_t hd) t (Set.mem_singleton t)
  have hDZ_cent : D ≤ Subgroup.centralizer (Z : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    change Subgroup.zpowers t ≤ Subgroup.centralizer (D : Set G)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hD_comm_t d hd).symm
  have hZD_cent : Z ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.le_centralizer_iff.mp hDZ_cent
  have hcardM : Nat.card ↥(D ⊔ Z) = Nat.card ↥D * Nat.card ↥Z := by
    have hcard' := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
        (A := D) (B := Z) (hZD_cent.trans (Subgroup.centralizer_le_normalizer (D : Set G)))
    rw [hDZ_bot, Subgroup.card_bot, mul_one] at hcard'
    exact hcard'
  have hcardDZ : Nat.card ↥(D ⊔ Z) = 2 ^ 8 := by
    rw [hcardM, hcardD, hcardZ]
    norm_num
  have hCeq : T ⊓ Subgroup.centralizer ({t} : Set G) = D ⊔ Z := by
    change T ⊓ Subgroup.centralizer ({t} : Set G) =
      (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range ⊔ Subgroup.zpowers t
    exact sec8t84d5_centralizer_eq_range_iota_sup_zpowers ht hsw1 hsw2 hcomm hinf hT0eq hTeq htT
  have hPt_cent : Pt ≤ Subgroup.centralizer ({t} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hPtc p hp
  have hPtC : Pt ≤ T ⊓ Subgroup.centralizer ({t} : Set G) := le_inf hPt hPt_cent
  have hZcent_t : Z ≤ Subgroup.centralizer ({t} : Set G) := by
    change Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set G)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; simp [hh]))
  have hZC : Z ≤ T ⊓ Subgroup.centralizer ({t} : Set G) :=
    le_inf (Subgroup.zpowers_le.mpr htT) hZcent_t
  have hPtZ_le : Pt ⊔ Z ≤ D ⊔ Z := by
    rw [← hCeq]
    exact sup_le hPtC hZC
  have hPtZnorm : Z ≤ Subgroup.normalizer (Pt : Set G) := by
    have hZc : Z ≤ Subgroup.centralizer (Pt : Set G) := by
      change Subgroup.zpowers t ≤ Subgroup.centralizer (Pt : Set G)
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hPtc p hp).symm
    exact hZc.trans (Subgroup.centralizer_le_normalizer (Pt : Set G))
  have hcardPtZ : Nat.card ↥(Pt ⊔ Z) = 2 ^ 8 := by
    have hcard' := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
        (A := Pt) (B := Z) hPtZnorm
    rw [hPtZ_bot, Subgroup.card_bot, mul_one] at hcard'
    rw [hcard', hcard, hcardZ]
    norm_num
  have hPtZ_eq : Pt ⊔ Z = D ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge hPtZ_le (by simp [hcardDZ, hcardPtZ])
  let M : Subgroup G := D ⊔ Z
  have hDMle : D ≤ M := le_sup_left
  have hZMle : Z ≤ M := le_sup_right
  have hPtMle : Pt ≤ M := by
    rw [show M = Pt ⊔ Z from hPtZ_eq.symm]
    exact le_sup_left
  have hDnZ : D ≤ Subgroup.normalizer (Z : Set G) :=
    hDZ_cent.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hZMnorm : (Z.subgroupOf M).Normal := by
    change (Z.subgroupOf (D ⊔ Z)).Normal
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hDnZ
  have hDdisj : Disjoint (D.subgroupOf M) (Z.subgroupOf M) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    have hxG : (x : G) ∈ D ⊓ Z :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    exact Subtype.ext (by simpa [hDZ_bot] using hxG)
  have hDcard : Nat.card ↥(D.subgroupOf M) * Nat.card ↥(Z.subgroupOf M) = Nat.card ↥M := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDMle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZMle).toEquiv]
    exact hcardM.symm
  have hPtdisj : Disjoint (Pt.subgroupOf M) (Z.subgroupOf M) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    have hxG : (x : G) ∈ Pt ⊓ Z :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    exact Subtype.ext (by simpa [hPtZ_bot] using hxG)
  have hPtcard : Nat.card ↥(Pt.subgroupOf M) * Nat.card ↥(Z.subgroupOf M) = Nat.card ↥M := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPtMle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZMle).toEquiv]
    have hcardMPt : Nat.card ↥M = Nat.card ↥Pt * Nat.card ↥Z := by
      have hcard' := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
          (A := Pt) (B := Z) hPtZnorm
      rw [hPtZ_bot, Subgroup.card_bot, mul_one, hPtZ_eq] at hcard'
      exact hcard'
    exact hcardMPt.symm
  have hDcomp : (D.subgroupOf M).IsComplement' (Z.subgroupOf M) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hDcard hDdisj
  have hPtcomp : (Pt.subgroupOf M).IsComplement' (Z.subgroupOf M) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hPtcard hPtdisj
  haveI : (Z.subgroupOf M).Normal := hZMnorm
  let eD : ↥M ⧸ (Z.subgroupOf M) ≃* ↥(D.subgroupOf M) := hDcomp.QuotientMulEquiv
  let eP : ↥M ⧸ (Z.subgroupOf M) ≃* ↥(Pt.subgroupOf M) := hPtcomp.QuotientMulEquiv
  let eDP : ↥(D.subgroupOf M) ≃* ↥(Pt.subgroupOf M) := eD.symm.trans eP
  let eDM : ↥(D.subgroupOf M) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDMle
  let ePtM : ↥(Pt.subgroupOf M) ≃* ↥Pt := Subgroup.subgroupOfEquivOfLe hPtMle
  let eS1D : ↥(T ⊓ Y1) ≃* ↥D := MonoidHom.ofInjective hφinj
  exact ⟨eS1D.trans (eDM.symm.trans (eDP.trans ePtM))⟩

end CFSG.OddStandard.SmallF3.Omega
