module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenSingle
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOrbitGen
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isComponent_iff_eq_of_two_le_pRank (h72 : KFactOmegaNotCentral)
    (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)))
    {J : Subgroup (StarGroup p H)} (hJ : CFSG.IsComponent J) :
    ∀ D : Subgroup (StarGroup p H), CFSG.IsComponent D ↔ D = J := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hAcentJ : ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C →
      CFSG.pCore p (StarGroup p H) ≤ centralizer (C : Set (StarGroup p H)) :=
    fun C hC => (pCore_le_centralizer_layer h.prime H).trans
      (Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hC))
  intro D
  constructor
  · intro hD
    by_contra hne
    obtain ⟨A, hAle, hAab, hAcard⟩ :=
      CFSG.SectionRank.exists_pRank h.prime.one_lt (CFSG.pCore p (StarGroup p H))
    have hle := h.add_card_le_three h72 hH2 hp (A := A) hAab hAcard
      ({J, D} : Finset (Subgroup (StarGroup p H))) (by
        intro C hC
        have hC' : C = J ∨ C = D := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hC
        rcases hC' with h1 | h2
        · rw [h1]
          exact ⟨hJ, hAle.trans (hAcentJ J hJ)⟩
        · rw [h2]
          exact ⟨hD, hAle.trans (hAcentJ D hD)⟩)
    rw [Finset.card_pair (fun hJD : J = D => hne hJD.symm)] at hle
    omega
  · rintro rfl
    exact hJ

theorem pRank_pCore_eq_two (h72 : KFactOmegaNotCentral) (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)))
    {J : Subgroup (StarGroup p H)} (hJ : CFSG.IsComponent J) :
    CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨A, hAle, hAab, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank h.prime.one_lt (CFSG.pCore p (StarGroup p H))
  have hAcent : A ≤ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) :=
    hAle.trans (pCore_le_centralizer_layer h.prime H)
  have hle := h.add_card_le_three h72 hH2 hp (A := A) hAab hAcard
    ({J} : Finset (Subgroup (StarGroup p H))) (by
      intro C hC
      rw [Finset.mem_singleton] at hC
      subst hC
      exact ⟨hJ, hAcent.trans (Subgroup.centralizer_le
        (CFSG.LocalCores.component_le_layer hJ))⟩)
  rw [Finset.card_singleton] at hle
  omega

theorem pRank_component_of_two_le_pRank (h72 : KFactOmegaNotCentral) (h2 : KFactCenterRankTwo)
    (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)))
    {J : Subgroup (StarGroup p H)} (hJ : CFSG.IsComponent J) :
    CFSG.Open.pRank p J = 1 ∨
      (CFSG.Open.pRank p J = 2 ∧ p ∣ Nat.card (center ↥J)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨A, hAle, hAab, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank h.prime.one_lt (CFSG.pCore p (StarGroup p H))
  obtain ⟨B, hBle, hBab, hBcard⟩ := CFSG.SectionRank.exists_pRank h.prime.one_lt J
  set r : ℕ := CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) with hr_def
  set b : ℕ := CFSG.Open.pRank p J with hb_def
  have hAcentJ : A ≤ centralizer (J : Set (StarGroup p H)) :=
    (hAle.trans (pCore_le_centralizer_layer h.prime H)).trans
      (Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hJ))
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, a * c = c * a := by
    intro a ha c hc
    exact (Subgroup.mem_centralizer_iff.mp (hAcentJ ha) c (hBle hc)).symm
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp
    (IsPGroup.to_le (CFSG.Open.IsElemAbelian.isPGroup hAab) inf_le_left)
  have hTcard : Nat.card ((A ⊓ B).subgroupOf J) = p ^ c := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right.trans hBle : A ⊓ B ≤ J)).toEquiv]
    exact hc
  have hTle : (A ⊓ B).subgroupOf J ≤ center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hxmem : ((x : ↥J) : StarGroup p H) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
    simpa using Subgroup.mem_centralizer_iff.mp (hAcentJ hxmem)
      ((g : ↥J) : StarGroup p H) g.2
  have hc_le_one : c ≤ 1 := by
    by_contra hcgt
    push Not at hcgt
    have hTab : IsElemAbelian p ((A ⊓ B).subgroupOf J) :=
      CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono hAab inf_le_left) J
    have hcle := CFSG.SectionRank.le_pRank h.prime.one_lt hTle hTab hTcard
    have h2le : 2 ≤ CFSG.Open.pRank p (center ↥J) := by omega
    have h4 := h2 (StarGroup p H) h.isKGroup_star J hJ p h.prime h.ne_two h2le
    have h3 : CFSG.Open.pRank p J ≤ 3 :=
      (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans
        (h.pRank_star_le_three hH2 hp)
    omega
  have hABab : IsElemAbelian p (A ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAab hBab hcomm
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hABab)
  have hdc : d + c = r + b := by
    have hprod := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hcomm
    rw [hd, hc, hAcard, hBcard, ← pow_add, ← pow_add] at hprod
    exact Nat.pow_right_injective h.prime.two_le hprod
  have hd3 : d ≤ 3 :=
    (CFSG.SectionRank.le_pRank h.prime.one_lt le_top hABab hd).trans
      (h.pRank_star_le_three hH2 hp)
  have hrb : r + b - c ≤ 3 := by omega
  have hb_le_two : b ≤ 2 := by omega
  have hb_pos : 1 ≤ b := by
    obtain ⟨e, heJ, hord, -⟩ := h.exists_noncentral h72 hJ
    have hep : e ^ p = 1 := by simpa [hord] using pow_orderOf_eq_one e
    have hEab : IsElemAbelian p (Subgroup.zpowers e) := CFSG.Open.isElemAbelian_zpowers hep
    have hEcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
      rw [Nat.card_zpowers, hord, pow_one]
    exact CFSG.SectionRank.le_pRank h.prime.one_lt (Subgroup.zpowers_le.mpr heJ) hEab hEcard
  rcases eq_or_lt_of_le hb_pos with hb1 | hb2
  · left
    exact hb1.symm
  · right
    have hb_eq : b = 2 := by omega
    have hc_eq : c = 1 := by omega
    refine ⟨hb_eq, ?_⟩
    have hcardinf : Nat.card ↥(A ⊓ B) = p := by rw [hc, hc_eq, pow_one]
    have hTp : Nat.card ((A ⊓ B).subgroupOf J) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right.trans hBle : A ⊓ B ≤ J)).toEquiv]
      exact hcardinf
    have hdvd : p ∣ Nat.card (center ↥J) := by
      conv_lhs => rw [← hTp]
      exact Subgroup.card_dvd_of_le hTle
    exact hdvd

theorem single_component (h72 : KFactOmegaNotCentral) (h2 : KFactCenterRankTwo)
    (h5c : KFactCenterRankFive) (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)))
    (hL : pLayerIn p H ≠ ⊥) :
    CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
      ∃ J : Subgroup (StarGroup p H), CFSG.IsComponent J ∧
        (∀ D : Subgroup (StarGroup p H), CFSG.IsComponent D ↔ D = J) ∧
        CFSG.layer (StarGroup p H) = J ∧
        (CFSG.Open.pRank p J = 1 ∨ (CFSG.Open.pRank p J = 2 ∧ p ∣ Nat.card (center ↥J))) ∧
        (p = 5 → CFSG.Open.pRank p J = 1) := by
  obtain ⟨J, hJ⟩ := exists_isComponent_of_pLayerIn_ne_bot h.prime hL
  have hJu := h.isComponent_iff_eq_of_two_le_pRank h72 hH2 hp hR hJ
  have hR2 := h.pRank_pCore_eq_two h72 hH2 hp hR hJ
  have hpc := h.pRank_component_of_two_le_pRank h72 h2 hH2 hp hR hJ
  refine ⟨hR2, J, hJ, hJu, layer_eq_of_forall_isComponent_iff hJu, hpc, ?_⟩
  intro hp5
  rcases hpc with h1 | ⟨hJ2, hdvd⟩
  · exact h1
  · exfalso
    have h3 := h5c (StarGroup p H) h.isKGroup_star J hJ p h.prime (le_of_eq hp5.symm) hdvd
    omega

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
