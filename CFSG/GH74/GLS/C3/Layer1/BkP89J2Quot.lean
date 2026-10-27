module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Core
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Stmt

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.TwoThin
open CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev zCof (v : G) : Mb (centralizer ({v} : Set G)) :=
  barMk ↥(centralizer ({v} : Set G)) ⟨v, v_mem_cent v⟩

omit [Finite G] in
theorem zCof_mem_center (v : G) : zCof v ∈ center (Mb (centralizer ({v} : Set G))) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨c, rfl⟩ := barMk_surjective y
  show barMk _ c * barMk _ ⟨v, v_mem_cent v⟩ = barMk _ ⟨v, v_mem_cent v⟩ * barMk _ c
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)

namespace P89Std

variable {M W Q : Subgroup G} {v : G} {Ebar : Subgroup (Mb M)}
variable (h : P89Std M W Q v Ebar)
include h

theorem zC_two : orderOf (zCof v) = 2 :=
  orderOf_barMk ((Subgroup.orderOf_mk v (v_mem_cent v)).trans h.v_two)

theorem Sb_syl : IsSylowOf 2 (imgM (centralizer ({v} : Set G)) W) ⊤ := by
  have hWC : IsSylowOf 2 W (centralizer ({v} : Set G)) := h.W_syl.of_le h.W_le_C le_top
  have := isSylowOf_imgM_of_le (le_refl (centralizer ({v} : Set G))) hWC
  rwa [imgM_top] at this

theorem card_Sb : Nat.card ↥(imgM (centralizer ({v} : Set G)) W) = 2 ^ 7 := by
  obtain ⟨e⟩ := equiv_imgM h.W_le_C h.W_pGroup
  rw [← Nat.card_congr e.toEquiv, h.card_W]

theorem Sb_center : ∀ s ∈ imgM (centralizer ({v} : Set G)) W,
    (∀ t ∈ imgM (centralizer ({v} : Set G)) W, s * t = t * s) → s = 1 ∨ s = zCof v := by
  intro s hs hsc
  obtain ⟨w, hwW, rfl⟩ := mem_imgM_iff.1 hs
  have hcomm : ∀ w' ∈ W0 M W Ebar, (w : G) * w' = w' * w := by
    intro w' hw'
    have hw'W : w' ∈ W := W0_le_W hw'
    have hw'C : w' ∈ centralizer ({v} : Set G) := h.W_le_C hw'W
    have h1 := hsc (barMk ↥(centralizer ({v} : Set G)) ⟨w', hw'C⟩)
      (mem_imgM_iff.2 ⟨⟨w', hw'C⟩, hw'W, rfl⟩)
    rw [← map_mul, ← map_mul] at h1
    have hwwW : (w : G) * w' ∈ W := W.mul_mem hwW hw'W
    have hwwW' : w' * (w : G) ∈ W := W.mul_mem hw'W hwW
    exact eq_of_barMk_eq (M := centralizer ({v} : Set G)) h.W_le_C h.W_pGroup hwwW hwwW' h1
  rcases h.cent_W0_in_W w hwW (fun y hy => hcomm y hy) with h1 | h1
  · left
    have : w = 1 := Subtype.ext h1
    rw [this, map_one]
  · right
    have : w = ⟨v, v_mem_cent v⟩ := Subtype.ext h1
    rw [this]

theorem eq_one_or_v_of_barMk {w : G} (hwW : w ∈ W)
    (hw : barMk ↥M ⟨w, h.W_le hwW⟩ = 1 ∨ barMk ↥M ⟨w, h.W_le hwW⟩ = h.vb) : w = 1 ∨ w = v := by
  rcases hw with h1 | h1
  · left
    exact eq_of_barMk_eq h.W_le h.W_pGroup hwW W.one_mem (by rw [h1]; exact (map_one _).symm)
  · right
    exact eq_of_barMk_eq h.W_le h.W_pGroup hwW h.v_mem h1

theorem W0_sq : ∀ w ∈ W0 M W Ebar, w * w = 1 ∨ w * w = v := by
  intro w hw
  obtain ⟨hwW, hwM, hwE⟩ := mem_W0_iff.1 hw
  have hww : w * w ∈ W := W.mul_mem hwW hwW
  refine h.eq_one_or_v_of_barMk hww ?_
  have h1 : (⟨w * w, h.W_le hww⟩ : ↥M) = ⟨w, hwM⟩ * ⟨w, hwM⟩ := rfl
  rw [h1, map_mul]
  exact h.facts.sq_mem _ hwE

theorem W0_comm : ∀ w ∈ W0 M W Ebar, ∀ w' ∈ W0 M W Ebar, ⁅w, w'⁆ = 1 ∨ ⁅w, w'⁆ = v := by
  intro w hw w' hw'
  obtain ⟨hwW, hwM, hwE⟩ := mem_W0_iff.1 hw
  obtain ⟨hw'W, hw'M, hw'E⟩ := mem_W0_iff.1 hw'
  have hc : ⁅w, w'⁆ ∈ W := by
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem hwW hw'W) (W.inv_mem hwW)) (W.inv_mem hw'W)
  refine h.eq_one_or_v_of_barMk hc ?_
  have h1 : (⟨⁅w, w'⁆, h.W_le hc⟩ : ↥M) = ⁅(⟨w, hwM⟩ : ↥M), (⟨w', hw'M⟩ : ↥M)⁆ := rfl
  rw [h1, map_commutatorElement]
  exact h.facts.comm_mem _ hwE _ hw'E

omit [Finite G] in
theorem zC_mem_Vb : zCof v ∈ imgM (centralizer ({v} : Set G)) (W0 M W Ebar) :=
  mem_imgM_iff.2 ⟨⟨v, v_mem_cent v⟩, h.v_mem_W0, rfl⟩

theorem card_Vb : Nat.card ↥(imgM (centralizer ({v} : Set G)) (W0 M W Ebar)) = 32 := by
  obtain ⟨e⟩ := equiv_imgM ((W0_le_W).trans h.W_le_C) h.W0_pGroup
  rw [← Nat.card_congr e.toEquiv, h.card_W0]

theorem Vb_sq_comm : ∀ x ∈ imgM (centralizer ({v} : Set G)) (W0 M W Ebar),
    x * x ∈ zpowers (zCof v) ∧
      ∀ y ∈ imgM (centralizer ({v} : Set G)) (W0 M W Ebar), ⁅x, y⁆ ∈ zpowers (zCof v) := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_imgM_iff.1 hx
  refine ⟨?_, fun y hy => ?_⟩
  · have h1 : barMk ↥(centralizer ({v} : Set G)) w * barMk ↥(centralizer ({v} : Set G)) w =
        barMk ↥(centralizer ({v} : Set G)) (⟨(w : G) * w, (centralizer ({v} : Set G)).mul_mem w.2 w.2⟩) :=
      (map_mul _ _ _).symm
    rw [h1]
    rcases h.W0_sq _ hw with h2 | h2
    · have : (⟨(w : G) * w, (centralizer ({v} : Set G)).mul_mem w.2 w.2⟩ : ↥(centralizer ({v} : Set G))) = 1 :=
        Subtype.ext h2
      rw [this, map_one]
      exact one_mem _
    · have : (⟨(w : G) * w, (centralizer ({v} : Set G)).mul_mem w.2 w.2⟩ : ↥(centralizer ({v} : Set G))) =
          ⟨v, v_mem_cent v⟩ := Subtype.ext h2
      rw [this]
      exact Subgroup.mem_zpowers _
  · obtain ⟨w', hw', rfl⟩ := mem_imgM_iff.1 hy
    have hcC : ⁅(w : G), (w' : G)⁆ ∈ centralizer ({v} : Set G) := by
      rw [commutatorElement_def]
      exact (centralizer ({v} : Set G)).mul_mem
        ((centralizer ({v} : Set G)).mul_mem
          ((centralizer ({v} : Set G)).mul_mem w.2 w'.2) ((centralizer ({v} : Set G)).inv_mem w.2))
        ((centralizer ({v} : Set G)).inv_mem w'.2)
    have h1 : ⁅barMk ↥(centralizer ({v} : Set G)) w, barMk ↥(centralizer ({v} : Set G)) w'⁆ =
        barMk ↥(centralizer ({v} : Set G)) (⟨⁅(w : G), (w' : G)⁆, hcC⟩) := by
      rw [← map_commutatorElement]
      rfl
    rw [h1]
    rcases h.W0_comm _ hw _ hw' with h2 | h2
    · have : (⟨⁅(w : G), (w' : G)⁆, hcC⟩ : ↥(centralizer ({v} : Set G))) = 1 := Subtype.ext h2
      rw [this, map_one]
      exact one_mem _
    · have : (⟨⁅(w : G), (w' : G)⁆, hcC⟩ : ↥(centralizer ({v} : Set G))) =
          ⟨v, v_mem_cent v⟩ := Subtype.ext h2
      rw [this]
      exact Subgroup.mem_zpowers _

noncomputable def psiY : ↥(normalizer (W0 M W Ebar : Set G)) →* Mb (centralizer ({v} : Set G)) :=
  (barMk ↥(centralizer ({v} : Set G))).comp
    (Subgroup.inclusion (h.normalizer_W0_le_cent))

@[expose] noncomputable def Pperf : Subgroup (Mb (centralizer ({v} : Set G))) :=
  (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G))).map h.psiY

theorem Pperf_perfect : ⁅h.Pperf, h.Pperf⁆ = h.Pperf := by
  have hp := Subgroup.isPerfect_iff.1 (CFSG.perfect_residual_characterization (G := ↥(normalizer (W0 M W Ebar : Set G)))).2.2.1
  unfold Pperf
  rw [← Subgroup.map_commutator, hp]

theorem three_dvd_card_Pperf : 3 ∣ Nat.card ↥h.Pperf := by
  have hYM : normalizer (W0 M W Ebar : Set G) ≤ M := h.normalizer_W0_le_M
  have hY' : imgM M (normalizer (W0 M W Ebar : Set G)) = centralizer ({h.vb} : Set (Mb M)) := by
    have := h.imgM_N0
    rwa [inf_eq_left.2 hYM] at this
  have hperfC : Group.IsPerfect ↥(imgM M (normalizer (W0 M W Ebar : Set G))) := by
    rw [Subgroup.isPerfect_iff, hY']
    exact h.facts.perfect
  have hmapTop : (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G))).map (toImgM hYM) = ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
      (toImgM hYM) (toImgM_surjective hYM)
  have h1 := Subgroup.card_ker_mul_card_range
    (h.psiY.domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G))))
  have h2 := Subgroup.card_ker_mul_card_range
    ((toImgM hYM).domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G))))
  have hr1 : (h.psiY.domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G)))).range =
      h.Pperf := by
    ext x
    simp only [MonoidHom.mem_range, Pperf, Subgroup.mem_map, MonoidHom.domRestrict_apply]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hr2 : ((toImgM hYM).domRestrict
      (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G)))).range = ⊤ := by
    rw [← hmapTop]
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.domRestrict_apply]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : (h.psiY.domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G)))).ker ≤
      ((toImgM hYM).domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G)))).ker := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd ⊢
    have h3 : barMk ↥(centralizer ({v} : Set G)) (Subgroup.inclusion h.normalizer_W0_le_cent (d : ↥(normalizer (W0 M W Ebar : Set G)))) = 1 := hd
    have h4 := (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h3
    have h5 : ((d : ↥(normalizer (W0 M W Ebar : Set G))) : G) ∈ pPrimeCoreOf 2 M := h.U1_le_R h4
    exact (mem_ker_toImgM hYM (d : ↥(normalizer (W0 M W Ebar : Set G)))).2 h5
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
  rw [hr1] at h1
  rw [hr2, Subgroup.card_top] at h2
  have hcardC : Nat.card ↥(imgM M (normalizer (W0 M W Ebar : Set G))) = 1920 := by
    rw [hY']
    exact h.facts.card_cent
  rw [hcardC] at h2
  have hpos : 0 < Nat.card ↥((h.psiY.domRestrict (CFSG.perfectResidual ↥(normalizer (W0 M W Ebar : Set G)))).ker) :=
    Nat.card_pos
  have hP : Nat.card ↥h.Pperf = m * 1920 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1, ← h2, hm]
    ring
  rw [hP]
  exact Dvd.dvd.mul_left (by norm_num) _

theorem pCore_eq (hnot : ¬ centralizer ({v} : Set G) ≤ M) :
    CFSG.pCore 2 (Mb (centralizer ({v} : Set G))) = zpowers (zCof v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf (zCof v) = 2 := h.zC_two
  have hzc := zCof_mem_center v
  have hnormZ : (zpowers (zCof v)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h1 := Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hzc k) g
    rw [h1, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hcardZ : Nat.card ↥(zpowers (zCof v)) = 2 := by rw [Nat.card_zpowers, hz2]
  have hpZ : IsPGroup 2 ↥(zpowers (zCof v)) := IsPGroup.of_card (n := 1) (by rw [hcardZ]; norm_num)
  have hle : zpowers (zCof v) ≤ CFSG.pCore 2 (Mb (centralizer ({v} : Set G))) :=
    le_sSup ⟨hnormZ, hpZ⟩
  have hN : (CFSG.pCore 2 (Mb (centralizer ({v} : Set G)))).Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 ↥(CFSG.pCore 2 (Mb (centralizer ({v} : Set G)))) := CFSG.pCore_isPGroup
  have hcard := h.card_normal_two_le hnot _ hN hN2 (hle (Subgroup.mem_zpowers _))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ]; exact hcard)).symm

theorem false_of_B_p810_J2 (hB : B_p810_J2) (hG : C3Hyp G) (hnot : ¬ centralizer ({v} : Set G) ≤ M) :
    False := by
  have hgen : Gen4 (Mb (centralizer ({v} : Set G))) :=
    Gen4.quotient _ (Gen4.subgroup (centralizer ({v} : Set G)) hG.gen4)
  have hcomp : ∀ J : Subgroup (Mb (centralizer ({v} : Set G))), CFSG.IsComponent J →
      InC2 ↥J ∨ InU2 ↥J := fun J hJ => hG.lt2o.2 v h.v_two J hJ
  exact hB (Mb (centralizer ({v} : Set G))) hgen hcomp (zCof v) h.zC_two (zCof_mem_center v)
    (h.pCore_eq hnot) (CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥(centralizer ({v} : Set G)))
    (imgM (centralizer ({v} : Set G)) W) h.Sb_syl h.card_Sb h.Sb_center
    (imgM (centralizer ({v} : Set G)) (W0 M W Ebar)) (imgM_mono W0_le_W) h.zC_mem_Vb h.card_Vb h.Vb_sq_comm
    h.Pperf h.Pperf_perfect h.three_dvd_card_Pperf

end P89Std

end CFSG.GH74.GLS.Th2.P85.Sp
