module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightE1

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

open scoped commutatorElement

theorem sec38a2_card_VB₂_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.V ⊔ d.B₂ : Subgroup G) ≤ 2 * (2 ^ f) ^ 9 := by
  have h := Common.card_sup_mul_card_inf_eq (hd.sec38a1_B₂_le_normalizer_V hGMS)
  rw [hd.card_V, hd.card_B₂] at h
  have hpos : 0 < Nat.card (d.V ⊓ d.B₂ : Subgroup G) := Nat.card_pos
  have h2 : Nat.card (d.V ⊔ d.B₂ : Subgroup G) ≤
      Nat.card (d.V ⊔ d.B₂ : Subgroup G) * Nat.card (d.V ⊓ d.B₂ : Subgroup G) :=
    Nat.le_mul_of_pos_right _ hpos
  rw [h] at h2
  calc Nat.card (d.V ⊔ d.B₂ : Subgroup G) ≤ (2 ^ f) ^ 2 * (2 * (2 ^ f) ^ 7) := h2
    _ = 2 * (2 ^ f) ^ 9 := by ring

theorem sec38a2_le_normalizer_E (hp : d.CaseHyp) {Y : Subgroup G} (hY : Y ≤ d.E ⊔ d.T) :
    Y ≤ normalizer (d.E : Set G) :=
  hY.trans (sup_le le_normalizer (hp.hyp.T_le_normalizer_E hp.gms))

theorem sec38a2_card_eq (hp : d.CaseHyp) {Y : Subgroup G} (hY : Y ≤ d.E ⊔ d.T) :
    Nat.card Y * (2 ^ f) ^ 7 =
      Nat.card (d.E ⊓ Y : Subgroup G) * Nat.card ((d.E ⊔ Y) ⊓ d.T : Subgroup G) := by
  have hGMS := hp.gms
  have hd := hp.hyp
  have hTN : d.T ≤ normalizer (d.E : Set G) := hd.T_le_normalizer_E hGMS
  have hYN : Y ≤ normalizer (d.E : Set G) := sec38a2_le_normalizer_E hp hY
  set S := (d.E ⊔ Y) ⊓ d.T with hS
  have hSN : S ≤ normalizer (d.E : Set G) := inf_le_right.trans hTN
  have h1 := Common.card_sup_mul_card_inf_eq hYN
  have h2 := Common.card_sup_mul_card_inf_eq hSN
  have hsup : d.E ⊔ S = d.E ⊔ Y := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) (sup_le le_sup_left ?_)
    intro y hy
    obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hTN (hY hy)
    have hsS : s ∈ S := by
      refine ⟨?_, hs⟩
      have : s = e⁻¹ * (e * s) := by group
      rw [this]
      exact mul_mem (inv_mem (Subgroup.mem_sup_left he) : e⁻¹ ∈ d.E ⊔ Y) (mem_sup_right hy)
    exact mul_mem (mem_sup_left he) (mem_sup_right hsS)
  have hinf : d.E ⊓ S = d.A₂ := by
    refine le_antisymm (fun g hg => ?_) (fun a ha => ?_)
    · have : g ∈ d.E ⊓ d.T := ⟨hg.1, hg.2.2⟩
      rw [hd.sec38a1_E_inf_T hGMS] at this
      exact this
    · exact ⟨hd.A₂_le_E hGMS ha, mem_sup_left (hd.A₂_le_E hGMS ha), hd.P_le (d.A₂_le_P ha)⟩
  rw [hsup, hinf, d.card_A₂, hd.card_E hGMS] at h2
  rw [hd.card_E hGMS] at h1
  have hq : 0 < (2 ^ f) ^ 14 := by positivity
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  calc (2 ^ f) ^ 14 * (Nat.card Y * (2 ^ f) ^ 7)
      = ((2 ^ f) ^ 14 * Nat.card Y) * (2 ^ f) ^ 7 := by ring
    _ = (Nat.card (d.E ⊔ Y : Subgroup G) * Nat.card (d.E ⊓ Y : Subgroup G)) * (2 ^ f) ^ 7 := by
        rw [h1]
    _ = (Nat.card (d.E ⊔ Y : Subgroup G) * (2 ^ f) ^ 7) * Nat.card (d.E ⊓ Y : Subgroup G) := by
        ring
    _ = ((2 ^ f) ^ 14 * Nat.card S) * Nat.card (d.E ⊓ Y : Subgroup G) := by rw [h2]
    _ = (2 ^ f) ^ 14 * (Nat.card (d.E ⊓ Y : Subgroup G) * Nat.card S) := by ring

theorem sec38a2_sq_mem (hp : d.CaseHyp) {Y : Subgroup G} (hY : Y ≤ d.E ⊔ d.T)
    (hY2 : ∀ y ∈ Y, y * y ∈ d.V) : ∀ g ∈ (d.E ⊔ Y) ⊓ d.T, g * g ∈ d.A₂ := by
  intro g hg
  have hGMS := hp.gms
  have hd := hp.hyp
  obtain ⟨e1, he1, y, hy, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (sec38a2_le_normalizer_E hp hY) hg.1
  have hyN := sec38a2_le_normalizer_E hp hY hy
  have hmem : e1 * y * (e1 * y) ∈ d.E := by
    have e : e1 * y * (e1 * y) = e1 * (y * e1 * y⁻¹) * (y * y) := by group
    rw [e]
    exact mul_mem (mul_mem he1 ((mem_normalizer_iff.1 hyN e1).1 he1)) (d.V_le_E (hY2 y hy))
  have hT : e1 * y * (e1 * y) ∈ d.T := mul_mem hg.2 hg.2
  have h3 : e1 * y * (e1 * y) ∈ d.E ⊓ d.T := ⟨hmem, hT⟩
  rwa [hd.sec38a1_E_inf_T hGMS] at h3

theorem sec38a2_exists_comp (hp : d.CaseHyp) {Y : Subgroup G} (hY : Y ≤ d.E ⊔ d.T) {y : G}
    (hy : y ∈ Y) : ∃ e ∈ d.E, ∃ x ∈ (d.E ⊔ Y) ⊓ d.T, y = e * x := by
  obtain ⟨e, he, s, hs, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (hp.hyp.T_le_normalizer_E hp.gms) (hY hy)
  refine ⟨e, he, s, ⟨?_, hs⟩, rfl⟩
  have : s = e⁻¹ * (e * s) := by group
  rw [this]
  exact mul_mem (inv_mem (Subgroup.mem_sup_left he) : e⁻¹ ∈ d.E ⊔ Y) (mem_sup_right hy)

theorem sec38a2_comm_mem (hp : d.CaseHyp) {Y : Subgroup G} (hY : ElemAbMod d.V Y) {e x : G}
    (he : e ∈ d.E) (hy : e * x ∈ Y) {z : G} (hz : z ∈ d.E ⊓ Y) : ⁅z, x⁆ ∈ d.V := by
  have hGMS := hp.gms
  have hd := hp.hyp
  have h1 : ⁅z, e * x⁆ ∈ d.V := hY.2 z hz.2 _ hy
  have h2 : ⁅z, e⁆ ∈ d.V := (hd.elemAbMod_V_E hGMS).2 z hz.1 e he
  have e1 : ⁅z, x⁆ = e⁻¹ * (⁅z, e⁆⁻¹ * ⁅z, e * x⁆) * e := by
    simp only [commutatorElement_def]; group
  have hw : ⁅z, e⁆⁻¹ * ⁅z, e * x⁆ ∈ d.V := mul_mem (inv_mem h2) h1
  have hc : e * (⁅z, e⁆⁻¹ * ⁅z, e * x⁆) = (⁅z, e⁆⁻¹ * ⁅z, e * x⁆) * e :=
    hd.sec38a1_V_comm hGMS hw he
  have hc' : e⁻¹ * (⁅z, e⁆⁻¹ * ⁅z, e * x⁆) * e = ⁅z, e⁆⁻¹ * ⁅z, e * x⁆ := by
    calc e⁻¹ * (⁅z, e⁆⁻¹ * ⁅z, e * x⁆) * e = e⁻¹ * (e * (⁅z, e⁆⁻¹ * ⁅z, e * x⁆)) := by
          rw [mul_assoc, ← hc]
      _ = ⁅z, e⁆⁻¹ * ⁅z, e * x⁆ := by group
  rw [e1, hc']
  exact hw

theorem sec38a2_arith_b {q y s w : ℕ} (hq : 4 ≤ q) (h : y * q ^ 7 = w * s)
    (hs : s ≤ 2 * q ^ 10) (hw : w ≤ (q ^ 5) ^ 2) : y < q ^ 14 := by
  have hq0 : 0 < q := by omega
  have hpos : 0 < q ^ 7 := pow_pos hq0 7
  have h1 : y * q ^ 7 ≤ (2 * q ^ 13) * q ^ 7 := by
    calc y * q ^ 7 = w * s := h
      _ ≤ (q ^ 5) ^ 2 * (2 * q ^ 10) := Nat.mul_le_mul hw hs
      _ = (2 * q ^ 13) * q ^ 7 := by ring
  have h2 : y ≤ 2 * q ^ 13 := le_of_mul_le_mul_right h1 hpos
  have h4 : 2 * q ^ 13 < q ^ 14 := by
    have e : q ^ 14 = q * q ^ 13 := by ring
    have hp13 : 0 < q ^ 13 := pow_pos hq0 13
    rw [e]
    nlinarith
  omega

theorem sec38a2_arith_c {q y s w : ℕ} (hq : 4 ≤ q) (h : y * q ^ 7 = w * s)
    (hs : s ≤ 4 * q ^ 10) (hw : w ≤ (q ^ 4) ^ 2) : y < q ^ 14 := by
  have hq0 : 0 < q := by omega
  have hpos : 0 < q ^ 7 := pow_pos hq0 7
  have h1 : y * q ^ 7 ≤ (4 * q ^ 11) * q ^ 7 := by
    calc y * q ^ 7 = w * s := h
      _ ≤ (q ^ 4) ^ 2 * (4 * q ^ 10) := Nat.mul_le_mul hw hs
      _ = (4 * q ^ 11) * q ^ 7 := by ring
  have h2 : y ≤ 4 * q ^ 11 := le_of_mul_le_mul_right h1 hpos
  have h4 : 4 * q ^ 11 < q ^ 14 := by
    have e : q ^ 14 = q ^ 3 * q ^ 11 := by ring
    have hp11 : 0 < q ^ 11 := pow_pos hq0 11
    have h3 : 4 < q ^ 3 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 3)
    rw [e]
    nlinarith
  omega

theorem sec38a2_of_hyp (hp : d.CaseHyp) (h1 : d.Sec38a1) : d.Sec38a2 := by
  have hGMS := hp.gms
  have hd := hp.hyp
  intro Y hVY hYET hY
  have hq4 : 4 ≤ 2 ^ f := hd.four_le
  have hEcard : Nat.card d.E = (2 ^ f) ^ 14 := hd.card_E hGMS
  by_cases hYZ : Y ≤ (d.E ⊔ zpowers d.t : Subgroup G)
  · rcases hd.sec38a1_le_or_le hGMS hYZ hY with hYE | hYVB
    · have hle : Nat.card Y ≤ (2 ^ f) ^ 14 := by
        rw [← hEcard]
        exact Subgroup.card_le_of_le hYE
      refine ⟨hle, fun heq => ?_⟩
      exact Subgroup.eq_of_le_of_card_ge hYE (le_of_eq (hEcard.trans heq.symm))
    · have hc : Nat.card Y ≤ 2 * (2 ^ f) ^ 9 :=
        (Subgroup.card_le_of_le hYVB).trans (sec38a2_card_VB₂_le hGMS hd)
      have hlt : 2 * (2 ^ f) ^ 9 < (2 ^ f) ^ 14 := by
        generalize (2 ^ f : ℕ) = q at hq4 ⊢
        have h5 : 4 ≤ q ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left hq4 5)
        have e : q ^ 14 = q ^ 9 * q ^ 5 := by ring
        have hp9 : 0 < q ^ 9 := pow_pos (by omega) 9
        rw [e]
        nlinarith
      have hlt' : Nat.card Y < (2 ^ f) ^ 14 := lt_of_le_of_lt hc hlt
      exact ⟨hlt'.le, fun heq => absurd heq hlt'.ne⟩
  · have hcnt := sec38a2_card_eq hp hYET
    have hsq := sec38a2_sq_mem hp hYET hY.1
    have hlt : Nat.card Y < (2 ^ f) ^ 14 := by
      by_cases hS : (d.E ⊔ Y) ⊓ d.T ≤ d.tP
      · obtain ⟨y', hy'Y, hy'Z⟩ := SetLike.not_le_iff_exists.1 hYZ
        obtain ⟨e', he', x, hxS, rfl⟩ := sec38a2_exists_comp hp hYET hy'Y
        have hxB : x ∉ d.B₂ := by
          intro hxB
          apply hy'Z
          have hB2 : d.B₂ ≤ d.E ⊔ zpowers d.t :=
            sup_le le_sup_right (hd.A₂_le_E hGMS |>.trans le_sup_left)
          exact mul_mem (mem_sup_left he') (hB2 hxB)
        have h5 := hd.sec38e1_card_le_C1_sq hGMS hxS.2 (X := d.E ⊓ Y) inf_le_left
          (fun z hz => sec38a2_comm_mem hp hY he' hy'Y hz)
        have h6 := hd.sec38c1_card_le_in (hS hxS) hxB (sec38e1_C1_le_A₂ d x) (fun a ha => ha.2)
        have hW : Nat.card (d.E ⊓ Y : Subgroup G) ≤ ((2 ^ f) ^ 5) ^ 2 :=
          h5.trans (Nat.pow_le_pow_left h6 2)
        have hSc : Nat.card ((d.E ⊔ Y) ⊓ d.T : Subgroup G) ≤ 2 * (2 ^ f) ^ 10 := by
          have h7 := Subgroup.card_le_of_le hS
          have h8 : Nat.card d.tP = 2 * (2 ^ f) ^ 10 := by
            rw [Data.tP, hd.card_zpowers_sup d.P_le_L, d.card_P]
          rwa [h8] at h7
        exact sec38a2_arith_b hq4 hcnt hSc hW
      · obtain ⟨x', hx'S, hx'P⟩ := SetLike.not_le_iff_exists.1 hS
        obtain ⟨e1, he1, y1, hy1, hx'e⟩ :=
          exists_mul_of_mem_sup_of_le_normalizer (sec38a2_le_normalizer_E hp hYET) hx'S.1
        have hy1x : e1⁻¹ * x' = y1 := by rw [hx'e]; group
        have h5 := hd.sec38e1_card_le_C1_sq hGMS hx'S.2 (X := d.E ⊓ Y) inf_le_left
          (fun z hz => sec38a2_comm_mem hp hY (inv_mem he1) (hy1x ▸ hy1) hz)
        have h6 := hd.sec38c1_card_le_out hx'S.2 hx'P (sec38e1_C1_le_A₂ d x') (fun a ha => ha.2)
        have hW : Nat.card (d.E ⊓ Y : Subgroup G) ≤ ((2 ^ f) ^ 4) ^ 2 :=
          h5.trans (Nat.pow_le_pow_left h6 2)
        have hSc : Nat.card ((d.E ⊔ Y) ⊓ d.T : Subgroup G) ≤ 4 * (2 ^ f) ^ 10 := by
          have h7 := hd.card_le_four_mul_of_sq_mem (Y := (d.E ⊔ Y) ⊓ d.T) inf_le_right
            (fun g hg => d.A₂_le_P (hsq g hg))
          rwa [d.card_P] at h7
        exact sec38a2_arith_c hq4 hcnt hSc hW
    exact ⟨hlt.le, fun heq => absurd heq hlt.ne⟩

end Data

namespace CaseBParts

theorem sec38a2 : Sec38a2Statement :=
  fun _ _ _ _ _ _ _ _ hp h1 => Data.sec38a2_of_hyp hp h1

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5