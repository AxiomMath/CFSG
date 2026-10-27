module

import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAFacts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XSpec

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dP sP)
open CFSG.RankThree.Native.F2 (validA_of_rep rep_invCand)
open scoped commutatorElement

theorem inv_mul_fix' {t g : Equiv.Perm (Fin 693)} {p : Fin 693} (h : t p = g p) :
    (t⁻¹ * g) p = p := by
  rw [Equiv.Perm.mul_apply, ← h, perm_inv_apply']

theorem conj_mem_of_gens {c : ChainData} {H : Subgroup (Equiv.Perm (Fin 693))}
    {g : Equiv.Perm (Fin 693)} (h : ∀ w ∈ c.gens, g * wP w * g⁻¹ ∈ H) :
    ∀ x ∈ c.grp, g * x * g⁻¹ ∈ H := by
  have hle : c.grp ≤ H.comap (MulAut.conj g).toMonoidHom := grp_le fun w hw => by
    simpa [MulAut.conj_apply] using h w hw
  intro x hx
  simpa [MulAut.conj_apply] using hle hx

theorem norm_of_all {c d : ChainData} (hc : c.GensOK) (hd : d.GensOK) {lv : Array Level}
    (hmem : ∀ {a : Array ℕ} {Y : Equiv.Perm (Fin 693)}, Rep 693 a Y →
      (Y ∈ d.grp ↔ siftA 693 lv d.B 0 a = true))
    (h : (c.O.all fun x => d.O.all fun g => siftA 693 lv d.B 0 (conjA 693 x g)) = true) :
    c.grp ≤ normalizer (d.grp : Set (Equiv.Perm (Fin 693))) :=
  grp_le fun w hw => mem_normalizer_grp (all_conj_iff hd hmem
    (validA_of_rep (rep_wA_gens hc hw)) (rep_wA_gens hc hw)
    (all_O_spec (p := fun x => d.O.all fun g => siftA 693 lv d.B 0 (conjA 693 x g)) h w hw))

theorem c11a_spec {b : Equiv.Perm (Fin 693)} (hb : b ∈ chZ2S.grp)
    (h : fixCard b = fixCard (gP 14)) : b = gP 14 := by
  have hz : Rep 693 gz (gP 14) := rep_gA tabs_check (by norm_num)
  obtain ⟨a, hB, hc⟩ := c11a_check b hb
  unfold c11aAt at hc
  rw [Bool.or_eq_true, bne_iff_ne] at hc
  rcases hc with hid | hne
  · exact eq_of_eqA hB hz hid
  · exact absurd (by rw [fixCnt_eq hB, fixCnt_eq hz, h]) hne

theorem z2s_word {y : Equiv.Perm (Fin 693)} (hy : y ∈ chZ2S.grp) : ∃ w ∈ z2sW, wP w = y := by
  have hreg : ∀ h ∈ chZ2S.grp, h 1 = 1 → h = 1 := fun h hh h1 => by
    obtain ⟨a, hX, hc⟩ := z2sKey_check h hh
    unfold z2sKeyAt at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
    rcases hc.1 with h' | he
    · exact absurd (by rw [hX.apply (by norm_num : 1 < 693)]; exact congrArg Fin.val h1) h'
    · exact eq_one_of_eqA hX he
  obtain ⟨a, hX, hc⟩ := z2sKey_check y hy
  unfold z2sKeyAt at hc
  rw [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at hc
  obtain ⟨w, hw, hk⟩ := hc.2
  have hl : ∀ k ∈ w, [k] ∈ chZ2S.gens ∧ k < 18 :=
    (by decide : ∀ w ∈ z2sW, ∀ k ∈ w, [k] ∈ chZ2S.gens ∧ k < 18) w hw
  have hr := rep_wA tabs_check w fun k hk => (hl k hk).2
  have hm := wP_mem_of_letters w fun k hk => (hl k hk).1
  have he : wP w 1 = y 1 := Fin.ext ((hr.apply (by norm_num : 1 < 693)).symm.trans
    (hk.trans (hX.apply (by norm_num : 1 < 693))))
  exact ⟨w, hw, inv_mul_eq_one.1 (hreg _ (mul_mem (inv_mem hm) hy) (inv_mul_fix' he))⟩

theorem c11Rej_spec {k : Array ℕ} {K : Equiv.Perm (Fin 693)} (hK : Rep 693 k K)
    (hr : c11RejW k = true) : K ∉ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) := by
  intro hn
  obtain ⟨idx, hidx, hgf⟩ := Array.any_eq_true.1 hr
  obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
  rw [hgw, Bool.not_eq_true'] at hgf
  obtain ⟨P, hP⟩ := exists_of_not_allLt hgf
  rw [List.any_eq_false] at hP
  have hG := rep_wA_gens gensOK_chZ2S hwm
  have hmem : K * wP w * K⁻¹ ∈ chZ2S.grp := (mem_normalizer_iff.1 hn _).1 (wP_mem_grp hwm)
  obtain ⟨b, hb, hbe⟩ := z2s_word hmem
  have hr := rep_wA tabs_check b ((by decide : ∀ w ∈ z2sW, ∀ k ∈ w, k < 18) b hb)
  apply hP b hb
  rw [beq_iff_eq, rep_get hG P, rep_get hK, rep_get hK P, rep_get hr, hbe]
  simp [Equiv.Perm.mul_apply]

theorem c11b_spec {k : Equiv.Perm (Fin 693)} (hk : k ∈ chK1.grp)
    (hn : k ∈ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693)))) : k ∈ chP2.grp := by
  obtain ⟨a, hK, hc⟩ := c11b_check k hk
  unfold c11bAt at hc
  rw [Bool.or_eq_true] at hc
  rcases hc with hr | hs
  · exact absurd hn (c11Rej_spec hK hr)
  · exact (mem_chP2_iff hK).2 hs

theorem rep_conjInv_w {w : List ℕ} (hw : ∀ k ∈ w, k < 18) {a : Array ℕ}
    {X : Equiv.Perm (Fin 693)} (hX : Rep 693 a X) :
    Rep 693 (conjInvA 693 (wA w) a) ((wP w)⁻¹ * X * wP w) := by
  have hr := rep_conjInvA (validA_of_rep (rep_wA tabs_check w hw)) hX
  rwa [permOfArr_eq_of_rep (rep_wA tabs_check w hw)] at hr

theorem i5_spec {s : Equiv.Perm (Fin 693)} (hs : s ∈ chS.grp)
    (h : (wP [16, 17, 16, 17])⁻¹ * s * wP [16, 17, 16, 17] ∈ chS.grp) : s ∈ chA1.grp := by
  have hg := i5Gen_check
  unfold i5GenCheck at hg
  rw [Bool.and_eq_true] at hg
  have hA : ∀ x ∈ chA1.grp, (wP [16, 17, 16, 17])⁻¹ * x * (wP [16, 17, 16, 17])⁻¹⁻¹ ∈ chS.grp :=
    conj_mem_of_gens fun w hw => by
      rw [inv_inv]
      exact (mem_chS_iff (rep_conjInv_w (by decide) (rep_wA_gens gensOK_chA1 hw))).2
        (all_O_spec (p := fun a => siftA 693 lvS chS.B 0 (conjInvA 693 (wA [16, 17, 16, 17]) a))
          hg.2 w hw)
  have hle : chS.grp ≤ chT1.grp ⊔ chA1.grp := grp_le fun w hw => by
    rcases (by decide : ∀ w ∈ chS.gens, w ∈ chT1.gens ∨ w ∈ chA1.gens) w hw with h1 | h1
    · exact mem_sup_left (wP_mem_grp h1)
    · exact mem_sup_right (wP_mem_grp h1)
  have hs' : s ∈ ((chT1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hle hs
  rw [coe_mul_of_left_le_normalizer_right _ _ (chT1_le_chK1.trans chK1_le_normalizer_A1)] at hs'
  obtain ⟨t, ht, a, ha, rfl⟩ := hs'
  have hta := hA a ha
  rw [inv_inv] at hta
  have htS : (wP [16, 17, 16, 17])⁻¹ * t * wP [16, 17, 16, 17] ∈ chS.grp := by
    have e : (wP [16, 17, 16, 17])⁻¹ * t * wP [16, 17, 16, 17] =
        ((wP [16, 17, 16, 17])⁻¹ * (t * a) * wP [16, 17, 16, 17]) *
          ((wP [16, 17, 16, 17])⁻¹ * a * wP [16, 17, 16, 17])⁻¹ := by group
    rw [e]
    exact mul_mem h (inv_mem hta)
  obtain ⟨b, hT, hc⟩ := i5_check t ht
  unfold i5At at hc
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with hn | hm
  · rw [(mem_chS_iff (rep_conjInv_w (by decide) hT)).1 htS] at hn
    exact absurd hn (by decide)
  · exact mul_mem ((mem_chA1_iff hT).2 hm) ha

theorem i8_spec {s : Equiv.Perm (Fin 693)} (hs : s ∈ chS.grp)
    (h : (wP [15, 17])⁻¹ * s * wP [15, 17] ∈ chS.grp) : s ∈ chA3.grp := by
  have hg := i8Gen_check
  unfold i8GenCheck at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := hg
  have hA : ∀ x ∈ chA3.grp, (wP [15, 17])⁻¹ * x * (wP [15, 17])⁻¹⁻¹ ∈ chS.grp :=
    conj_mem_of_gens fun w hw => by
      rw [inv_inv]
      exact (mem_chS_iff (rep_conjInv_w (by decide) (rep_wA_gens gensOK_chA3 hw))).2
        (all_O_spec (p := fun a => siftA 693 lvS chS.B 0 (conjInvA 693 (wA [15, 17]) a)) h2 w hw)
  have hN1 := norm_of_all gensOK_chX1 gensOK_chX3A3 mem_chX3A3_iff h3
  have hN3 := norm_of_all gensOK_chX3 gensOK_chA3 mem_chA3_iff h4
  have hle1 : chS.grp ≤ chX1.grp ⊔ chX3A3.grp := grp_le fun w hw => by
    rcases (by decide : ∀ w ∈ chS.gens, w ∈ chX1.gens ∨ w ∈ chX3A3.gens) w hw with h1 | h1
    · exact mem_sup_left (wP_mem_grp h1)
    · exact mem_sup_right (wP_mem_grp h1)
  have hle3 : chX3A3.grp ≤ chX3.grp ⊔ chA3.grp := grp_le fun w hw => by
    rcases (by decide : ∀ w ∈ chX3A3.gens, w ∈ chX3.gens ∨ w ∈ chA3.gens) w hw with h1 | h1
    · exact mem_sup_left (wP_mem_grp h1)
    · exact mem_sup_right (wP_mem_grp h1)
  have hs' : s ∈ ((chX1.grp ⊔ chX3A3.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hle1 hs
  rw [coe_mul_of_left_le_normalizer_right _ _ hN1] at hs'
  obtain ⟨x, hx, b, hb, rfl⟩ := hs'
  have hb' : b ∈ ((chX3.grp ⊔ chA3.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hle3 hb
  rw [coe_mul_of_left_le_normalizer_right _ _ hN3] at hb'
  obtain ⟨y, hy, a, ha, rfl⟩ := hb'
  have hta := hA a ha
  rw [inv_inv] at hta
  have hxyS : (wP [15, 17])⁻¹ * (x * y) * wP [15, 17] ∈ chS.grp := by
    have e : (wP [15, 17])⁻¹ * (x * y) * wP [15, 17] =
        ((wP [15, 17])⁻¹ * (x * (y * a)) * wP [15, 17]) *
          ((wP [15, 17])⁻¹ * a * wP [15, 17])⁻¹ := by group
    rw [e]
    exact mul_mem h (inv_mem hta)
  obtain ⟨c, d, hC, hD, hc⟩ := i8_check x hx y hy
  unfold i8At at hc
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with hn | hm
  · rw [(mem_chS_iff (rep_conjInv_w (by decide) (rep_compA hC hD))).1 hxyS] at hn
    exact absurd hn (by decide)
  · have e : x * (y * a) = x * y * a := (mul_assoc x y a).symm
    simp only at e ⊢
    rw [e]
    exact mul_mem ((mem_chA3_iff (rep_compA hC hD)).2 hm) ha

theorem i8b_spec {x : Equiv.Perm (Fin 693)} (hx : x ∈ chX3A3.grp)
    (h : (wP [4, 17])⁻¹ * x * wP [4, 17] ∈ chX3A3.grp) : x ∈ chA3.grp := by
  have hg := i8bGen_check
  unfold i8bGenCheck at hg
  rw [Bool.and_eq_true] at hg
  have hg8 := i8Gen_check
  unfold i8GenCheck at hg8
  simp only [Bool.and_eq_true] at hg8
  have hA : ∀ y ∈ chA3.grp, (wP [4, 17])⁻¹ * y * (wP [4, 17])⁻¹⁻¹ ∈ chX3A3.grp :=
    conj_mem_of_gens fun w hw => by
      rw [inv_inv]
      exact (mem_chX3A3_iff (rep_conjInv_w (by decide) (rep_wA_gens gensOK_chA3 hw))).2
        (all_O_spec (p := fun a => siftA 693 lvX3A3 chX3A3.B 0 (conjInvA 693 (wA [4, 17]) a))
          hg.2 w hw)
  have hN3 := norm_of_all gensOK_chX3 gensOK_chA3 mem_chA3_iff hg8.2
  have hle3 : chX3A3.grp ≤ chX3.grp ⊔ chA3.grp := grp_le fun w hw => by
    rcases (by decide : ∀ w ∈ chX3A3.gens, w ∈ chX3.gens ∨ w ∈ chA3.gens) w hw with h1 | h1
    · exact mem_sup_left (wP_mem_grp h1)
    · exact mem_sup_right (wP_mem_grp h1)
  have hx' : x ∈ ((chX3.grp ⊔ chA3.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hle3 hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hN3] at hx'
  obtain ⟨y, hy, a, ha, rfl⟩ := hx'
  have hta := hA a ha
  rw [inv_inv] at hta
  have hyS : (wP [4, 17])⁻¹ * y * wP [4, 17] ∈ chX3A3.grp := by
    have e : (wP [4, 17])⁻¹ * y * wP [4, 17] =
        ((wP [4, 17])⁻¹ * (y * a) * wP [4, 17]) * ((wP [4, 17])⁻¹ * a * wP [4, 17])⁻¹ := by
      group
    rw [e]
    exact mul_mem h (inv_mem hta)
  obtain ⟨b, hY, hc⟩ := i8b_check y hy
  unfold i8bAt at hc
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with hn | hm
  · rw [(mem_chX3A3_iff (rep_conjInv_w (by decide) hY)).1 hyS] at hn
    exact absurd hn (by decide)
  · exact mul_mem ((mem_chA3_iff hY).2 hm) ha

theorem c6_wit {l d : Array ℕ} {L D : Equiv.Perm (Fin 693)} (hL : Rep 693 l L) (hD : Rep 693 d D)
    (hw : (!(chA4.O.all fun g => eqA 693 (compA 693 (compA 693 l d) g)
      (compA 693 g (compA 693 l d)))) = true) :
    ∃ w ∈ chA4.gens, L * D * wP w ≠ wP w * (L * D) := by
  rw [Bool.not_eq_true', Array.all_eq_false] at hw
  obtain ⟨idx, hidx, hgf⟩ := hw
  obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
  rw [hgw] at hgf
  have hG := rep_wA_gens gensOK_chA4 hwm
  refine ⟨w, hwm, fun he => hgf ?_⟩
  exact (eqA_iff (rep_compA (rep_compA hL hD) hG) (rep_compA hG (rep_compA hL hD))).2 he

theorem c6_spec {l : Equiv.Perm (Fin 693)} (hl : l ∈ chLam.grp) {j : ℕ} (hj : j < 2)
    (h : ∀ w ∈ chA4.gens, l * sP ^ j * wP w = wP w * (l * sP ^ j)) : l = 1 ∧ j = 0 := by
  obtain ⟨a, hL, hc⟩ := c6_check l hl
  have hD : Rep 693 dArr[3 * j]! (sP ^ j) := by
    have := rep_dArr' (i := 0) (by norm_num) hj
    rwa [zero_add, pow_zero, one_mul] at this
  unfold c6At at hc
  rw [List.all_eq_true] at hc
  have hq := hc (3 * j) (by interval_cases j <;> simp)
  rw [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hq
  rcases hq with hw | ⟨hq0, hid⟩
  · obtain ⟨w, hwm, hne⟩ := c6_wit hL hD hw
    exact absurd (h w hwm) hne
  · exact ⟨eq_of_eqA hL rep_idA hid, by omega⟩

theorem c7_wit {y : Array ℕ} {Y : Equiv.Perm (Fin 693)} (hY : Rep 693 y Y)
    (hw : (!(lsGens.all fun g => siftA 693 lvA3 chA3.B 0 (commutatorA 693 y g))) = true) :
    (∃ w ∈ chLam.gens, ⁅Y, wP w⁆ ∉ chA3.grp) ∨ ∃ w ∈ chSig.gens, ⁅Y, wP w⁆ ∉ chA3.grp := by
  have hv := validA_of_rep hY
  rw [Bool.not_eq_true', lsGens, Array.all_append, Bool.and_eq_false_iff] at hw
  rcases hw with hw | hw
  · left
    rw [Array.all_eq_false] at hw
    obtain ⟨idx, hidx, hgf⟩ := hw
    obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
    rw [hgw] at hgf
    refine ⟨w, hwm, fun hm => hgf ?_⟩
    exact (mem_chA3_iff (rep_comm hv (validA_of_rep (rep_wA_gens gensOK_chLam hwm)) hY
      (rep_wA_gens gensOK_chLam hwm))).1 hm
  · right
    rw [Array.all_eq_false] at hw
    obtain ⟨idx, hidx, hgf⟩ := hw
    obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
    rw [hgw] at hgf
    refine ⟨w, hwm, fun hm => hgf ?_⟩
    exact (mem_chA3_iff (rep_comm hv (validA_of_rep (rep_wA_gens gensOK_chSig hwm)) hY
      (rep_wA_gens gensOK_chSig hwm))).1 hm

theorem A3_fix {x : Equiv.Perm (Fin 693)} (hx : x ∈ chA3.grp) {p : ℕ} (hp : p ∈ fixF)
    (hp' : p < 693) : x ⟨p, hp'⟩ = ⟨p, hp'⟩ := by
  have hle : chA3.grp ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) (⟨p, hp'⟩ : Fin 693) :=
    grp_le fun w hw => by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact (xFix_spec.1 ⟨p, hp'⟩).2 hp w hw
  have h := hle hx
  rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h

theorem c7Pt_wit {l s d g : Array ℕ} {L S D G : Equiv.Perm (Fin 693)} (hl : Rep 693 l L)
    (hs : Rep 693 s S) (hd : Rep 693 d D) (hg : Rep 693 g G) (h : c7PtW l s d g = true) :
    ⁅L * S * D, G⁆ ∉ chA3.grp := by
  intro hm
  obtain ⟨p, hp, hne⟩ := List.any_eq_true.1 h
  have hp' : p < 693 := (by decide : ∀ q ∈ fixF, q < 693) p hp
  have hr := rep_compA (rep_compA (rep_compA (rep_compA hl hs) hd) hg)
    (rep_compA (rep_compA (rep_compA (rep_invCand hd) (rep_invCand hs)) (rep_invCand hl))
      (rep_invCand hg))
  have e : L * S * D * G * (D⁻¹ * S⁻¹ * L⁻¹ * G⁻¹) = ⁅L * S * D, G⁆ := by
    rw [commutatorElement_def]
    group
  rw [e] at hr
  rw [bne_iff_ne, hr.apply hp', A3_fix hm hp hp'] at hne
  exact hne rfl

theorem c7Pt_wit' {l s d : Array ℕ} {L S D : Equiv.Perm (Fin 693)} (hl : Rep 693 l L)
    (hs : Rep 693 s S) (hd : Rep 693 d D) (hw : (lsGens.any fun g => c7PtW l s d g) = true) :
    (∃ w ∈ chLam.gens, ⁅L * S * D, wP w⁆ ∉ chA3.grp) ∨
      ∃ w ∈ chSig.gens, ⁅L * S * D, wP w⁆ ∉ chA3.grp := by
  rw [lsGens, Array.any_append, Bool.or_eq_true] at hw
  rcases hw with hw | hw
  · left
    obtain ⟨idx, hidx, hgf⟩ := Array.any_eq_true.1 hw
    obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
    rw [hgw] at hgf
    exact ⟨w, hwm, c7Pt_wit hl hs hd (rep_wA_gens gensOK_chLam hwm) hgf⟩
  · right
    obtain ⟨idx, hidx, hgf⟩ := Array.any_eq_true.1 hw
    obtain ⟨w, hwm, hgw⟩ := O_mem_gens hidx
    rw [hgw] at hgf
    exact ⟨w, hwm, c7Pt_wit hl hs hd (rep_wA_gens gensOK_chSig hwm) hgf⟩

theorem c7_spec {l s : Equiv.Perm (Fin 693)} (hl : l ∈ chLam.grp) (hs : s ∈ chSig.grp)
    {i j : ℕ} (hi : i < 3) (hj : j < 2)
    (hL : ∀ w ∈ chLam.gens, ⁅l * s * (dP ^ i * sP ^ j), wP w⁆ ∈ chA3.grp)
    (hS : ∀ w ∈ chSig.gens, ⁅l * s * (dP ^ i * sP ^ j), wP w⁆ ∈ chA3.grp) :
    l = 1 ∧ s = 1 ∧ j = 0 := by
  obtain ⟨a, b, hX, hY, hc0⟩ := c7_check l hl s hs
  have hD := rep_dArr' hi hj
  unfold c7At at hc0
  have hc := allLt_spec hc0 (show i + 3 * j < 6 by omega)
  rw [Bool.or_eq_true, Bool.or_eq_true] at hc
  rcases hc with (hp | hid) | hw
  · rcases c7Pt_wit' hX hY hD hp with ⟨w, hwm, hn'⟩ | ⟨w, hwm, hn'⟩
    · exact absurd (hL w hwm) hn'
    · exact absurd (hS w hwm) hn'
  · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hid
    obtain ⟨⟨hx1, hy1⟩, hq⟩ := hid
    exact ⟨eq_of_eqA hX rep_idA hx1, eq_of_eqA hY rep_idA hy1, by omega⟩
  · rcases c7_wit (rep_compA (rep_compA hX hY) hD) hw with ⟨w, hwm, hn'⟩ | ⟨w, hwm, hn'⟩
    · exact absurd (hL w hwm) hn'
    · exact absurd (hS w hwm) hn'

theorem nm_spec : chA1.grp ≤ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) ∧
    chA1.grp ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    chP2.grp ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
  have h := nm_check
  unfold nmCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := h
  exact ⟨norm_of_all gensOK_chA1 gensOK_chZ2S mem_chZ2S_iff h2,
    norm_of_all gensOK_chA1 gensOK_chA4 mem_chA4_iff h3,
    norm_of_all gensOK_chP2 gensOK_chA4 mem_chA4_iff h4⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
