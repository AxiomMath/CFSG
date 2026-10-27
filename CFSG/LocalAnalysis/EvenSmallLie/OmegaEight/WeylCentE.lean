module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylPerm
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCentCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

theorem dFix_spec {r : ℕ} (hr : r < 112) :
    ∃ m < 256, framePop m % 2 = 0 ∧ m ≠ 0 ∧ (signArrs[m]!)[r]! = r := by
  have h := allLt_spec dFix_check hr
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, he⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at he
  exact ⟨m, List.mem_range.1 hm, he.1.1, he.1.2, he.2⟩

theorem sOrbit_spec {r : ℕ} (hr : r < 240) (h112 : 112 ≤ r) :
    ∃ m < 256, framePop m % 2 = 0 ∧ (signArrs[m]!)[112]! = r := by
  have h := sOrbit_check
  rw [sOrbitCheck, List.all_eq_true] at h
  have := h r (List.mem_range.2 hr)
  rw [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at this
  rcases this with h1 | ⟨m, hm, he⟩
  · omega
  · simp only [Bool.and_eq_true, beq_iff_eq] at he
    exact ⟨m, List.mem_range.1 hm, he.1, he.2⟩

theorem frameRefl_spec (i : Fin 8) :
    ∃ a < 128, ∃ b < 128, (reflArrs[112 + a]!)[112 + b]! = keyPts.getD i 0 := by
  have h := allLt_spec frameRefl_check i.2
  rw [List.any_eq_true] at h
  obtain ⟨a, ha, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨b, hb, h⟩ := h
  exact ⟨a, List.mem_range.1 ha, b, List.mem_range.1 hb, by simpa using h⟩

theorem decode_mem_evenSub {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) :
    frameDecode m ∈ evenSub :=
  mem_evenSub.2 ((evenSub_iff_frameDecode m hm).2 he)

theorem signPerm_decode_apply {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) (r : Fin 240) :
    ((signPerm (frameDecode m) r : Fin 240) : ℕ) = (signArrs[m]!)[(r : ℕ)]! := by
  rw [signArrs_get hm, (rep_signArr (decode_mem_evenSub hm he)) r]

theorem signPerm_decode_mem {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) :
    signPerm (frameDecode m) ∈ eSub :=
  mem_eSub.2 ⟨_, decode_mem_evenSub hm he, rfl⟩

@[expose] def rS : Fin 240 := ⟨112, by norm_num⟩

theorem apply_comm {w e : Equiv.Perm (Fin 240)} (h : w * e = e * w) (r : Fin 240) :
    w (e r) = e (w r) := by
  rw [← Equiv.Perm.mul_apply, h, Equiv.Perm.mul_apply]

theorem le_apply_rS {w : Equiv.Perm (Fin 240)} (hc : ∀ e ∈ eSub, w * e = e * w) :
    112 ≤ (w rS : ℕ) := by
  by_contra h
  push Not at h
  obtain ⟨m, hm, he, h0, hfix⟩ := dFix_spec h
  have h1 : signPerm (frameDecode m) (w rS) = w rS :=
    Fin.ext (by rw [signPerm_decode_apply hm he]; exact hfix)
  have h2 : signPerm (frameDecode m) rS = rS := by
    have := apply_comm (hc _ (signPerm_decode_mem hm he)) rS
    rw [h1] at this
    exact w.injective this
  rcases d_facts.sFix 112 (by norm_num) with h' | h'
  · norm_num at h'
  · have h3 := signPerm_decode_apply hm he rS
    rw [h2] at h3
    exact h' m hm he h0 h3.symm

theorem eq_one_of_comm_eSub {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hc : ∀ e ∈ eSub, w * e = e * w) (h0 : w rS = rS) : w = 1 := by
  have hS : ∀ t : Fin 240, 112 ≤ (t : ℕ) → w t = t := by
    intro t ht
    obtain ⟨m, hm, he, hmt⟩ := sOrbit_spec t.2 ht
    have ht' : signPerm (frameDecode m) rS = t :=
      Fin.ext (by rw [signPerm_decode_apply hm he]; exact hmt)
    rw [← ht', apply_comm (hc _ (signPerm_decode_mem hm he)), h0]
  refine eq_one_of_fixes_frame hw fun i => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := frameRefl_spec i
  have hb' : b + 112 < 240 := by omega
  have ha' : a + 112 < 240 := by omega
  have e1 : (⟨frameRoot i, frameRoot_lt i⟩ : Fin 240) =
      refl (112 + a) ⟨112 + b, by omega⟩ := by
    refine Fin.ext ?_
    show frameRoot i = _
    have h1 := (rep_refl (by omega : 112 + a < 240)).apply (by omega : 112 + b < 240)
    rw [← reflArrs_get (by omega), hab, keyPts_getD] at h1
    exact h1
  have hconj := refl_conj hw ⟨112 + a, by omega⟩
  rw [e1]
  have hwa : w ⟨112 + a, by omega⟩ = ⟨112 + a, by omega⟩ := hS _ (by simp)
  have hwb : w ⟨112 + b, by omega⟩ = ⟨112 + b, by omega⟩ := hS _ (by simp)
  rw [hwa] at hconj
  have := congrArg (fun g => g (w ⟨112 + b, by omega⟩)) hconj
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
  rw [hwb] at this
  exact this

theorem eSub_comm {e f : Equiv.Perm (Fin 240)} (he : e ∈ eSub) (hf : f ∈ eSub) :
    e * f = f * e := by
  obtain ⟨v, hv, rfl⟩ := mem_eSub.1 he
  obtain ⟨u, hu, rfl⟩ := mem_eSub.1 hf
  rw [← signPerm_add hv hu, ← signPerm_add hu hv, add_comm]

theorem centralizer_eSub {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hc : ∀ e ∈ eSub, w * e = e * w) : w ∈ eSub := by
  obtain ⟨m, hm, he, hmt⟩ := sOrbit_spec (w rS).2 (le_apply_rS hc)
  set e := signPerm (frameDecode m)
  have hemem : e ∈ eSub := signPerm_decode_mem hm he
  have hEw : e⁻¹ * w ∈ wE8 := mul_mem (inv_mem (wPlus_le (eSub_le_wPlus hemem))) hw
  have hc' : ∀ f ∈ eSub, e⁻¹ * w * f = f * (e⁻¹ * w) := by
    intro f hf
    rw [mul_assoc, hc f hf, ← mul_assoc, eSub_comm (inv_mem hemem) hf, mul_assoc]
  have h0 : (e⁻¹ * w) rS = rS := by
    have : e rS = w rS := Fin.ext (by rw [signPerm_decode_apply hm he]; exact hmt)
    rw [Equiv.Perm.mul_apply, ← this, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have h1 := eq_one_of_comm_eSub hEw hc' h0
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact hemem

end CFSG.EvenSmallLie.OmegaEight.Weyl
