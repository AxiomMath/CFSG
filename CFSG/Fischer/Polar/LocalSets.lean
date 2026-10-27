
module

public import CFSG.Fischer.Polar.LocalSetsBase

public import CFSG.Fischer.Polar.Lines
public import CFSG.Fischer.Polar.Search
public import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Data.CFSGNative.F4.T46Simple
public import CFSG.Fischer.UnitaryAction
public import Certificates.Data.CFSGNative.Fi22.Local
public import Certificates.Data.Kernel.Fi22.Orb

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native

local notation "PT" => perpTab ()
local notation "LT" => lineTab (perpTab ())
local notation "LAM" => lamTab ()
local notation "WS" => gWords ()
local notation "CT" => mkCtx (perpTab ()) (gWords ()) (lamTab ())

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs perpTab
  perpLists lineTab lamTab gWords hypEnum

theorem hypFacts : HypFacts := by
  have h := hyp_certificate
  unfold hypCertificate hypChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem word_facts {x : ℕ} (hx : x < 693) :
    (∀ p ∈ WS[x]!, p < 693) ∧ ap (tvWordTab WS[x]!) 0 = x ∧
      invOK 693 (tvWordTab WS[x]!) ((CT).gI[x]!) = true := by
  have h := hypFacts.words
  unfold wordsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have h1 := (allIn_eq_true.1 h.2) x (Nat.zero_le _) hx
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem rep_gx (x : Fin 693) : Rep 693 (tvWordTab WS[x.val]!) (gx x) :=
  rep_wordTab _ (word_facts x.2).1

theorem gx_zero (x : Fin 693) : gx x 0 = x := by
  apply Fin.ext
  have h := (rep_gx x) 0 (by norm_num)
  rw [(word_facts x.2).2.1, idx_of_lt _ (by norm_num), Equiv.Perm.smul_def,
    show (⟨0, by norm_num⟩ : Fin 693) = 0 from rfl] at h
  exact h.symm

theorem rep_gI (x : Fin 693) : Rep 693 ((CT).gI[x.val]!) (gx x)⁻¹ :=
  (rep_gx x).inv_of_invOK (word_facts x.2).2.2

theorem ctxOK_hypCtx :
    CtxOK CT where
  perpT x y := by rw [hypCtx_P]; exact perpTab_spec x y
  pl x y := by rw [hypCtx_pl]; exact mem_perpLists
  lamIdx a ha j := by rw [hypCtx_lamIdx ha, mem_filterRange, hypCtx_lam]
  gI x hx y hy := by
    rw [rep_gI ⟨x, hx⟩ y hy]
    exact idx_lt _ hy

theorem lamSel_get_lt {i : ℕ} (hi : i < 5) :
    (lamSel ())[i]! < 693 ∧ (lamSel ())[i]! ≠ 0 ∧ (PT[0]!)[(lamSel ())[i]!]! = true := by
  have h := hypFacts.lam
  unfold lamOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.1.1.2) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem lam_facts {j : ℕ} (hj : j < 1024) :
    (LAM[j]!)[0]! = true ∧ (∀ z < 693, (LAM[j]!)[z]! = true → (PT[0]!)[z]! = true) ∧
      ∀ y < 693, (PT[0]!)[y]! = true → y ≠ 0 →
        ∃ z ∈ LT[y]!, z ≠ 0 ∧ (LAM[j]!)[z]! = true := by
  have h := hypFacts.lam
  unfold lamOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have h1 := (allIn_eq_true.1 h.2) j (Nat.zero_le _) hj
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨h0, hsub⟩, hline⟩ := h1
  refine ⟨h0, fun z hz hzj => ?_, fun y hy hpy hy0 => ?_⟩
  · have := (allIn_eq_true.1 hsub) z (Nat.zero_le _) hz
    rw [hzj, Bool.not_true, Bool.false_or] at this
    exact this
  · have := (allIn_eq_true.1 hline) y (Nat.zero_le _) hy
    have hy0' : (y == 0) = false := beq_eq_false_iff_ne.2 hy0
    rw [hpy, hy0', Bool.not_true, Bool.false_or, Bool.false_or, Array.any_eq_true'] at this
    obtain ⟨z, hz, hzz⟩ := this
    rw [Bool.and_eq_true, bne_iff_ne] at hzz
    exact ⟨z, hz, hzz.1, hzz.2⟩

theorem exists_lam_of_zero_mem
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O)
    (h0 : (0 : Fin 693) ∈ O) :
    ∃ j < 1024, ∀ z : Fin 693, perp 0 z → (z ∈ O ↔ (LAM[j]!)[z.val]! = true) := by
  have hsel : ∀ i < 5, ∃ k < 4, ∃ a : Fin 693, a ∈ O ∧
      a.val = (lineC 0 (lamSel ())[i]!)[1 + k]! := by
    intro i hi
    obtain ⟨hlt, hne, hp⟩ := lamSel_get_lt hi
    set s : Fin 693 := ⟨(lamSel ())[i]!, hlt⟩
    have hs0 : (0 : Fin 693) ≠ s := fun h => hne (congrArg Fin.val h).symm
    have hps : perp 0 s := (perpTab_spec 0 s).1 hp
    obtain ⟨a, haL, haO, ha0⟩ := hO.exists_ne (isLine_lineThru hs0 hps)
      (left_mem_lineThru 0 s) h0
    rw [mem_lineThru_iff hs0 hps, Fin.val_zero] at haL
    obtain ⟨k, hk, hka⟩ := Array.mem_iff_getElem.1 haL
    have hsize : (lineC 0 s.val).size = 5 := by
      have := lineC_eq 0 s
      rw [Fin.val_zero] at this
      rw [this]
      rfl
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply ha0
      apply Fin.ext
      rw [← hka, ← getElem!_pos _ 0 hk, lineC_zero_get s]
      rfl
    refine ⟨k - 1, by omega, a, haO, ?_⟩
    rw [show 1 + (k - 1) = k by omega, getElem!_pos _ k hk, hka]
  choose! d hd a haO hda using hsel
  set j := d 0 + 4 * d 1 + 16 * d 2 + 64 * d 3 + 256 * d 4 with hjdef
  have h0' := hd 0 (by norm_num)
  have h1' := hd 1 (by norm_num)
  have h2' := hd 2 (by norm_num)
  have h3' := hd 3 (by norm_num)
  have h4' := hd 4 (by norm_num)
  have hj : j < 1024 := by omega
  have hdig : ∀ i < 5, j / 4 ^ i % 4 = d i := by
    intro i hi
    interval_cases i <;> simp only [Nat.reducePow] <;> omega
  have hstart : ∀ p : Fin 693,
      (lamStart ((lamSel ()).map (lineC 0)) j)[p.val]! = true → p ∈ O := by
    intro p hp
    unfold lamStart at hp
    rw [getElem!_pos _ p.val (by simp), Array.getElem_ofFn] at hp
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at hp
    rcases hp with hp | ⟨i, hi, hpi⟩
    · rw [show p = 0 from Fin.ext hp]
      exact h0
    · have hpe : p = a i := by
        apply Fin.ext
        rw [hda i hi, ← hdig i hi, hpi, lamSel_map_get hi]
      rw [hpe]
      exact haO i hi
  have hlamO : ∀ p : Fin 693, (LAM[j]!)[p.val]! = true → p ∈ O := by
    rw [lam_get hj]
    exact clIter_sound hO.closed 3 _ hstart
  obtain ⟨hl0, -, hlline⟩ := lam_facts hj
  refine ⟨j, hj, fun z hz => ⟨fun hzO => ?_, hlamO z⟩⟩
  by_cases hz0 : z = 0
  · rw [hz0]
    exact hl0
  · obtain ⟨z', hz', hz'0, hz'j⟩ := hlline z.val z.2 ((perpTab_spec 0 z).2 hz)
      (fun h => hz0 (Fin.ext h))
    rw [lineTab_zero hz] at hz'
    have h0z : (0 : Fin 693) ≠ z := Ne.symm hz0
    have hlt0z : (0 : Fin 693) < z := lt_of_le_of_ne (Fin.zero_le _) h0z
    have hz'lt : z' < 693 := (lineC_facts hlt0z hz).2.1 z' (by rwa [Fin.val_zero])
    set w : Fin 693 := ⟨z', hz'lt⟩
    have hwL : w ∈ lineThru 0 z := (mem_lineThru_iff h0z hz w).2 (by rwa [Fin.val_zero])
    have hwO : w ∈ O := hlamO w hz'j
    have h0w : (0 : Fin 693) ≠ w := fun h => hz'0 (congrArg Fin.val h).symm
    have hzw := hO.eq_of_mem (isLine_lineThru h0z hz) ⟨left_mem_lineThru 0 z, h0⟩
      ⟨right_mem_lineThru 0 z, hzO⟩ ⟨hwL, hwO⟩ h0z h0w
    rw [hzw]
    exact hz'j

theorem localOK_of_isClosedHyperoval
    {O : Set (Fin 693)} (hO : IsClosedHyperoval O) :
    LocalOK CT O := by
  intro x hx
  have hg := gx_mem x
  have hgi : (gx x)⁻¹ ∈ T46 := T46.inv_mem hg
  have hO' : IsClosedHyperoval (⇑(gx x)⁻¹ '' O) := hO.image_of_mem hgi
  have hinv : (gx x)⁻¹ x = 0 := by
    calc (gx x)⁻¹ x = (gx x)⁻¹ (gx x 0) := by rw [gx_zero]
      _ = 0 := perm_inv_apply_self _ _
  have h0 : (0 : Fin 693) ∈ ⇑(gx x)⁻¹ '' O := ⟨x, hx, hinv⟩
  obtain ⟨j, hj, hjz⟩ := exists_lam_of_zero_mem hO' h0
  refine ⟨j, hj, fun y hy => ?_⟩
  have hr : ap ((CT).gI[x.val]!) y.val = ((gx x)⁻¹ y).val := by
    rw [rep_gI x y.val y.2, idx_of_lt _ y.2, Equiv.Perm.smul_def, Fin.eta]
  rw [hypCtx_lam, hr]
  have hperp : perp 0 ((gx x)⁻¹ y) := by
    have := (isPolarAut_of_mem hgi).map_perp x y
    rw [hinv] at this
    exact this.2 hy
  rw [← hjz _ hperp]
  exact ((gx x)⁻¹.injective.mem_set_image).symm

end CFSG.Fischer
