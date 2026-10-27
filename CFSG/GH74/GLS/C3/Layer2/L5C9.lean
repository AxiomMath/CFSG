
module

public import CFSG.GH74.GLS.C3.Layer2.L5C9Base

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs
public import Certificates.Certificate5071

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.HF

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5

theorem fam0_card : fam0.card = 4 :=
  Certificates.certificate5071.1

theorem fam1_card : fam1.card = 4 :=
  Certificates.certificate5071.2.1

theorem one_mem_n24L : (1 : Perm (Fin 16)) ∈ n24L :=
  Certificates.certificate5071.2.2.1

theorem n24L_mul_chk : mulClosedChkP n24L = true :=
  Certificates.certificate5071.2.2.2.1

theorem n24L_inv_chk : invClosedChkP n24L = true :=
  Certificates.certificate5071.2.2.2.2.1

theorem n24L_nodup : n24L.Nodup :=
  Certificates.certificate5071.2.2.2.2.2.1

@[expose] def N24sub : Subgroup (Perm (Fin 16)) :=
  lsubP n24L one_mem_n24L n24L_mul_chk n24L_inv_chk

theorem wHat_mem_n24L : wHat ∈ n24L :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem d8L_sub_n24L_chk :
    d8L.all (fun d => decide (d ∈ n24L)) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem d8L_sub_n24L : ∀ d ∈ d8L, d ∈ n24L := by
  have h := d8L_sub_n24L_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem v4L_sub_d8L_chk :
    v4L.all (fun v => decide (v ∈ d8L)) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem v4L_sub_d8L : ∀ v ∈ v4L, v ∈ d8L := by
  have h := v4L_sub_d8L_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem v4L_normal_chk :
    n24L.all (fun m => v4L.all fun v => decide (m * v * m⁻¹ ∈ v4L)) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem v4L_normal : ∀ m ∈ n24L, ∀ v ∈ v4L, m * v * m⁻¹ ∈ v4L := by
  have h := v4L_normal_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem cHat_v4L_chk :
    v4L.all (fun v => decide (cHat * v * cHat⁻¹ ∈ v4L)) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cHat_normalizes_v4L :
    ∀ v ∈ v4L, cHat * v * cHat⁻¹ ∈ v4L := by
  have h := cHat_v4L_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem n24_enum : allQ2 gN n24Entry = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem n24_gen
    (m : Perm (Fin 16)) (hlin : IsLin16 m) (hQ : Qpl.image m ≠ Qpl)
    (hQ1 : Qpl.image m ∩ Qpl = {0}) (hQ2 : Qpl.image m ∩ Ppl = {0})
    (F : Finset (Finset (Fin 16))) (hF : F.card ≤ 4) (hQF : Qpl ∈ F)
    (hstab : ∀ V ∈ F, V.image yHat ∈ F ∧ V.image wHat ∈ F ∧ V.image m ∈ F) :
    Ppl.image m = Ppl ∧
      ((F = fam0 ∧ ∀ A ∈ n24L, A ∈ Subgroup.closure {yHat, wHat, m}) ∨
        (F = fam1 ∧ ∀ A ∈ n24L, twPerm * A * twPerm⁻¹ ∈ Subgroup.closure {yHat, wHat, m})) := by
  have hg : gN (m 1) (m 2) = true := by
    simp only [gN, ← Qpl_image_lin hlin, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hQ, hQ1⟩, hQ2⟩
  have hc := lin_check2 gN n24Entry n24_enum hlin hg
  have hpre : n24Pre m = true := by
    simp only [n24Pre, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hQ, hQ1⟩, hQ2⟩
  simp only [n24Entry, hpre, Bool.not_true, Bool.false_or] at hc
  have hF' : ∀ V ∈ F, ∀ g ∈ [yHat, wHat, m], V.image g ∈ F := by
    intro V hV g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    exacts [(hstab V hV).1, (hstab V hV).2.1, (hstab V hV).2.2]
  have ho : (orbList [yHat, wHat, m] 6).toFinset ⊆ F := fun V hV =>
    orbList_mem hQF hF' 6 V (List.mem_toFinset.1 hV)
  have hset : ({x | x ∈ [yHat, wHat, m]} : Set (Perm (Fin 16))) = {yHat, wHat, m} := by
    ext x
    simp
  simp only [n24Chk, n24Tail, n24Cov, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hc
  rcases hc with h5 | ⟨hP, ⟨hf0, hall0⟩ | ⟨hf1, hall1⟩⟩
  · exfalso
    have := Finset.card_le_card ho
    omega
  · refine ⟨hP, Or.inl ⟨?_, ?_⟩⟩
    · exact (Finset.eq_of_subset_of_card_le (hf0.trans ho) (by rw [fam0_card]; exact hF)).symm
    · intro A hA
      rw [← hset]
      exact mem_closure_of_tab [yHat, wHat, m] 8 (by simpa using hall0 A hA)
  · refine ⟨hP, Or.inr ⟨?_, ?_⟩⟩
    · exact (Finset.eq_of_subset_of_card_le (hf1.trans ho) (by rw [fam1_card]; exact hF)).symm
    · intro A hA
      rw [← hset]
      exact mem_closure_of_tab [yHat, wHat, m] 8 (by simpa using hall1 A hA)

theorem planes0_fam0 :
    ∀ V ∈ planes0, V.toFinset ∈ fam0 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fam0_planes0 :
    ∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem planes1_fam1 :
    ∀ V ∈ planes1, V.toFinset ∈ fam1 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fam1_planes1 :
    ∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fam0ChkL_of
    {m : Perm (Fin 16)} (h : ∀ V ∈ fam0, V.image m ∈ fam0) :
    fam0ChkL m = true := by
  simp only [fam0ChkL, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  intro V hV
  obtain ⟨W, hW, hWe⟩ := fam0_planes0 _ (h _ (planes0_fam0 V hV))
  refine ⟨W, hW, fun x hx => ?_⟩
  have : m x ∈ V.toFinset.image m := Finset.mem_image_of_mem m (List.mem_toFinset.2 hx)
  rw [← hWe] at this
  exact List.mem_toFinset.1 this

theorem fam1ChkL_of
    {m : Perm (Fin 16)} (h : ∀ V ∈ fam1, V.image m ∈ fam1) :
    fam1ChkL m = true := by
  simp only [fam1ChkL, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  intro V hV
  obtain ⟨W, hW, hWe⟩ := fam1_planes1 _ (h _ (planes1_fam1 V hV))
  refine ⟨W, hW, fun x hx => ?_⟩
  have : m x ∈ V.toFinset.image m := Finset.mem_image_of_mem m (List.mem_toFinset.2 hx)
  rw [← hWe] at this
  exact List.mem_toFinset.1 this

theorem Qpl_mem_fam0 : Qpl ∈ fam0 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qpl_mem_fam1 : Qpl ∈ fam1 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem gFam_of_pres {m : Perm (Fin 16)} (hlin : IsLin16 m)
    (h : (∀ V ∈ fam0, V.image m ∈ fam0) ∨ (∀ V ∈ fam1, V.image m ∈ fam1)) :
    gFam (m 1) (m 2) = true := by
  have e := Qpl_image_lin hlin
  simp only [gFam, ← e, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with h | h
  · exact Or.inl (h Qpl Qpl_mem_fam0)
  · exact Or.inr (h Qpl Qpl_mem_fam1)

theorem G72L_length : G72L.length = 72 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem G72L_nodup : G72L.Nodup :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem one_mem_G72L : (1 : Perm (Fin 16)) ∈ G72L :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem G72L_mul_chk : mulClosedChkP G72L = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem G72L_inv_chk : invClosedChkP G72L = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def G72sub : Subgroup (Perm (Fin 16)) :=
  lsubP G72L one_mem_G72L G72L_mul_chk G72L_inv_chk

theorem card_G72 : Nat.card G72sub = 72 := by
  rw [natCard_eq_length G72sub G72L G72L_nodup (fun p => Iff.rfl)]
  exact G72L_length

theorem G72L_facts :
    G72L.all (fun m => linChk m && fam0Chk m) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fam_enum :
    allQ2 gFam (famEntry G72L) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pres_P_of_fam (m : Perm (Fin 16)) (hlin : IsLin16 m)
    (h : (∀ V ∈ fam0, V.image m ∈ fam0) ∨ (∀ V ∈ fam1, V.image m ∈ fam1)) :
    Ppl.image m = Ppl := by
  have hc := lin_check2 gFam (famEntry G72L) fam_enum hlin (gFam_of_pres hlin h)
  have h' : (fam0ChkL m || fam1ChkL m) = true := by
    rcases h with h | h
    · rw [fam0ChkL_of h]
      rfl
    · rw [fam1ChkL_of h]
      exact Bool.or_true _
  simp only [famEntry, Bool.and_eq_true] at hc
  have h2 := hc.1.1
  simp only [presChk, h', Bool.not_true, Bool.false_or] at h2
  exact of_decide_eq_true h2

theorem mem_G72 {m : Perm (Fin 16)} :
    m ∈ G72sub ↔ IsLin16 m ∧ ∀ V ∈ fam0, V.image m ∈ fam0 := by
  constructor
  · intro hm
    have h := G72L_facts
    simp only [List.all_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h m hm
    exact ⟨isLin16_of_chk h1, fam0Chk_iff.1 h2⟩
  · rintro ⟨hlin, hfam⟩
    have hc := lin_check2 gFam (famEntry G72L) fam_enum hlin (gFam_of_pres hlin (Or.inl hfam))
    have h0 := fam0ChkL_of hfam
    simp only [famEntry, Bool.and_eq_true] at hc
    have h2 := hc.1.2
    simp only [h0, Bool.not_true, Bool.false_or] at h2
    show m ∈ G72L
    exact of_decide_eq_true h2

theorem card_dvd_72 (N : Subgroup (Perm (Fin 16)))
    (hN : ∀ m ∈ N, IsLin16 m ∧ ∀ V ∈ fam0, V.image m ∈ fam0) : Nat.card N ∣ 72 := by
  have hle : N ≤ G72sub := fun m hm => mem_G72.2 (hN m hm)
  have := Subgroup.card_dvd_of_le hle
  rwa [card_G72] at this

theorem n24g_mem : n24L.getD 6 1 ∈ n24L :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem G72_cHat (N : Subgroup (Perm (Fin 16)))
    (hN : ∀ m ∈ N, IsLin16 m ∧ Ppl.image m = Ppl ∧ ∀ V ∈ fam0, V.image m ∈ fam0)
    (hA : ∀ A ∈ n24L, A ∈ N) (hex : ∃ m ∈ N, m ∉ n24L) : cHat ∈ N := by
  obtain ⟨m, hm, hmn⟩ := hex
  obtain ⟨hlin, -, hfam⟩ := hN m hm
  have hc := lin_check2 gFam (famEntry G72L) fam_enum hlin (gFam_of_pres hlin (Or.inl hfam))
  have h0 := fam0ChkL_of hfam
  have hmn' : decide (m ∈ n24L) = false := decide_eq_false hmn
  simp only [famEntry, Bool.and_eq_true] at hc
  have hc2 := hc.2
  simp only [cHatChk, h0, hmn', Bool.not_true, Bool.false_or, Bool.or_false,
    decide_eq_true_eq] at hc2
  have hmem := mem_closure_of_tab [wHat, n24L.getD 6 1, m] 8 hc2
  refine (Subgroup.closure_le N).2 ?_ hmem
  intro x hx
  have hx' : x ∈ [wHat, n24L.getD 6 1, m] := hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl
  · exact hA _ wHat_mem_n24L
  · exact hA _ n24g_mem
  · exact hm

theorem yHat_ne_one : yHat ≠ 1 :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem d8_enum :
    n24L.all (fun b => n24L.all fun c => d8Chk b c) = true :=
  Certificates.certificate5071.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem d8L_unique
    (D : Subgroup (Perm (Fin 16))) (hD : D ≤ N24sub) (hcard : Nat.card D = 8)
    (hy : yHat ∈ D) (d : Perm (Fin 16)) : d ∈ D ↔ d ∈ d8L := by
  obtain ⟨b, hb, c, hc, hgen⟩ := exists_gen3 D yHat hy yHat_ne_one hcard.le
  have hbn : b ∈ n24L := hD hb
  have hcn : c ∈ n24L := hD hc
  have h := d8_enum
  simp only [List.all_eq_true] at h
  have hchk := h b hbn c hcn
  have hset : ({x | x ∈ [yHat, b, c]} : Set (Perm (Fin 16))) = {yHat, b, c} := by
    ext x
    simp
  set T := closureL (([yHat, b, c] : List (Perm (Fin 16))).map tabL) 8 with hT
  simp only [d8Chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hclosed, hlast⟩ := hchk
  have hDmem : ∀ x : Perm (Fin 16), x ∈ D ↔ x ∈ n24L ∧ tabL x ∈ T := by
    intro x
    constructor
    · intro hx
      refine ⟨hD hx, ?_⟩
      refine closure_sub_tab [yHat, b, c] T (one_mem_closureL _ _) ?_ ?_
      · intro t ht s hs
        exact hclosed t ht s hs
      · rw [hset, hgen]
        exact hx
    · rintro ⟨-, hx⟩
      have := mem_closure_of_tab [yHat, b, c] 8 hx
      rw [hset, hgen] at this
      exact this
  set L := n24L.filter fun x => decide (tabL x ∈ T) with hL
  have hLcard : Nat.card D = L.length := by
    refine natCard_eq_length D L (n24L_nodup.filter _) fun p => ?_
    rw [hL, List.mem_filter, decide_eq_true_eq]
    exact hDmem p
  have hL8 : L.length = 8 := hLcard ▸ hcard
  simp only [hL8, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hlast
  obtain ⟨hl1, hl2⟩ := hlast
  constructor
  · intro hx
    have : d ∈ L := by
      rw [hL, List.mem_filter, decide_eq_true_eq]
      exact (hDmem d).1 hx
    exact hl1 d this
  · intro hx
    have hx' : d ∈ L := hl2 d hx
    rw [hL, List.mem_filter, decide_eq_true_eq] at hx'
    exact (hDmem d).2 hx'

end CFSG.GH74.GLS.C3.Layer2.L5.HF
