module

public import CFSG.Certificates.Kernel.F4TT3
public import CFSG.Certificates.Kernel.F4TT4

public section

namespace CFSG.KC.F4T

open CFSG.Fischer CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

theorem imgT_sound {v v' : List Nat} (hv : (∀ x ∈ v, x < 4) ∧ vecT v ≠ 0)
    (hv' : (∀ x ∈ v', x < 4) ∧ vecT v' ≠ 0) {A B : M3 Nat} (hA : OK A) (hB : OK B)
    (hdA : (toMT A).det ≠ 0) (hdB : (toMT B).det ≠ 0) (h : imgT A v = imgT B v') :
    ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec (toMT A) (vecT v) = c • Matrix.mulVec (toMT B) (vecT v') :=
  imgT_proj hv.1 hv'.1 hA hB (mulVec_ne_zero_of_det hdA hv.2) (mulVec_ne_zero_of_det hdB hv'.2) h

theorem levelsT_contains : ∀ l < 4, ∀ p < 6, l < p → levelsT.contains (l, p) = true := by
  decide

theorem levelsT_mem (l : Nat) (hl : l < 4) (p : Nat) (hp : p < 6) (hlp : l < p) :
    (l, p) ∈ levelsT := by
  have := levelsT_contains l hl p hp hlp
  simpa using this

theorem getD_mem_of_lt {Om : List (List Nat)} {q : Nat} (hq : q < Om.length) :
    Om.getD q [] ∈ Om := by
  rw [List.getD_eq_getElem _ _ hq]
  exact List.getElem_mem hq

theorem inPT_sound (k : Fin 6) {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega k ↔ ∃ d ∈ Om, vecT d = v) (hOm : PtsOK Om) {A : M3 Nat} (hA : OK A)
    (h : inPT Om A = true) : (toMT A).det = 1 ∧ stabilizes k (toMT A) := by
  simp only [inPT, Bool.and_eq_true, Nat.beq_eq] at h
  have hd : (toMT A).det = 1 := by rw [f4_detT hA, h.1, f4_one]
  refine ⟨hd, ?_⟩
  have h1 := hmaskT_sound hOm hA mOne_OK (by rw [hd]; exact one_ne_zero)
    (by rw [toMT_mOne, Matrix.det_one]; exact one_ne_zero) h.2
  rw [toMT_mOne] at h1
  exact stab_of_ImgIn hΩ h1

theorem InM_P_of_inPT (k : Fin 6) {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega k ↔ ∃ d ∈ Om, vecT d = v) (hOm : PtsOK Om) {A : M3 Nat} (hA : OK A)
    (h : inPT Om A = true) : InM (P k) (toMT A) := by
  obtain ⟨hd, hs⟩ := inPT_sound k hΩ hOm hA h
  exact InM_of_P le_rfl hd hs

theorem closure_eq_P_of_data (k : Fin 6) {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega k ↔ ∃ d ∈ Om, vecT d = v) (hOm : PtsOK Om)
    (hdist : ∀ i < 6, ∀ j < 6, i ≠ j → ∀ c : F4, vecT (Om.getD i []) ≠ c • vecT (Om.getD j []))
    (hframe : IsUnit (Matrix.of fun r (i : Fin 3) => vecT (Om.getD i []) r).det)
    (ha : ∃ a : Fin 3 → F4, (∀ i, a i ≠ 0) ∧
      Matrix.mulVec (Matrix.of fun r (i : Fin 3) => vecT (Om.getD i []) r) a = vecT (Om.getD 3 []))
    {g1 g2 code : List Nat} {ws cw : List (List Nat)}
    (hchain : chainOK Om g1 g2 cw = true) (hnr : nonRootOK Om g1 g2 code ws = true)
    {x w z t : Matrix.GeneralLinearGroup (Fin 3) F4} (hx : (x : Matrix (Fin 3) (Fin 3) F4) = Xd)
    (hw : (w : Matrix (Fin 3) (Fin 3) F4) = Wm 1) (hz : (z : Matrix (Fin 3) (Fin 3) F4) = Zs)
    (ht : toMT (matN code) = (t : Matrix (Fin 3) (Fin 3) F4)) :
    Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4)) = P k := by
  simp only [nonRootOK, Bool.and_eq_true, Nat.beq_eq] at hnr
  obtain ⟨⟨⟨⟨hc, hinA⟩, _⟩, e1⟩, e2⟩ := hnr
  simp only [chainOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hchain
  obtain ⟨⟨⟨⟨⟨⟨hlen, hc1⟩, hc2⟩, hin1⟩, hin2⟩, hwl⟩, hsteps⟩ := hchain
  have hAOK := matN_OK hc
  obtain ⟨hdA, hsA⟩ := inPT_sound k hΩ hOm hAOK hinA
  set H := Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4)) with hH
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hwH : w ∈ H := Subgroup.subset_closure (by simp)
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  obtain ⟨o1, _, o3, _⟩ := consts_OK
  have hg4 : GensIn H [xdT, wmT 1, zsT, matN code] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨o1, ⟨x, hxH, by rw [hx, toMT_xdT]⟩⟩
    · exact ⟨wmT_OK (by decide), ⟨w, hwH, by rw [hw, toMT_wmT, f4_one]⟩⟩
    · exact ⟨o3, ⟨z, hzH, by rw [hz, toMT_zsT]⟩⟩
    · exact ⟨hAOK, ⟨t, htH, ht.symm⟩⟩
  have hg1OK := matN_OK hc1
  have hg2OK := matN_OK hc2
  have hgH : GensIn H [matN g1, matN g2] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨hg1OK, ?_⟩
      rw [← mEq_eq e1]
      exact InM_evalT hg4 _
    · refine ⟨hg2OK, ?_⟩
      rw [← mEq_eq e2]
      exact InM_evalT hg4 _
  have hgP : GensIn (P k) [matN g1, matN g2] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨hg1OK, InM_P_of_inPT k hΩ hOm hg1OK hin1⟩
    · exact ⟨hg2OK, InM_P_of_inPT k hΩ hOm hg2OK hin2⟩
  have hpt : ∀ q < 6, (∀ x ∈ Om.getD q [], x < 4) ∧ vecT (Om.getD q []) ≠ 0 := fun q hq =>
    hOm _ (getD_mem_of_lt (by rw [hlen]; exact hq))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_P.2 ⟨by rw [hx]; exact det_Xd, by rw [hx]; exact stab_Xd _⟩
    · exact mem_P.2 ⟨by rw [hw]; exact det_Wm1, by rw [hw]; exact stab_Wm1 _⟩
    · exact mem_P.2 ⟨by rw [hz]; exact det_Zs, by rw [hz]; exact stab_Zs _⟩
    · exact mem_P.2 ⟨by rw [← ht]; exact hdA, by rw [← ht]; exact hsA⟩
  · obtain ⟨a, ha0, ha3⟩ := ha
    have hZ : InM H Zs := ⟨z, hzH, hz⟩
    refine P_le_of_chain k (fun q => vecT (Om.getD q [])) ?_ ?_ hdist hframe (fun i => rfl) ha0
      ha3 hZ ?_
    · intro v hv
      obtain ⟨d, hd, rfl⟩ := (hΩ v).1 hv
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hd
      exact ⟨q, by rw [← hlen]; exact hq, by rw [List.getD_eq_getElem _ _ hq]⟩
    · intro q hq
      exact (hΩ _).2 ⟨_, getD_mem_of_lt (by rw [hlen]; exact hq), rfl⟩
    · intro l hl p hlp hp
      obtain ⟨wd, hwd⟩ := snd_mem_zip hwl (levelsT_mem l hl p hp hlp)
      have hst := hsteps _ hwd
      simp only [stepOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hst
      obtain ⟨hfix, hmove⟩ := hst
      set r := evalT [matN g1, matN g2] wd with hr
      have hrOK : OK r := evalT_OK _ _
      obtain ⟨u, huH, hu⟩ := InM_evalT hgH wd
      obtain ⟨u', huP, hu'⟩ := InM_evalT hgP wd
      have huu : u = u' := Units.ext (hu.trans hu'.symm)
      have hrdet : (toMT r).det ≠ 0 := by
        rw [← hu', (mem_P.1 huP).1]
        exact one_ne_zero
      have hone : (toMT mOne).det ≠ 0 := by rw [toMT_mOne, Matrix.det_one]; exact one_ne_zero
      refine ⟨u', huP, huu ▸ huH, fun i hi => ?_, ?_⟩
      · obtain ⟨c, hc, he⟩ := imgT_sound (hpt i (by omega)) (hpt i (by omega)) hrOK mOne_OK hrdet
          hone (hfix i hi)
        rw [toMT_mOne, Matrix.one_mulVec] at he
        exact ⟨c, hc, by rw [hu']; exact he⟩
      · obtain ⟨c, hc, he⟩ := imgT_sound (hpt l (by omega)) (hpt p hp) hrOK mOne_OK hrdet
          hone hmove
        rw [toMT_mOne, Matrix.one_mulVec] at he
        exact ⟨c, hc, by rw [hu']; exact he⟩

end CFSG.KC.F4T

end
