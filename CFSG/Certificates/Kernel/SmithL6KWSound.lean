module

public import CFSG.Certificates.Kernel.SmithL6KGSound
public import CFSG.Certificates.Kernel.SmithL6CollSound
public import Certificates.Data.Kernel.SmithL6KW

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (tri applyCols)

theorem tvA_lt64 {p : Nat × Nat} (hp : TvP p) {x : Nat} (hx : x < 64) : tvA p x < 64 := by
  unfold tvA
  split
  · exact xor_lt64 hx hp.1
  · exact hx

theorem form_conjP_snd (p q : Nat × Nat) (x : Nat) :
    form (conjP p q).2 x = form q.2 (tvA p x) := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  unfold conjP tvA
  simp only
  cases hφw : form φ w <;> cases hψx : form ψ x <;>
    simp [form_xor_left, form_xor_right, hφw, hψx]

theorem setM_imgMaskK {p : Nat × Nat} (hp : TvP p) (M : Nat) :
    setM (imgMaskK (codeOf p) M) = (setM M).image (tvA p) := by
  unfold imgMaskK
  rw [codeOf_div hp, codeOf_mod hp]
  ext y
  rw [mem_setM, Finset.mem_image]
  have e := foldl_or_testBit (fun x => tvA (p.1, p.2) x) (fun x => M.testBit x) (List.range 64) 0 y
  simp only [Nat.zero_testBit, Bool.false_or] at e
  rw [e, List.any_eq_true]
  have hp' : (p.1, p.2) = p := rfl
  simp only [hp', List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨-, x, hx, hM, rfl⟩
    exact ⟨x, mem_setM.mpr ⟨hx, hM⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx64, hM⟩ := mem_setM.mp hx
    exact ⟨tvA_lt64 hp hx64, x, hx64, hM, rfl⟩

theorem wt_lt20K (i : Nat) : wt i < 2 ^ 20 := by
  unfold wt
  generalize wB i = p
  obtain ⟨a, b, c⟩ := p
  exact wedge3_lt20 a b c

@[expose] def Clo (k : Nat) : Prop :=
  ∀ i < 1395, ∃ j < 1395, wt j = applyCols (tvCols k) (wt i) ∧
    setM (wMask j) = (setM (wMask i)).image (tvApply k)

theorem clo_tvImg {g u : Nat} (hg : g < 1953) (hu : u < 1953) (Cg : Clo g) (Cu : Clo u) :
    Clo (tvImg g u) := by
  intro i hi
  obtain ⟨j1, hj1, w1, m1⟩ := Cg i hi
  obtain ⟨j2, hj2, w2, m2⟩ := Cu j1 hj1
  obtain ⟨j3, hj3, w3, m3⟩ := Cg j2 hj2
  refine ⟨j3, hj3, ?_, ?_⟩
  · rw [w3, w2, w1, tvCols_tvImg hg hu _ (wt_lt20K i)]
  · rw [m3, m2, m1, Finset.image_image, Finset.image_image]
    exact congrArg (fun f => Finset.image f (setM (wMask i)))
      (funext fun x => (tvApply_tvImg hg hu x).symm)

theorem clo_of_closeRowK {g R W M : Nat} (hg : g < 1953) (hW : ∀ i < 1395, fldW 20 W i = wt i)
    (hM : ∀ i < 1395, fldW 64 M i = wMask i)
    (h : closeRowK (tvCols g).toList (codeOf (tvPair g)) R W M = true) : Clo g := by
  intro i hi
  unfold closeRowK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hj, hw⟩, hm⟩ := h i hi
  refine ⟨_, hj, ?_, ?_⟩
  · rw [← hW _ hj, hw, hW i hi, ← applyCols_toArray, Array.toArray_toList]
  · rw [← hM _ hj, hm, hM i hi, setM_imgMaskK (tvP_tvPair hg)]
    exact congrArg (fun f => Finset.image f (setM (wMask i)))
      (funext fun x => (tvApply_eq_tvA g x).symm)

theorem chkTW_of {G : List Nat} (hG : ∀ s < G.length, G.getD s 0 < 1953)
    (hG0 : G.getD 0 1 = 0) (hR : Reach 1953 G.length (· == 0)
      (fun s u v => tvImg (G.getD s 0) u == v))
    (hclo : ∀ s < G.length, Clo (G.getD s 0))
    (hinj : ∀ i < 1395, ∀ j < 1395, wt i = wt j → i = j)
    (hann : ∀ j < 1395, setM (annArr[j]!) = annS (setM (wMask j))) :
    chkTW = true := by
  have hlen : 0 < G.length := by
    rcases G with _ | ⟨g, G⟩
    · simp at hG0
    · simp
  have hgd : G.getD 0 0 = 0 := by
    rcases G with _ | ⟨g, G⟩
    · simp at hlen
    · simpa using hG0
  have hall := reach_gens hR Clo (hgd ▸ hclo 0 hlen)
    fun s hs u hu hP => clo_tvImg (hG s hs) hu (hclo s hs) hP
  unfold chkTW
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  intro k hk i hi
  obtain ⟨j, hj, hw, hm⟩ := hall k hk i hi
  have hpi : planeImg k i = j := by
    unfold planeImg wtIdx
    rw [tvArr_get hk, wtArr_get hi, ← hw]
    exact foldl_set_last (f := fun j => wtArr[j]!) (wt_lt20K j) hj (wtArr_get hj)
      fun j' h1 h2 e => by
        rw [wtArr_get h2] at e
        have := hinj j' h2 j hj e
        omega
  rw [hpi]
  refine ⟨hj, by rw [wtArr_get hj, tvArr_get hk, wtArr_get hi]; exact hw, ?_⟩
  rw [planePtsArr_get hi]
  unfold planePts
  rw [List.all_toArray, List.all_eq_true]
  intro a ha
  rw [List.mem_filter, List.mem_range] at ha
  obtain ⟨ha1, ha2⟩ := ha
  rw [tvTab_get hk ha1, flagArr_get hj (tvImg_lt hk ha1)]
  unfold inPlane at ha2 ⊢
  rw [maskArr_get hi] at ha2
  rw [maskArr_get hj, tvPair_tvImg hk ha1]
  rw [Bool.and_eq_true] at ha2 ⊢
  have hp := tvP_tvPair hk
  have hq := tvP_tvPair ha1
  have hv : (tvPair a).1 ∈ setM (wMask i) := mem_setM.mpr ⟨hq.1, ha2.1⟩
  have hφ : (tvPair a).2 ∈ annS (setM (wMask i)) := by
    rw [← hann i hi]
    exact mem_setM.mpr ⟨hq.2.1, ha2.2⟩
  constructor
  · have h1 : tvA (tvPair k) (tvPair a).1 ∈ setM (wMask j) := by
      rw [hm]
      exact Finset.mem_image.mpr ⟨_, hv, tvApply_eq_tvA _ _⟩
    exact (mem_setM.mp h1).2
  · have h2 : (conjP (tvPair k) (tvPair a)).2 ∈ annS (setM (wMask j)) := by
      rw [mem_annS]
      refine ⟨(conjP_tvP hp hq).2.1, fun y hy => ?_⟩
      rw [hm, Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [form_conjP_snd, ← tvApply_eq_tvA, tvApply_tvApply hk]
      exact (mem_annS.mp hφ).2 x hx
    rw [← hann j hj] at h2
    exact (mem_setM.mp h2).2

end CFSG.SmithL6.K
