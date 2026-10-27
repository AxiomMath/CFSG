module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Sylow
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocCrit

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat (isPrimeFormGram_one4)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf (PairWit)

theorem powRaw_spec {x : Array ℕ} (hx : rawValid x = true) (n : ℕ) :
    rawValid (powRaw x n) = true ∧ ev (powRaw x n) = ev x ^ n := by
  induction n with
  | zero => exact ⟨rawValid_idCode, by rw [pow_zero]; exact ev_idCode⟩
  | succ n ih =>
    refine ⟨rawValid_mulRaw hx ih.1, ?_⟩
    rw [powRaw, ev_mulRaw hx ih.1, ih.2, pow_succ']

theorem foldl_spec {ls : Array (Array ℕ)} {K : Subgroup (MulAut P43)}
    (hls : ∀ i < 3, rawValid ls[i]! = true ∧ ev ls[i]! ∈ K) :
    ∀ (w : List (ℕ × ℕ)) (acc : Array ℕ), (∀ l ∈ w, l.1 < 3) → rawValid acc = true → ev acc ∈ K →
      rawValid (w.foldl (fun acc l => mulRaw acc (powRaw ls[l.1]! l.2)) acc) = true ∧
        ev (w.foldl (fun acc l => mulRaw acc (powRaw ls[l.1]! l.2)) acc) ∈ K := by
  intro w
  induction w with
  | nil => intro acc _ h1 h2; exact ⟨h1, h2⟩
  | cons l w ih =>
    intro acc hw h1 h2
    have hl : l.1 < 3 := hw l (by simp)
    obtain ⟨hv, hk⟩ := hls l.1 hl
    obtain ⟨hpv, hpe⟩ := powRaw_spec hv l.2
    simp only [List.foldl_cons]
    refine ih _ (fun l' hl' => hw l' (by simp [hl'])) (rawValid_mulRaw h1 hpv) ?_
    rw [ev_mulRaw h1 hpv, hpe]
    exact K.mul_mem h2 (K.pow_mem hk _)

theorem evalWord_spec {ls : Array (Array ℕ)} {K : Subgroup (MulAut P43)}
    (hls : ∀ i < 3, rawValid ls[i]! = true ∧ ev ls[i]! ∈ K) {w : List (ℕ × ℕ)}
    (hw : ∀ l ∈ w, l.1 < 3) : rawValid (evalWord ls w) = true ∧ ev (evalWord ls w) ∈ K :=
  foldl_spec hls w idCode hw rawValid_idCode (by rw [ev_idCode]; exact K.one_mem)

theorem ev_mem_inner {g : Array ℕ} (hv : rawValid g = true) (h16 : g[16]! = 0)
    (hdet : detC g = 3) : ev g ∈ inner P43 := by
  have h9 := ((rawValid_iff g).1 hv).2.1
  have hd1 : ((glOf g hv : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).det = 1 := by
    rw [glOf_val, det_matC h9, hdet, uncode9_three]
  rw [mem_inner_primeFormP]
  refine ⟨⟨glOf g hv, ⟨glOf_mem g hv, hd1⟩⟩, ?_⟩
  have hdec : decG g = ⟨unitOf g, 1⟩ := by
    unfold decG
    rw [h16, pow_zero]
  have hun : unitOf g = ⟨glOf g hv, glOf_mem g hv⟩ := by
    unfold unitOf
    rw [dif_pos hv]
  unfold ev
  rw [hdec, primeFormPsi_apply, map_one, mul_one, hun]

theorem ev_inv_of_isZ {g gi : Array ℕ} (hg : rawValid g = true) (hgi : rawValid gi = true)
    (h : isZ (mulRaw g gi) = true) : ev gi = (ev g)⁻¹ := by
  have h1 := (ev_eq_one_iff (rawValid_mulRaw hg hgi)).2 h
  rw [ev_mulRaw hg hgi] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem comm_of_eqZ {g t : Array ℕ} (hg : rawValid g = true) (ht : rawValid t = true)
    (h : eqZ (mulRaw g t) (mulRaw t g) = true) : ev g * ev t = ev t * ev g := by
  have h1 := eqZ_ev (rawValid_mulRaw hg ht) (rawValid_mulRaw ht hg) h
  rwa [ev_mulRaw hg ht, ev_mulRaw ht hg] at h1

theorem even_orderOf_of_pow {G : Type*} [Group G] {u : G} {j : ℕ} (h2 : (u ^ j) ^ 2 = 1)
    (h1 : u ^ j ≠ 1) : Even (orderOf u) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply h1
  have hd : orderOf u ∣ j * 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact h2)
  have hcop : Nat.Coprime (orderOf u) 2 := Nat.coprime_two_right.mpr hodd
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right hd)

theorem repOK_sound {r : Rep} (h : repOK r = true) : PairWit (inner P43) (ev r.x) (ev r.t) := by
  unfold repOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    and_assoc] at h
  obtain ⟨hx, ht, hg1, hg1i, hg2, hg2i, h16₁, h16₂, hd₁, hd₂, hi₁, hi₂, hc₁, hc₂, hwa, hwb, hma,
    hZa, hmb, hZb, hZc2, hZc⟩ := h
  have hx1 : rawValid (repX1 r) = true := rawValid_mulRaw (rawValid_mulRaw hg1 hx) hg1i
  have hx2 : rawValid (repX2 r) = true := rawValid_mulRaw (rawValid_mulRaw hg2 hx) hg2i
  have hinv₁ : ev r.g1i = (ev r.g1)⁻¹ := ev_inv_of_isZ hg1 hg1i hi₁
  have hinv₂ : ev r.g2i = (ev r.g2)⁻¹ := ev_inv_of_isZ hg2 hg2i hi₂
  have hev1 : ev (repX1 r) = ev r.g1 * ev r.x * (ev r.g1)⁻¹ := by
    unfold repX1
    rw [ev_mulRaw (rawValid_mulRaw hg1 hx) hg1i, ev_mulRaw hg1 hx, hinv₁]
  have hev2 : ev (repX2 r) = ev r.g2 * ev r.x * (ev r.g2)⁻¹ := by
    unfold repX2
    rw [ev_mulRaw (rawValid_mulRaw hg2 hx) hg2i, ev_mulRaw hg2 hx, hinv₂]
  have hls : ∀ i < 3, rawValid (repLetters r)[i]! = true ∧ ev (repLetters r)[i]! ∈
      Subgroup.closure ({ev r.x, ev r.g1 * ev r.x * (ev r.g1)⁻¹, ev r.g2 * ev r.x * (ev r.g2)⁻¹} :
        Set (MulAut P43)) := by
    intro i hi
    interval_cases i
    · refine ⟨hx, ?_⟩
      change ev r.x ∈ _
      exact Subgroup.subset_closure (by simp)
    · refine ⟨hx1, ?_⟩
      change ev (repX1 r) ∈ _
      rw [hev1]
      exact Subgroup.subset_closure (by simp)
    · refine ⟨hx2, ?_⟩
      change ev (repX2 r) ∈ _
      rw [hev2]
      exact Subgroup.subset_closure (by simp)
  obtain ⟨hav, haK⟩ := evalWord_spec hls (w := r.wa) hwa
  obtain ⟨hbv, hbK⟩ := evalWord_spec hls (w := r.wb) hwb
  have hcv : rawValid (repC r) = true := rawValid_mulRaw hav hbv
  have hca : ev (repC r) = ev (repA r) * ev (repB r) := ev_mulRaw hav hbv
  refine ⟨ev r.g1, ev_mem_inner hg1 h16₁ hd₁, ev r.g2, ev_mem_inner hg2 h16₂ hd₂,
    comm_of_eqZ hg1 ht hc₁, comm_of_eqZ hg2 ht hc₂, ev (repA r), haK, ev (repB r), hbK, ?_, ?_, ?_⟩
  · have h1 : ev (repA r) ^ r.ma = 1 := by
      have := (ev_eq_one_iff (powRaw_spec hav r.ma).1).2 hZa
      rwa [(powRaw_spec hav r.ma).2] at this
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr hma) (orderOf_dvd_of_pow_eq_one h1)
  · have h1 : ev (repB r) ^ r.mb = 1 := by
      have := (ev_eq_one_iff (powRaw_spec hbv r.mb).1).2 hZb
      rwa [(powRaw_spec hbv r.mb).2] at this
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr hmb) (orderOf_dvd_of_pow_eq_one h1)
  · rw [← hca]
    have hcj := powRaw_spec hcv r.j
    have hcj2 := powRaw_spec hcj.1 2
    have h2 : (ev (repC r) ^ r.j) ^ 2 = 1 := by
      have := (ev_eq_one_iff hcj2.1).2 hZc2
      rwa [hcj2.2, hcj.2] at this
    have h1 : ev (repC r) ^ r.j ≠ 1 := by
      intro h1
      rw [← hcj.2] at h1
      have := (ev_eq_one_iff hcj.1).1 h1
      rw [hZc] at this
      exact Bool.false_ne_true this
    exact even_orderOf_of_pow h2 h1


theorem repOK_rawValid {r : Rep} (h : repOK r = true) :
    rawValid r.x = true ∧ rawValid r.t = true := by
  unfold repOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', and_assoc] at h
  exact ⟨h.1, h.2.1⟩

theorem size_squares (pts : Array (Array ℕ)) : (squares pts).size = pts.size := by
  simp [squares]

theorem squares_getElem (pts : Array (Array ℕ)) {i : ℕ} (hi : i < pts.size) :
    (squares pts)[i]! = mulRaw pts[i]! pts[i]! := by
  unfold squares
  have h2 : i < (pts.map fun z => mulRaw z z).size := by simpa using hi
  rw [getElem!_pos (pts.map fun z => mulRaw z z) i h2, getElem!_pos pts i hi]
  simp

theorem squares_spec {pts : Array (Array ℕ)} (hv : ∀ i < pts.size, rawValid pts[i]! = true) :
    ∀ i < pts.size, rawValid (squares pts)[i]! = true ∧
      ev (squares pts)[i]! = ev pts[i]! ^ 2 := by
  intro i hi
  rw [squares_getElem pts hi]
  exact ⟨rawValid_mulRaw (hv i hi) (hv i hi), by rw [ev_mulRaw (hv i hi) (hv i hi), pow_two]⟩

theorem mem_orderEight {p4 p8 : Array (Array ℕ)} {i : ℕ} :
    i ∈ orderEight p4 p8 ↔ i < p4.size ∧ isZ p8[i]! = true ∧ isZ p4[i]! = false := by
  simp [orderEight]

theorem mem_involutions {pts p2 : Array (Array ℕ)} {j : ℕ} :
    j ∈ involutions pts p2 ↔ j < pts.size ∧ isZ p2[j]! = true ∧ isZ pts[j]! = false := by
  simp [involutions]

theorem mem_goodPairs {pts p2 p4 p8 : Array (Array ℕ)} {i j : ℕ} :
    (i, j) ∈ goodPairs pts p2 p4 p8 ↔ i ∈ orderEight p4 p8 ∧ j ∈ involutions pts p2 ∧
      eqZ (mulRaw pts[i]! pts[j]!) (mulRaw pts[j]! pts[i]!) = true := by
  simp [goodPairs, and_assoc]

theorem cover_spec {D : Data} (hcov : coverOK D = true) {i j : ℕ}
    (hij : (i, j) ∈ goodPairs (bfs D).pts (squares (bfs D).pts) (squares (squares (bfs D).pts))
      (squares (squares (squares (bfs D).pts)))) :
    ∃ r s, r < D.reps.size ∧ s < (bfs D).pts.size ∧
      eqZ (mulRaw (bfs D).pts[s]! (bfs D).pts[i]!) (mulRaw D.reps[r]!.x (bfs D).pts[s]!) = true ∧
      eqZ (mulRaw (bfs D).pts[s]! (bfs D).pts[j]!) (mulRaw D.reps[r]!.t (bfs D).pts[s]!) = true := by
  unfold coverOK at hcov
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcov
  obtain ⟨hlen, hall⟩ := hcov
  obtain ⟨k, hk, hkk⟩ := List.getElem_of_mem hij
  have hkt : k < D.tab.toList.length := by simp; omega
  have hz := List.getElem_mem (l := (goodPairs (bfs D).pts (squares (bfs D).pts)
    (squares (squares (bfs D).pts)) (squares (squares (squares (bfs D).pts)))).zip D.tab.toList)
    (n := k) (by simp [List.length_zip]; omega)
  have := hall _ hz
  simp only [List.getElem_zip, hkk] at this
  obtain ⟨⟨⟨hr, hs⟩, h1⟩, h2⟩ := this
  exact ⟨_, _, hr, hs, h1, h2⟩


theorem pairWit_of_checks {D : Data} (hs : sylowOK D = true) (hc : coverOK D = true)
    (hr : repsOK D = true) :
    ∀ x ∈ Ssub D, ∀ t ∈ Ssub D, orderOf x = 8 → orderOf t = 2 → x * t = t * x →
      PairWit (inner P43) x t := by
  obtain ⟨hgens, hmem, hcard, hvalid⟩ := sylow_spec hs
  intro x hx t ht hox hot hxt
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  obtain ⟨j, hj, rfl⟩ := (hmem t).1 ht
  have hv : ∀ i < (bfs D).pts.size, rawValid (bfs D).pts[i]! = true := fun i hi =>
    ((valid_iff _).1 (hvalid i hi)).1
  have hav := hv i hi
  have hbv := hv j hj
  have hs2 := size_squares (bfs D).pts
  have hs4 := size_squares (squares (bfs D).pts)
  have hv2 := squares_spec hv
  have hv2' : ∀ i < (squares (bfs D).pts).size, rawValid (squares (bfs D).pts)[i]! = true :=
    fun i hi => (hv2 i (by omega)).1
  have hv4 := squares_spec hv2'
  have hv4' : ∀ i < (squares (squares (bfs D).pts)).size,
      rawValid (squares (squares (bfs D).pts))[i]! = true := fun i hi => (hv4 i (by omega)).1
  have hv8 := squares_spec hv4'
  have hi2 : i < (squares (bfs D).pts).size := by omega
  have hi4 : i < (squares (squares (bfs D).pts)).size := by omega
  have hj2 : j < (squares (bfs D).pts).size := by omega
  obtain ⟨hp2v, hp2e⟩ := hv2 i hi
  obtain ⟨hp4v, hp4e⟩ := hv4 i hi2
  obtain ⟨hp8v, hp8e⟩ := hv8 i hi4
  obtain ⟨hq2v, hq2e⟩ := hv2 j hj
  have hx8 : ev (bfs D).pts[i]! ^ 8 = 1 := by rw [← hox]; exact pow_orderOf_eq_one _
  have hx4 : ev (bfs D).pts[i]! ^ 4 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hox]; norm_num)
  have ht2 : ev (bfs D).pts[j]! ^ 2 = 1 := by rw [← hot]; exact pow_orderOf_eq_one _
  have ht1 : ev (bfs D).pts[j]! ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff.2 h1] at hot
    omega
  have hX8 : isZ (squares (squares (squares (bfs D).pts)))[i]! = true := by
    refine (ev_eq_one_iff hp8v).1 ?_
    rw [hp8e, hp4e, hp2e, ← pow_mul, ← pow_mul]
    exact hx8
  have hX4 : isZ (squares (squares (bfs D).pts))[i]! = false := by
    by_contra hcon
    have h1 := (ev_eq_one_iff hp4v).2 (by simpa using hcon)
    rw [hp4e, hp2e, ← pow_mul] at h1
    exact hx4 h1
  have hT2 : isZ (squares (bfs D).pts)[j]! = true := by
    refine (ev_eq_one_iff hq2v).1 ?_
    rw [hq2e]
    exact ht2
  have hT1 : isZ (bfs D).pts[j]! = false := by
    by_contra hcon
    exact ht1 ((ev_eq_one_iff hbv).2 (by simpa using hcon))
  have hcomm : eqZ (mulRaw (bfs D).pts[i]! (bfs D).pts[j]!)
      (mulRaw (bfs D).pts[j]! (bfs D).pts[i]!) = true := by
    refine (eqZ_iff_ev (rawValid_mulRaw hav hbv) (rawValid_mulRaw hbv hav)).2 ?_
    rw [ev_mulRaw hav hbv, ev_mulRaw hbv hav]
    exact hxt
  have hgood : (i, j) ∈ goodPairs (bfs D).pts (squares (bfs D).pts) (squares (squares (bfs D).pts))
      (squares (squares (squares (bfs D).pts))) :=
    mem_goodPairs.2 ⟨mem_orderEight.2 ⟨hi4, hX8, hX4⟩, mem_involutions.2 ⟨hj, hT2, hT1⟩, hcomm⟩
  obtain ⟨r, s, hr', hs', h1, h2⟩ := cover_spec hc hgood
  have hrep : repOK D.reps[r]! = true := by
    unfold repsOK at hr
    rw [List.all_eq_true] at hr
    refine hr _ ?_
    rw [Array.mem_toList_iff]
    rw [getElem!_pos D.reps r hr']
    exact Array.getElem_mem hr'
  obtain ⟨hxr, htr⟩ := repOK_rawValid hrep
  have hsv := hv s hs'
  have e1 := eqZ_ev (rawValid_mulRaw hsv hav) (rawValid_mulRaw hxr hsv) h1
  have e2 := eqZ_ev (rawValid_mulRaw hsv hbv) (rawValid_mulRaw htr hsv) h2
  rw [ev_mulRaw hsv hav, ev_mulRaw hxr hsv] at e1
  rw [ev_mulRaw hsv hbv, ev_mulRaw htr hsv] at e2
  have hw := PairWit.conj (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P43)
    (repOK_sound hrep) (ev (bfs D).pts[s]!)⁻¹
  have e3 : ev D.reps[r]!.x = ev (bfs D).pts[s]! * ev (bfs D).pts[i]! * (ev (bfs D).pts[s]!)⁻¹ := by
    rw [e1]; group
  have e4 : ev D.reps[r]!.t = ev (bfs D).pts[s]! * ev (bfs D).pts[j]! * (ev (bfs D).pts[s]!)⁻¹ := by
    rw [e2]; group
  rw [e3, e4] at hw
  simpa [mul_assoc] using hw

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
