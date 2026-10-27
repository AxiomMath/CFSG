module

public import Certificates.Data.B3Spor3Checks
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426
open scoped commutatorElement

variable {n : ℕ}

theorem convProdOK_sound {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ q ∈ ps, q < n) (hE : enumOK n gs ps c = true) {qs rs : List ℕ}
    (h : convProdOK n c.pts qs rs = true) {N : ℕ}
    (hN : Nat.card (closure (permsA n gs)) = N)
    (hq : (Nat.primeFactorsList N).all (fun q => q == 3 || qs.contains q) = true) :
    ∀ w ∈ closure (permsA n gs), (orderOf w).Prime → orderOf w ≠ 3 →
      ∃ u ∈ closure (permsA n gs), 3 ∣ orderOf (w * (u * w * u⁻¹)) := by
  intro w hw hwp hw3
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps hE
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hps hE hw
  have hdvd : orderOf w ∣ N := hN ▸ Subgroup.orderOf_dvd_natCard _ hw
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  have hmem' : orderOf w ∈ Nat.primeFactorsList N := (Nat.mem_primeFactorsList hN0).2 ⟨hwp, hdvd⟩
  have hq' := List.all_eq_true.1 hq _ hmem'
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hq'
  have hqs : orderOf w ∈ qs := hq'.resolve_left hw3
  have hc := allLt_spec h hi
  have hpow : eqA n (powArr n c.pts[i]! (orderOf w)) (idA n) = true :=
    (eqA_iff (rep_powArr hrep _) rep_idA).2 (pow_orderOf_eq_one w)
  have hw1 : ¬ eqA n c.pts[i]! (idA n) = true := by
    intro h1
    have := (eqA_iff hrep rep_idA).1 h1
    rw [this, orderOf_one] at hwp
    exact Nat.not_prime_one hwp
  have hany : (qs.any fun q => eqA n (powArr n c.pts[i]! q) (idA n)) = true :=
    List.any_eq_true.2 ⟨_, hqs, hpow⟩
  rw [hany, Bool.eq_false_iff.2 hw1] at hc
  simp only [Bool.not_true, Bool.false_or, Bool.or_false] at hc
  obtain ⟨j, hj', hjr⟩ := List.any_eq_true.1 hc
  have hj : j < c.pts.size := List.mem_range.1 hj'
  obtain ⟨r, hr, hrr⟩ := List.any_eq_true.1 hjr
  obtain ⟨hne', hcube⟩ := Bool.and_eq_true_iff.1 hrr
  have hne : ¬ eqA n (powArr n (compA n c.pts[i]! (conjA n c.pts[j]! c.pts[i]!)) r) (idA n) = true := by
    intro h1
    rw [h1] at hne'
    exact absurd hne' (by decide)
  have hjv : validA n c.pts[j]! = true := hval j hj
  have hconj := rep_conjA hjv hrep
  have hprod := rep_compA hrep hconj
  have hpr := rep_powArr hprod r
  have hu : permOfArr n c.pts[j]! ∈ closure (permsA n gs) := (hmem _).2 ⟨j, hj, rfl⟩
  refine ⟨permOfArr n c.pts[j]!, hu, ?_⟩
  set v := w * (permOfArr n c.pts[j]! * w * (permOfArr n c.pts[j]!)⁻¹) with hv
  have hy1 : v ^ r ≠ 1 := fun h1 => hne ((eqA_iff hpr rep_idA).2 h1)
  have hy3 : (v ^ r) ^ 3 = 1 := (eqA_iff (rep_powArr hpr 3) rep_idA).1 hcube
  have hyo : orderOf (v ^ r) = 3 := orderOf_eq_prime hy3 hy1
  rw [← hyo]
  exact orderOf_pow_dvd r

theorem critOK_sound {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ q ∈ ps, q < n) (hE : enumOK n gs ps c = true) {N : ℕ}
    (hN : Nat.card (closure (permsA n gs)) = N) {cr : Crit} (h : critOK n c.pts N cr = true) :
    B3Phi 3 (closure (permsA n gs)) := by
  unfold critOK at h
  split_ifs at h with hm
  · have hNe : N = 2 ^ cr.a * 3 ^ cr.b := beq_iff_eq.1 h
    exact b3Phi_of_card_two_primes Nat.prime_three (a := cr.b) (q := 2) (b := cr.a)
      Nat.prime_two (by norm_num) (by rw [hN, hNe, mul_comm])
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    exact b3Phi_of_oPrime (gLAPPrimeCoreOf_three_eq_bot_of_conj_product
      (convProdOK_sound hps hE h1 hN h2))

theorem exists_fin_list (L : List ℕ) (hlt : ∀ q ∈ L, q < n) (hnd : L.Nodup) :
    ∃ bs : List (Fin n), bs.Nodup ∧ bs.map Fin.val = L := by
  refine ⟨L.pmap Fin.mk hlt, ?_, ?_⟩
  · exact hnd.pmap (fun a ha b hb h => by simpa using h)
  · rw [List.map_pmap]
    simp

theorem caseOK_valid {D : Data} {k : Case} {x : Array ℕ} (h : caseOK D k x = true) :
    validA D.n x = true := by
  unfold caseOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem caseOK_chain {D : Data} {k : Case} {x : Array ℕ} (h : caseOK D k x = true) :
    ∃ bs : List (Fin D.n), bs.Nodup ∧ bs.map Fin.val = k.base.toList ∧ 1 ≤ D.n ∧
      2 ≤ k.S.size ∧ (∀ q ∈ k.base.toList, q < D.n) ∧
      caseChainOK2P D.n k.S k.base k.W D.A D.B = true := by
  unfold caseOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hchain⟩, hnd⟩, hlt⟩, hn1⟩, hk2⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨bs, hbs, hbsm⟩ := exists_fin_list (n := D.n) k.base.toList hlt hnd
  exact ⟨bs, hbs, hbsm, hn1, hk2, hlt, hchain⟩

theorem caseOK_sound {D : Data} {k : Case} {x : Array ℕ} {A B : Equiv.Perm (Fin D.n)}
    (hA : Rep D.n D.A A) (hB : Rep D.n D.B B) (h : caseOK D k x = true) :
    permOfArr D.n x ^ 3 = 1 ∧
      B3Phi 3 (centralizer {permOfArr D.n x} ⊓ closure {A, B}) := by
  have hx : Rep D.n x (permOfArr D.n x) := rep_of_validA (caseOK_valid h)
  unfold caseOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hchain⟩, hnd⟩, hlt⟩, hn1⟩, hk2⟩, hcent⟩, hcube⟩, hcrit⟩ := h
  obtain ⟨bs, hbs, hbsm⟩ := exists_fin_list (n := D.n) k.base.toList hlt hnd
  have hbase : (bs.map Fin.val).toArray = k.base := by rw [hbsm]
  have hchain' : caseChainOK2P D.n k.S (bs.map Fin.val).toArray k.W D.A D.B = true := by
    rw [hbase]; exact hchain
  have hcent' : centOKP 3 D.n k.S (bs.map Fin.val).toArray x k.rels k.gens k.base.toList
      (enumBfs D.n k.gens k.base.toList (k.card + 1)) k.card = true := by
    rw [hbase]; exact hcent
  obtain ⟨hC, hCcard⟩ := case_centralizer2P (p := 3) hn1 hk2 hbs hA hB hchain' hx hlt hcent'
  refine ⟨(eqA_iff (rep_powArr hx 3) rep_idA).1 hcube, ?_⟩
  rw [← hC]
  exact critOK_sound hlt (centOKP_enum hcent') hCcard hcrit

theorem b3Phi_conj_class {P : Subgroup (Equiv.Perm (Fin n))} {X k : Equiv.Perm (Fin n)}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2)
    (h : B3Phi 3 (centralizer {X} ⊓ P)) :
    B3Phi 3 (centralizer {k * X ^ e * k⁻¹} ⊓ P) := by
  have hXe : (X ^ e) ^ e = X := by
    rcases he with rfl | rfl
    · simp
    · calc (X ^ 2) ^ 2 = X ^ 3 * X := by group
        _ = X := by rw [hX3, one_mul]
  have hmap : (centralizer {X} ⊓ P).map (MulAut.conj k).toMonoidHom =
      centralizer {k * X ^ e * k⁻¹} ⊓ P := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      have hz : z * X ^ e = X ^ e * z := (Commute.pow_right (show Commute z X from hzc) e).eq
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * X ^ e * k⁻¹) = k * (z * X ^ e) * k⁻¹ := by group
        _ = k * (X ^ e * z) * k⁻¹ := by rw [hz]
        _ = k * X ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hyc, hyP⟩
      refine ⟨k⁻¹ * y * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hyP) hk⟩, by group⟩
      have h1 : k⁻¹ * y * k * X ^ e = X ^ e * (k⁻¹ * y * k) := by
        calc k⁻¹ * y * k * X ^ e = k⁻¹ * (y * (k * X ^ e * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * X ^ e * k⁻¹) * y) * k := by rw [hyc]
          _ = X ^ e * (k⁻¹ * y * k) := by group
      have h2 : (Commute (k⁻¹ * y * k) (X ^ e)) := h1
      have h3 := Commute.pow_right h2 e
      rw [hXe] at h3
      exact h3.eq
  rw [← hmap]
  exact (b3Phi_map_iff Nat.prime_three (MulAut.conj k).toMonoidHom
    (MulAut.conj k).injective).2 h

theorem check_sound (D : Data) {A B : Equiv.Perm (Fin D.n)} (hA : Rep D.n D.A A)
    (hB : Rep D.n D.B B) (h : check D = true) :
    ∀ x ∈ closure {A, B}, orderOf x = 3 → B3Phi 3 (centralizer {x} ⊓ closure {A, B}) := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hprod⟩, hord⟩, hm3⟩, hN3⟩, hlines⟩, hsift⟩, htrans⟩, hrec⟩, hsz⟩, hcases⟩ := h
  have hc0 := allLt_spec hcases hpos
  obtain ⟨bs, hbs, hbsm, hn1, hk2, hlt, hchain⟩ := caseOK_chain hc0
  have hbase : (bs.map Fin.val).toArray = D.cases[0]!.base := by rw [hbsm]
  have hchain' : caseChainOK2P D.n D.cases[0]!.S (bs.map Fin.val).toArray D.cases[0]!.W D.A D.B
      = true := by rw [hbase]; exact hchain
  have hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin D.n)}, Rep D.n g G →
      siftA D.n (rawLevels D.n D.cases[0]!.S D.cases[0]!.base) D.cases[0]!.base 0 g = true →
      G ∈ closure {A, B} := by
    intro g G hG hs
    refine mem_closure_two_of_siftG hn1 hk2 hbs hA hB hchain' hG ?_
    rw [hbase]; exact hs
  have hcardP : Nat.card (closure {A, B}) = D.ord := by
    rw [card_closure_two_of_chainOK hn1 hk2 hbs hA hB hchain', hbase, hprod]
  have hfac : (Nat.card (closure {A, B})).factorization 3 = D.k3 := by
    rw [hcardP, hord]
    exact factorization_pow_mulG Nat.prime_three (fun hd => hm3 (Nat.mod_eq_zero_of_dvd hd))
  have hQcard : Nat.card (closure (permsA D.n D.QGens)) = D.N3 := linesOK3_card hlt hlines
  have hQP : closure (permsA D.n D.QGens) ≤ closure {A, B} := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hmemP (rep_of_validA (enumOK_gens_valid (linesOK3_parts hlines).1 hl))
      (allLt_spec hsift hl)
  have hQ : Nat.card (closure (permsA D.n D.QGens)) =
      3 ^ (Nat.card (closure {A, B})).factorization 3 := by
    rw [hQcard, hfac, hN3]
  have hcaseX : ∀ c < D.cases.size, validA D.n D.caseX[c]! = true := fun c hc =>
    caseOK_valid (allLt_spec hcases hc)
  have hrec' : ∀ j < D.lines.size, D.recs.getD j 0 < D.cases.size := fun j hj =>
    of_decide_eq_true (allLt_spec hrec hj)
  intro x hxP hxo
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep (r := D.lines.size) hQP hQ
    (fun j => permOfArr D.n D.lines[j]!) (fun c => permOfArr D.n D.caseX[c]!)
    (fun j => permOfArr D.n D.trans[j]!) (fun j => D.recs.getD j 0)
    (fun g hg hg3 => linesOK3_spec hlt hlines hg hg3)
    (fun j hj => transOK2_spec hmemP (fun j hj => hcaseX _ (hrec' j hj))
      (fun j hj => (linesOK3_line hlines hj).1) htrans hj) hxP hxo
  have hcj := hrec' j hj
  obtain ⟨hX3, hphi⟩ := caseOK_sound hA hB (allLt_spec hcases hcj)
  exact b3Phi_conj_class hX3 hk he hphi

theorem check_valid {D : Data} (h : check D = true) :
    validA D.n D.A = true ∧ validA D.n D.B = true := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hcases⟩ := h
  have hc0 := allLt_spec hcases hpos
  unfold caseOK at hc0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc0
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc0
  exact ⟨hA, hB⟩

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3
