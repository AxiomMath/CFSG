module

public import Certificates.Data.Kernel.TcF
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TcNative
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KC.TcF

open CFSG.KS.SporSch CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier

variable {n : Nat}

private theorem bnot_eq (b : Bool) : Bool.rec (motive := fun _ => Bool) true false b = !b := by
  cases b <;> rfl

private theorem memF_iff {bs : List Nat} {N : Nat} {t : Nat → Nat → Nat} {f : Nat → Nat} :
    memF bs N t f = true ↔ ∃ i < N, eqOnL bs (t i) f = true := by
  unfold memF
  simp only [bnot_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, CFSG.KS.Raw.Orb.allN_iff]
  push Not
  simp

@[expose] def ElF (H : Subgroup (Equiv.Perm (Fin n))) (a : Array Nat) (f : Nat → Nat) : Prop :=
  validA n a = true ∧ RepF n f (permOfArr n a) ∧ permOfArr n a ∈ H

@[expose] def ElFI (H : Subgroup (Equiv.Perm (Fin n))) (a : Array Nat) (f fi : Nat → Nat) : Prop :=
  ElF H a f ∧ RepF n fi (permOfArr n a)⁻¹

private theorem any_of_memF {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat} {N : Nat}
    {c : ArrCert} {t : Nat → Nat → Nat} (hF : BaseFaithful H bs) (hs : c.pts.size = N)
    (hp : ∀ i < N, ElF H c.pts[i]! (t i)) {a : Array Nat} {f : Nat → Nat}
    {g : Equiv.Perm (Fin n)} (ha : Rep n a g) (hf : RepF n f g) (hg : g ∈ H)
    (h : memF bs N t f = true) : c.pts.toList.any (eqA n a) = true := by
  obtain ⟨i, hi, he⟩ := memF_iff.1 h
  obtain ⟨hv, hr, hm⟩ := hp i hi
  have e : permOfArr n c.pts[i]! = g := eq_of_eqOnL hF hr hf hm hg he
  rw [List.any_eq_true]
  refine ⟨c.pts[i]!, ?_, (eqA_iff ha (rep_of_validA hv)).2 e.symm⟩
  rw [getElem!_pos c.pts i (by omega)]
  exact Array.getElem_mem_toList _

private theorem memF_of_any {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat} {N : Nat}
    {c : ArrCert} {t : Nat → Nat → Nat} (hbs : ∀ b ∈ bs, b < n) (hs : c.pts.size = N)
    (hp : ∀ i < N, ElF H c.pts[i]! (t i)) {a : Array Nat} {f : Nat → Nat}
    {g : Equiv.Perm (Fin n)} (ha : Rep n a g) (hf : RepF n f g)
    (h : c.pts.toList.any (eqA n a) = true) : memF bs N t f = true := by
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, he⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < N := by rw [← hs]; simpa using hi
  have hget : c.pts.toList[i] = c.pts[i]! := by
    rw [getElem!_pos c.pts i (by omega)]
    simp
  rw [hget] at he
  obtain ⟨hv, hr, -⟩ := hp i hi'
  have e : g = permOfArr n c.pts[i]! := (eqA_iff ha (rep_of_validA hv)).1 he
  exact memF_iff.2 ⟨i, hi', eqOnL_of_eq hbs hr (e ▸ hf)⟩

theorem tcOK_of_F {m ngQ ngK NQ NK NS : Nat} {ps bs : List Nat} {x : Array Nat} {D : TcData}
    {cQ cK cS : ArrCert} {H : Subgroup (Equiv.Perm (Fin n))} {xf : Nat → Nat}
    {gQ cu cv cui cvi gK R Ri tq tk : Nat → Nat → Nat} {sig : Nat → Nat → Nat}
    (hbs : ∀ b ∈ bs, b < n) (hF : BaseFaithful H bs) (hx : ElF H x xf)
    (hQs : D.gQ.size = ngQ) (hQ : ∀ i < ngQ, ElF H D.gQ[i]! (gQ i))
    (hUs : D.cu.size = ngQ) (hU : ∀ i < ngQ, ElFI H D.cu[i]! (cu i) (cui i))
    (hVs : D.cv.size = ngQ) (hV : ∀ i < ngQ, ElFI H D.cv[i]! (cv i) (cvi i))
    (hKs : D.gK.size = ngK) (hK : ∀ l < ngK, ElF H D.gK[l]! (gK l))
    (hRs : D.reps.size = m) (hR : ∀ j < m, ElFI H D.reps[j]! (R j) (Ri j))
    (hSs : D.sig.size = ngQ) (hsig : ∀ i < ngQ, ∀ j < m, (D.sig[i]!)[j]! = sig i j)
    (heQ : enumOK n D.gQ ps cQ = true) (hsQ : cQ.pts.size = NQ)
    (hpQ : ∀ i < NQ, ElF H cQ.pts[i]! (tq i))
    (heK : enumOK n D.gK ps cK = true) (hsK : cK.pts.size = NK)
    (hpK : ∀ i < NK, ElF H cK.pts[i]! (tk i))
    (heS : enumOK m D.sig (List.range m) cS = true) (hsS : cS.pts.size = NS)
    (h : tcRestF bs m xf ngQ gQ cu cv cui cvi ngK gK R Ri sig NQ tq NK tk NS = true) :
    tcOK n m ps x D cQ cK cS = true := by
  unfold tcRestF at h
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := h
  obtain ⟨hxv, hxr, hxH⟩ := hx
  have hrx : Rep n x (permOfArr n x) := rep_of_validA hxv
  have g2 : (cQ.pts.size == 3 * (m.factorial / 2)) = true :=
    beq_iff_eq.2 (hsQ.trans (Nat.eq_of_beq_eq_true c1))
  have g4 : eqA n (CFSG.Monster.B.Mathieu.powArr n x 3) (idA n) = true :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrx 3) rep_idA).2
      (eq_of_eqOnL hF (hxr.powF 3) RepF.one (H.pow_mem hxH 3) H.one_mem c2)
  have g5 : eqA n x (idA n) = false := by
    rw [bnot_eq, Bool.not_eq_true'] at c3
    rw [Bool.eq_false_iff]
    intro h1
    have e : permOfArr n x = 1 := (eqA_iff hrx rep_idA).1 h1
    have := eqOnL_of_eq hbs hxr (e ▸ RepF.one)
    rw [c3] at this
    exact Bool.false_ne_true this
  have g6 : allLt D.gQ.size (fun i => commA n D.gQ[i]! x) = true := by
    rw [allLt_iff, hQs]
    intro i hi
    obtain ⟨hv, hr, hm⟩ := hQ i hi
    have e : permOfArr n D.gQ[i]! * permOfArr n x = permOfArr n x * permOfArr n D.gQ[i]! :=
      eq_of_eqOnL hF (hr.comp hxr) (hxr.comp hr) (H.mul_mem hm hxH) (H.mul_mem hxH hm)
        (CFSG.KS.Raw.Orb.allN_iff.1 c4 i hi)
    exact (eqA_iff (rep_compA (rep_of_validA hv) hrx) (rep_compA hrx (rep_of_validA hv))).2 e
  have g7 : cQ.pts.toList.any (eqA n x) = true := any_of_memF hF hsQ hpQ hrx hxr hxH c5
  have g9 : (cK.pts.size * m == cQ.pts.size) = true := beq_iff_eq.2 (by
    rw [hsK, hsQ]
    exact Nat.eq_of_beq_eq_true c6)
  have g10 : cK.pts.toList.any (eqA n x) = true := any_of_memF hF hsK hpK hrx hxr hxH c7
  have g11 : allLt D.gK.size (fun l => cQ.pts.toList.any (eqA n D.gK[l]!)) = true := by
    rw [allLt_iff, hKs]
    intro l hl
    obtain ⟨hv, hr, hm⟩ := hK l hl
    exact any_of_memF hF hsQ hpQ (rep_of_validA hv) hr hm (CFSG.KS.Raw.Orb.allN_iff.1 c8 l hl)
  have g12 : (D.reps.size == m) = true := beq_iff_eq.2 hRs
  have g13 : allLt m (fun j => validA n D.reps[j]! &&
      cQ.pts.toList.any (eqA n D.reps[j]!)) = true := by
    rw [allLt_iff]
    intro j hj
    obtain ⟨⟨hv, hr, hm⟩, -⟩ := hR j hj
    rw [hv, any_of_memF hF hsQ hpQ (rep_of_validA hv) hr hm (CFSG.KS.Raw.Orb.allN_iff.1 c9 j hj)]
    rfl
  have g14 : allLt m (fun j => allLt m (fun k => (j == k) ||
      !(cK.pts.toList.any (eqA n (compA n (invCand n D.reps[j]!) D.reps[k]!))))) = true := by
    rw [allLt_iff]
    intro j hj
    rw [allLt_iff]
    intro k hk
    have d := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 c10 j hj) k hk
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hb : Nat.beq j k = false := by
        rw [Bool.eq_false_iff]
        intro e
        exact hjk (Nat.eq_of_beq_eq_true e)
      rw [hb, bnot_eq, Bool.not_eq_true'] at d
      obtain ⟨⟨hvj, -, -⟩, hrij⟩ := hR j hj
      obtain ⟨⟨hvk, hrk, -⟩, -⟩ := hR k hk
      have hnot : cK.pts.toList.any (eqA n (compA n (invCand n D.reps[j]!) D.reps[k]!)) =
          false := by
        rw [Bool.eq_false_iff]
        intro ha
        have := memF_of_any hbs hsK hpK (rep_compA (rep_inv_of_validA hvj) (rep_of_validA hvk))
          (hrij.comp hrk) ha
        rw [d] at this
        exact Bool.false_ne_true this
      rw [hnot]
      simp
  have g15 : (D.cu.size == D.gQ.size) = true := beq_iff_eq.2 (hUs.trans hQs.symm)
  have g16 : (D.cv.size == D.gQ.size) = true := beq_iff_eq.2 (hVs.trans hQs.symm)
  have g17 : allLt D.gQ.size (fun i => validA n D.cu[i]! && validA n D.cv[i]! &&
      cQ.pts.toList.any (eqA n D.cu[i]!) && cQ.pts.toList.any (eqA n D.cv[i]!) &&
      eqA n D.gQ[i]! (commutatorA n D.cu[i]! D.cv[i]!)) = true := by
    rw [allLt_iff, hQs]
    intro i hi
    have e := CFSG.KS.Raw.Orb.allN_iff.1 c11 i hi
    simp only [CFSG.KS.bAnd_iff] at e
    obtain ⟨u2, v2, e5⟩ := e
    obtain ⟨⟨hvu, hru, hmu⟩, hrui⟩ := hU i hi
    obtain ⟨⟨hvv, hrv, hmv⟩, hrvi⟩ := hV i hi
    obtain ⟨hvg, hrg, hmg⟩ := hQ i hi
    have hcomm : permOfArr n D.gQ[i]! = permOfArr n D.cu[i]! * (permOfArr n D.cv[i]! *
        ((permOfArr n D.cu[i]!)⁻¹ * (permOfArr n D.cv[i]!)⁻¹)) :=
      eq_of_eqOnL hF hrg (hru.comp (hrv.comp (hrui.comp hrvi))) hmg
        (H.mul_mem hmu (H.mul_mem hmv (H.mul_mem (H.inv_mem hmu) (H.inv_mem hmv)))) e5
    have hrc : Rep n (commutatorA n D.cu[i]! D.cv[i]!)
        (permOfArr n D.cu[i]! * permOfArr n D.cv[i]! *
          ((permOfArr n D.cu[i]!)⁻¹ * (permOfArr n D.cv[i]!)⁻¹)) :=
      rep_compA (rep_compA (rep_of_validA hvu) (rep_of_validA hvv))
        (rep_compA (rep_inv_of_validA hvu) (rep_inv_of_validA hvv))
    rw [hvu, hvv, any_of_memF hF hsQ hpQ (rep_of_validA hvu) hru hmu u2,
      any_of_memF hF hsQ hpQ (rep_of_validA hvv) hrv hmv v2,
      (eqA_iff (rep_of_validA hvg) hrc).2 (by rw [hcomm, mul_assoc])]
    rfl
  have g18 : (D.sig.size == D.gQ.size) = true := beq_iff_eq.2 (hSs.trans hQs.symm)
  have g19 : allLt D.gQ.size (fun i => allLt m (fun j => decide ((D.sig[i]!)[j]! < m) &&
      cK.pts.toList.any (eqA n (compA n (invCand n D.reps[(D.sig[i]!)[j]!]!)
        (compA n D.gQ[i]! D.reps[j]!))))) = true := by
    rw [allLt_iff, hQs]
    intro i hi
    rw [allLt_iff]
    intro j hj
    obtain ⟨s1, s2⟩ := (CFSG.KS.bAnd_iff _ _).1
      (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 c12 i hi) j hj)
    have hs : sig i j < m := by
      rw [Nat.blt_eq] at s1
      exact s1
    obtain ⟨⟨hvs, -, hms⟩, hrsi⟩ := hR _ hs
    obtain ⟨⟨hvj, hrj, hmj⟩, -⟩ := hR j hj
    obtain ⟨hvg, hrg, hmg⟩ := hQ i hi
    rw [hsig i hi j hj, decide_eq_true hs, Bool.true_and]
    exact any_of_memF hF hsK hpK
      (rep_compA (rep_inv_of_validA hvs) (rep_compA (rep_of_validA hvg) (rep_of_validA hvj)))
      (hrsi.comp (hrg.comp hrj)) (H.mul_mem (H.inv_mem hms) (H.mul_mem hmg hmj)) s2
  have g21 : (cS.pts.size == m.factorial / 2) = true :=
    beq_iff_eq.2 (hsS.trans (Nat.eq_of_beq_eq_true c13))
  unfold tcOK
  rw [heQ, g2, hxv, g4, g5, g6, g7, heK, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    heS, g21]
  rfl

end CFSG.KC.TcF

end
