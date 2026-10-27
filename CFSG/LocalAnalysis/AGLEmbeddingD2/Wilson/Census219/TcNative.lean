module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TripleCoverKit
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Mathieu.SylowSound

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu Subgroup Equiv
open scoped commutatorElement

structure TcData where
  gQ : Array (Array ℕ)
  cu : Array (Array ℕ)
  cv : Array (Array ℕ)
  gK : Array (Array ℕ)
  reps : Array (Array ℕ)
  sig : Array (Array ℕ)

@[expose] def tcOK (N m : ℕ) (ps : List ℕ) (x : Array ℕ) (D : TcData) (cQ cK cS : ArrCert) : Bool :=
  enumOK N D.gQ ps cQ && (cQ.pts.size == 3 * (m.factorial / 2)) &&
  validA N x && eqA N (powArr N x 3) (idA N) && !(eqA N x (idA N)) &&
  allLt D.gQ.size (fun i => commA N D.gQ[i]! x) &&
  cQ.pts.toList.any (eqA N x) &&
  enumOK N D.gK ps cK && (cK.pts.size * m == cQ.pts.size) && cK.pts.toList.any (eqA N x) &&
  allLt D.gK.size (fun l => cQ.pts.toList.any (eqA N D.gK[l]!)) &&
  (D.reps.size == m) &&
  allLt m (fun j => validA N D.reps[j]! && cQ.pts.toList.any (eqA N D.reps[j]!)) &&
  allLt m (fun j => allLt m (fun k => (j == k) ||
    !(cK.pts.toList.any (eqA N (compA N (invCand N D.reps[j]!) D.reps[k]!))))) &&
  (D.cu.size == D.gQ.size) && (D.cv.size == D.gQ.size) &&
  allLt D.gQ.size (fun i => validA N D.cu[i]! && validA N D.cv[i]! &&
    cQ.pts.toList.any (eqA N D.cu[i]!) && cQ.pts.toList.any (eqA N D.cv[i]!) &&
    eqA N D.gQ[i]! (commutatorA N D.cu[i]! D.cv[i]!)) &&
  (D.sig.size == D.gQ.size) &&
  allLt D.gQ.size (fun i => allLt m (fun j => decide ((D.sig[i]!)[j]! < m) &&
    cK.pts.toList.any (eqA N (compA N (invCand N D.reps[(D.sig[i]!)[j]!]!)
      (compA N D.gQ[i]! D.reps[j]!))))) &&
  enumOK m D.sig (List.range m) cS && (cS.pts.size == m.factorial / 2)

theorem tcOK_parts {N m : ℕ} {ps : List ℕ} {x : Array ℕ} {D : TcData} {cQ cK cS : ArrCert}
    (h : tcOK N m ps x D cQ cK cS = true) :
    enumOK N D.gQ ps cQ = true ∧ cQ.pts.size = 3 * (m.factorial / 2) ∧
    validA N x = true ∧ eqA N (powArr N x 3) (idA N) = true ∧ eqA N x (idA N) = false ∧
    allLt D.gQ.size (fun i => commA N D.gQ[i]! x) = true ∧
    cQ.pts.toList.any (eqA N x) = true ∧
    enumOK N D.gK ps cK = true ∧ cK.pts.size * m = cQ.pts.size ∧ cK.pts.toList.any (eqA N x) = true ∧
    allLt D.gK.size (fun l => cQ.pts.toList.any (eqA N D.gK[l]!)) = true ∧
    D.reps.size = m ∧
    allLt m (fun j => validA N D.reps[j]! && cQ.pts.toList.any (eqA N D.reps[j]!)) = true ∧
    allLt m (fun j => allLt m (fun k => (j == k) ||
      !(cK.pts.toList.any (eqA N (compA N (invCand N D.reps[j]!) D.reps[k]!))))) = true ∧
    D.cu.size = D.gQ.size ∧ D.cv.size = D.gQ.size ∧
    allLt D.gQ.size (fun i => validA N D.cu[i]! && validA N D.cv[i]! &&
      cQ.pts.toList.any (eqA N D.cu[i]!) && cQ.pts.toList.any (eqA N D.cv[i]!) &&
      eqA N D.gQ[i]! (commutatorA N D.cu[i]! D.cv[i]!)) = true ∧
    D.sig.size = D.gQ.size ∧
    allLt D.gQ.size (fun i => allLt m (fun j => decide ((D.sig[i]!)[j]! < m) &&
      cK.pts.toList.any (eqA N (compA N (invCand N D.reps[(D.sig[i]!)[j]!]!)
        (compA N D.gQ[i]! D.reps[j]!))))) = true ∧
    enumOK m D.sig (List.range m) cS = true ∧ cS.pts.size = m.factorial / 2 := by
  simp only [tcOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc] at h
  exact h

section Spec

variable {N m : ℕ} {ps : List ℕ}

theorem any_of_mem {gs : Array (Array ℕ)} {c : ArrCert} (hps : ∀ p ∈ ps, p < N)
    (h : enumOK N gs ps c = true) {t : Array ℕ} {X : Perm (Fin N)} (ht : Rep N t X)
    (hX : X ∈ closure (permsA N gs)) : c.pts.toList.any (eqA N t) = true := by
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hps h hX
  rw [List.any_eq_true]
  refine ⟨c.pts[i]!, ?_, (eqA_iff ht hrep).2 rfl⟩
  rw [getElem!_pos c.pts i hi]
  exact Array.getElem_mem_toList hi

theorem tcOK_spec {x : Array ℕ} {D : TcData} {cQ cK cS : ArrCert} (hps : ∀ p ∈ ps, p < N)
    (hm : 5 ≤ m) (h : tcOK N m ps x D cQ cK cS = true) :
    permOfArr N x ∈ closure (permsA N D.gQ) ∧
    CFSG.IsQuasisimple ↥(closure (permsA N D.gQ)) ∧
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover ↥(closure (permsA N D.gQ))
      (alternatingGroup (Fin m)) := by
  obtain ⟨hQe, hQc, hxv, hx3, hx1, hxcomm, hxQ, hKe, hKc, hxK, hKQ, hrs, hrQ, hdist, hcu, hcv,
    hcomms, hsig, hact, hSe, hSc⟩ := tcOK_parts h
  set Q := closure (permsA N D.gQ) with hQdef
  set K := closure (permsA N D.gK) with hKdef
  have hrx : Rep N x (permOfArr N x) := rep_of_validA hxv
  have hXQ : permOfArr N x ∈ Q := enumOK_mem_of_any hps hQe hrx hxQ
  have hXK : permOfArr N x ∈ K := enumOK_mem_of_any hps hKe hrx hxK
  have hKleQ : K ≤ Q := by
    rw [hKdef, closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any hps hQe (rep_of_validA (enumOK_gens_valid hKe hl)) (allLt_spec hKQ hl)
  have : Nontrivial (Fin m) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQcard : Nat.card Q = 3 * Nat.card (alternatingGroup (Fin m)) := by
    rw [(enumOK_spec hps hQe).2.1, hQc, nat_card_alternatingGroup, Nat.card_fin]
  have hKcard : Nat.card K * m = Nat.card Q := by
    rw [(enumOK_spec hps hQe).2.1, (enumOK_spec hps hKe).2.1, hKc]
  have hX3 : permOfArr N x ^ 3 = 1 := (eqA_iff (rep_powArr hrx 3) rep_idA).1 hx3
  have hX1 : permOfArr N x ≠ 1 := fun h1 => by
    have := (eqA_iff hrx rep_idA).2 h1
    rw [hx1] at this
    exact Bool.false_ne_true this
  have hXord : orderOf (permOfArr N x) = 3 := orderOf_eq_prime hX3 hX1
  have hcent : ∀ y ∈ Q, Commute y (permOfArr N x) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact (commA_iff (rep_of_validA (enumOK_gens_valid hQe hi)) hrx).1 (allLt_spec hxcomm hi)
    | one => exact Commute.one_left _
    | mul y z _ _ hy hz => exact hy.mul_left hz
    | inv y _ hy => exact hy.inv_left
  have hperf : Group.IsPerfect ↥Q := by
    rw [Subgroup.isPerfect_iff]
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    · rw [hQdef, closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have h5 := allLt_spec hcomms hi
      simp only [Bool.and_eq_true] at h5
      obtain ⟨⟨⟨⟨hu, hv⟩, hu'⟩, hv'⟩, hc⟩ := h5
      have hcu' : D.cu.size > i := by rw [hcu]; exact hi
      have hcv' : D.cv.size > i := by rw [hcv]; exact hi
      have huQ : permOfArr N D.cu[i]! ∈ Q := enumOK_mem_of_any hps hQe (rep_of_validA hu) hu'
      have hvQ : permOfArr N D.cv[i]! ∈ Q := enumOK_mem_of_any hps hQe (rep_of_validA hv) hv'
      have hg : permOfArr N D.gQ[i]! = ⁅permOfArr N D.cu[i]!, permOfArr N D.cv[i]!⁆ :=
        (eqA_iff (rep_of_validA (enumOK_gens_valid hQe hi)) (rep_commutatorA hu hv)).1 hc
      change permOfArr N D.gQ[i]! ∈ _
      rw [hg]
      exact Subgroup.commutator_mem_commutator huQ hvQ
  have hKQ' : K ≤ Q := hKleQ
  set K' : Subgroup ↥Q := K.subgroupOf Q with hK'def
  have hK'card : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ').toEquiv
  have hidx : Nat.card (↥Q ⧸ K') = m := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
    rw [hK'card] at h1
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have : Nat.card K * m = Nat.card K * Nat.card (↥Q ⧸ K') := by rw [hKcard, h1, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hKpos this).symm
  have hrQ' : ∀ j < m, validA N D.reps[j]! = true ∧ cQ.pts.toList.any (eqA N D.reps[j]!) = true :=
    fun j hj => by
      have := allLt_spec hrQ hj
      simp only [Bool.and_eq_true] at this
      exact this
  have hrmem : ∀ j : Fin m, permOfArr N D.reps[(j : ℕ)]! ∈ Q := fun j =>
    enumOK_mem_of_any hps hQe (rep_of_validA (hrQ' j j.2).1) (hrQ' j j.2).2
  set rj : Fin m → ↥Q := fun j => ⟨permOfArr N D.reps[(j : ℕ)]!, hrmem j⟩ with hrj
  set f : Fin m → ↥Q ⧸ K' := fun j => ((rj j : ↥Q) : ↥Q ⧸ K') with hfdef
  have hinj : Function.Injective f := by
    intro j k hjk
    by_contra hne
    have hmem : (rj j)⁻¹ * rj k ∈ K' := QuotientGroup.eq.1 hjk
    have hmemK : (permOfArr N D.reps[(j : ℕ)]!)⁻¹ * permOfArr N D.reps[(k : ℕ)]! ∈ K := hmem
    have hany := any_of_mem hps hKe
      (rep_compA (rep_inv_of_validA (hrQ' j j.2).1) (rep_of_validA (hrQ' k k.2).1)) hmemK
    have hd := allLt_spec (allLt_spec hdist j.2) k.2
    have hjk' : ((j : ℕ) == (k : ℕ)) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun he => hne (Fin.ext he)
    rw [hjk', Bool.false_or, Bool.not_eq_true'] at hd
    rw [hd] at hany
    exact Bool.false_ne_true hany
  have hf : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hidx, Nat.card_fin])
  set e : ↥Q ⧸ K' ≃ Fin m := (Equiv.ofBijective f hf).symm with he
  set π : ↥Q →* Perm (Fin m) := cosetPerm K' e with hπdef
  have hgQmem : ∀ i < D.gQ.size, permOfArr N D.gQ[i]! ∈ Q := fun i hi =>
    Subgroup.subset_closure (mem_permsA hi)
  have hπ : ∀ i (hi : i < D.gQ.size),
      π ⟨permOfArr N D.gQ[i]!, hgQmem i hi⟩ = permOfArr m D.sig[i]! := by
    intro i hi
    have hisig : i < D.sig.size := by rw [hsig]; exact hi
    have hsv : validA m D.sig[i]! = true := enumOK_gens_valid hSe hisig
    have hesymm : ∀ b : Fin m, e.symm b = f b := fun b => by simp [he]
    apply Equiv.ext
    intro j
    show cosetPerm K' e ⟨permOfArr N D.gQ[i]!, hgQmem i hi⟩ j = _
    rw [cosetPerm_apply, hesymm j]
    have hsm : (⟨permOfArr N D.gQ[i]!, hgQmem i hi⟩ : ↥Q) • f j =
        ((⟨permOfArr N D.gQ[i]!, hgQmem i hi⟩ * rj j : ↥Q) : ↥Q ⧸ K') := rfl
    rw [hsm, ← Equiv.eq_symm_apply, hesymm]
    apply QuotientGroup.eq.2
    set k : Fin m := permOfArr m D.sig[i]! j with hk
    have hkv : (k : ℕ) = (D.sig[i]!)[(j : ℕ)]! := ((rep_of_validA hsv).apply j.2).symm
    have hact' := allLt_spec (allLt_spec hact hi) j.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hact'
    have hgv : validA N D.gQ[i]! = true := enumOK_gens_valid hQe hi
    have hrk : Rep N (compA N (invCand N D.reps[(D.sig[i]!)[(j : ℕ)]!]!)
        (compA N D.gQ[i]! D.reps[(j : ℕ)]!))
        ((permOfArr N D.reps[(D.sig[i]!)[(j : ℕ)]!]!)⁻¹ *
          (permOfArr N D.gQ[i]! * permOfArr N D.reps[(j : ℕ)]!)) :=
      rep_compA (rep_inv_of_validA (hrQ' _ hact'.1).1)
        (rep_compA (rep_of_validA hgv) (rep_of_validA (hrQ' j j.2).1))
    have hmemK := enumOK_mem_of_any hps hKe hrk hact'.2
    rw [← hkv] at hmemK
    show ((permOfArr N D.gQ[i]! * permOfArr N D.reps[(j : ℕ)]!)⁻¹ *
      permOfArr N D.reps[(k : ℕ)]!) ∈ K
    have := K.inv_mem hmemK
    rwa [mul_inv_rev, inv_inv] at this
  have hSgen : ∀ l < D.sig.size, permOfArr m D.sig[l]! ∈ π.range := by
    intro l hl
    rw [hsig] at hl
    exact ⟨⟨permOfArr N D.gQ[l]!, hgQmem l hl⟩, hπ l hl⟩
  have hSclos : closure (permsA m D.sig) = alternatingGroup (Fin m) := by
    apply eq_alternatingGroup_of_card (by omega)
    rw [(enumOK_spec (fun p hp => List.mem_range.1 hp) hSe).2.1, hSc, nat_card_alternatingGroup,
      Nat.card_fin]
  have hA : alternatingGroup (Fin m) ≤ π.range := by
    rw [← hSclos, closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hSgen l hl
  set xQ : ↥Q := ⟨permOfArr N x, hXQ⟩ with hxQ'
  have hxc : xQ ∈ center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g.1 g.2).eq
  have hxk : π xQ = 1 :=
    cosetPerm_eq_one_of_central K' e hxc (show permOfArr N x ∈ K from hXK)
  have hxo : orderOf xQ = 3 := by rw [hxQ', Subgroup.orderOf_mk]; exact hXord
  obtain ⟨-, -, -, hq, ht⟩ := tripleCover_of_range hm π hxo hxc hxk hA hQcard hperf
  exact ⟨hXQ, hq, ht⟩

end Spec

end CFSG.AGLEmbeddingD2.Wilson.Census219
