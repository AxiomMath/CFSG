module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Kit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426

variable {n : ℕ}

theorem caseOK_card_sound {D : Data} {k : Case} {x : Array ℕ} {A B : Equiv.Perm (Fin D.n)}
    (hA : Rep D.n D.A A) (hB : Rep D.n D.B B) (h : caseOK D k x = true) :
    permOfArr D.n x ^ 3 = 1 ∧
      Nat.card ↥(centralizer {permOfArr D.n x} ⊓ closure {A, B}) = k.card := by
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
  exact hCcard

theorem card_centralizer_conj_class {P : Subgroup (Equiv.Perm (Fin n))} {X k : Equiv.Perm (Fin n)}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Nat.card ↥(centralizer {k * X ^ e * k⁻¹} ⊓ P) = Nat.card ↥(centralizer {X} ⊓ P) := by
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
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem check_card_order_sound (D : Data) {A B : Equiv.Perm (Fin D.n)} (hA : Rep D.n D.A A)
    (hB : Rep D.n D.B B) (h : check D = true) :
    Nat.card ↥(closure {A, B}) = D.ord ∧
      ∀ x ∈ closure {A, B}, orderOf x = 3 → ∃ c < D.cases.size,
        Nat.card ↥(centralizer {x} ⊓ closure {A, B}) = D.cases[c]!.card := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hprod⟩, hord⟩, hm3⟩, hN3⟩, hlines⟩, hsift⟩, htrans⟩, hrec⟩, hsz⟩,
    hcases⟩ := h
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
  refine ⟨hcardP, ?_⟩
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
  obtain ⟨hX3, hcardC⟩ := caseOK_card_sound hA hB (allLt_spec hcases hcj)
  refine ⟨D.recs.getD j 0, hcj, ?_⟩
  rw [card_centralizer_conj_class hX3 hk he, hcardC]

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem sporL3DownInner_of_check {s : TauCeti.SporadicName} (D : B3S3.Data)
    (hD : B3S3.check D = true) {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (P : Subgroup (Equiv.Perm (Fin D.n))) (hP : P = Subgroup.closure {A, B})
    (hM : Nonempty (↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (hord : NoL3Eq D.ord)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card < 20160) : SporL3DownInner s := by
  subst hP
  obtain ⟨hcardP, hcls⟩ := B3S3.check_card_order_sound D hA hB hD
  refine sporL3DownInner_of_model _ hM (by rw [hcardP]; exact hord) ?_
  intro x hx
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  have hmapc := map_centralizer_subtype (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
