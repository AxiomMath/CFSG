module

public import Certificates.Data.OmegaAutQ
public import Certificates.Data.Kernel.OmegaAutQ.Poly

public section

namespace CFSG.KC.OmegaAutQ

open Certificates.OmegaAutQ CFSG.KD.OmegaAutQ

section Transfer

variable {G : Type} [Mul G] [One G] [DecidableEq G]

structure Good (ι : G → S81) : Prop where
  inj : Function.Injective ι
  mul : ∀ a b, ι (a * b) = ι a * ι b
  one : ι 1 = 1

variable {ι : G → S81} (h : Good ι)
include h

theorem mem_map' (a : G) (L : List G) : ι a ∈ L.map ι ↔ a ∈ L := by
  simp only [List.mem_map, h.inj.eq_iff, exists_eq_right]

theorem span1_map (g : G) (T : List G) : span1 (ι g) (T.map ι) = (span1P g T).map ι := by
  simp only [span1, span1P, tabP_eq, List.map_append, List.map_map, Function.comp_def, h.mul]

theorem commL_map (L : List G) (g : G) : commL (L.map ι) (ι g) = (commLP L g).map ι := by
  simp only [commL, commLP, List.filter_map, Function.comp_def, ← h.mul, h.inj.eq_iff]

theorem firstOut_map (Q T : List G) : firstOut (Q.map ι) (T.map ι) = ι (firstOutP Q T) := by
  simp only [firstOut, firstOutP, List.find?_map, Function.comp_def, mem_map' h]
  cases (Q.find? fun x => decide (x ∉ T)) with
  | none => exact h.one.symm
  | some x => rfl

theorem conjPairs_map (B T : List G) (g : G) :
    conjPairs (B.map ι) (T.map ι) (ι g) = (conjPairsP B T g).map (Prod.map ι ι) := by
  simp only [conjPairs, conjPairsP, List.flatMap_map, List.map_flatMap, List.filter_map,
    List.map_map, Function.comp_def, ← h.mul, h.inj.eq_iff, Prod.map_apply]

theorem imgAux_map (Q : List G) (g : G) (s : Bool) (ps : List (G × G)) :
    imgAux (Q.map ι) (ι g) s (ps.map (Prod.map ι ι)) = (imgAuxP Q g s ps).map ι := by
  simp only [imgAux, imgAuxP, List.filter_map, List.all_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, ← h.mul, h.inj.eq_iff]

theorem imgCand_map (Q B T : List G) (g : G) :
    imgCand (Q.map ι) (B.map ι) (T.map ι) (ι g) = (imgCandP Q B T g).map ι := by
  simp only [imgCand, imgCandP, ← h.mul, mem_map' h, conjPairs_map h, imgAux_map h]

theorem candsOf_map (Q B T : List G) (g1 g2 : G) :
    candsOf (Q.map ι) (B.map ι) (T.map ι) (ι g1) (ι g2) =
      (candsOfP Q B T g1 g2).map (Prod.map ι ι) := by
  simp only [candsOf, candsOfP, imgCand_map h, List.filter_map, List.flatMap_map,
    List.map_flatMap, List.map_map, List.all_map, Function.comp_def, ← h.mul, h.inj.eq_iff,
    Prod.map_apply]

theorem leafOf_map (Q B T : List G) (g1 g2 : G) :
    leafOf (Q.map ι) (B.map ι) (T.map ι) (ι g1) (ι g2) = leafOfP Q B T g1 g2 := by
  simp only [leafOf, leafOfP, mem_map' h, span1_map h, List.all_map, Function.comp_def,
    candsOf_map h, List.length_map]

theorem leaf_map (Q B T : List G) : leaf (Q.map ι) (B.map ι) (T.map ι) = leafP Q B T := by
  simp only [leaf, leafP, firstOut_map h, span1_map h, leafOf_map h]

theorem snoc_map (B : List G) (c : G) : B.map ι ++ [ι c] = (B ++ [c]).map ι := by
  simp only [List.map_append, List.map_cons, List.map_nil]

theorem level2_map (Q B T2 Iab : List G) :
    level2 (Q.map ι) (B.map ι) (T2.map ι) (Iab.map ι) = level2P Q B T2 Iab := by
  simp only [level2, level2P, List.all_map, Function.comp_def, mem_map' h, span1_map h,
    snoc_map h, leaf_map h]

theorem level1_map (Q B T1 Ia : List G) :
    level1 (Q.map ι) (B.map ι) (T1.map ι) (Ia.map ι) = level1P Q B T1 Ia := by
  simp only [level1, level1P, List.all_map, Function.comp_def, mem_map' h, span1_map h,
    snoc_map h, commL_map h, level2_map h]

theorem chainChk_map (Q I : List G) : chainChk (Q.map ι) (I.map ι) = chainChkP Q I := by
  have h1 : ([1] : List S81) = ([1] : List G).map ι := by
    simp only [List.map_cons, List.map_nil, h.one]
  simp only [chainChk, chainChkP, List.all_map, Function.comp_def, commL_map h]
  congr 1
  funext a
  have e : ([ι a] : List S81) = [a].map ι := rfl
  rw [h1, span1_map h, e, level1_map h]

theorem invsOf_map (Q : List G) : invsOf (Q.map ι) = (invsOfP Q).map ι := by
  simp only [invsOf, invsOfP, List.filter_map, Function.comp_def, ← h.mul, ← h.one, ne_eq,
    h.inj.eq_iff]

end Transfer

theorem allLt_iff {m : ℕ} {f : ℕ → Bool} : allLt m f = true ↔ ∀ k < m, f k = true := by
  induction m with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ m ih =>
    have e : allLt (m + 1) f = (allLt m f && f m) := rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h m (by omega)⟩

theorem pwFilter_congr_mem {α : Type} {R R' : α → α → Prop} {dR : DecidableRel R}
    [DecidableRel R'] (l : List α) (hR : ∀ a ∈ l, ∀ b ∈ l, (R a b ↔ R' a b)) :
    l.pwFilter R = l.pwFilter R' := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih fun a ha b hb => hR a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have hx : (∀ y ∈ xs.pwFilter R', R x y) ↔ ∀ y ∈ xs.pwFilter R', R' x y := by
      refine forall₂_congr fun y hy => hR x (by simp) y
        (List.mem_cons_of_mem _ (List.pwFilter_subset xs hy))
    by_cases hc : ∀ y ∈ xs.pwFilter R', R' x y
    · rw [List.pwFilter_cons_of_pos (by rw [ih']; exact hx.2 hc), List.pwFilter_cons_of_pos hc, ih']
    · rw [List.pwFilter_cons_of_neg (by rw [ih']; exact fun h' => hc (hx.1 h')),
        List.pwFilter_cons_of_neg hc, ih']

@[expose] def phi (p : ℕ × ℕ) : S81 :=
  thetaHom ((q8List ()).getD p.1 1, 1) * thetaHom (1, (q8List ()).getD p.2 1)

@[expose] def psi (tP i : ℕ) : S81 := phi (pairOf tP i)

theorem qmList_pairs : qmList () = (pairs64.map phi).dedup := by
  simp only [qmList, tabP_eq]
  congr 1

theorem mem_pairs64 {p : ℕ × ℕ} (hp : p ∈ pairs64) : p.1 < 8 ∧ p.2 < 8 := by
  simp only [pairs64, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, l, hl, rfl⟩ := hp
  exact ⟨hk, hl⟩

theorem pairOf_lt (tP i : ℕ) : (pairOf tP i).1 < 8 ∧ (pairOf tP i).2 < 8 := by
  have h : laneW 6 tP i < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact ⟨by simp only [pairOf]; omega, by simp only [pairOf]; omega⟩

section Tables

variable {tA tB : ℕ → ℕ}
  (hA : ∀ k < 8, ∀ x : Fin 81, (thetaHom ((q8List ()).getD k 1, 1) x).val = laneW 7 (tA k) x.val)
  (hB : ∀ l < 8, ∀ x : Fin 81, (thetaHom (1, (q8List ()).getD l 1) x).val = laneW 7 (tB l) x.val)
include hA hB

theorem phi_apply {p : ℕ × ℕ} (hp1 : p.1 < 8) (hp2 : p.2 < 8) (x : Fin 81) :
    (phi p x).val = imgP tA tB p.1 p.2 x.val := by
  simp only [phi, Equiv.Perm.mul_apply, imgP]
  rw [hA _ hp1, hB _ hp2]

theorem phi_eq_iff {p q : ℕ × ℕ} (hp1 : p.1 < 8) (hp2 : p.2 < 8) (hq1 : q.1 < 8) (hq2 : q.2 < 8) :
    phi p = phi q ↔ (sigNe tA tB p q = false) := by
  have : sigNe tA tB p q = false ↔ allLt 81 (fun x => imgP tA tB p.1 p.2 x == imgP tA tB q.1 q.2 x)
      = true := by
    unfold sigNe
    cases allLt 81 (fun x => imgP tA tB p.1 p.2 x == imgP tA tB q.1 q.2 x) <;> simp
  rw [this, allLt_iff, Equiv.ext_iff]
  constructor
  · intro h x hx
    have := congrArg Fin.val (h ⟨x, hx⟩)
    rw [phi_apply hA hB hp1 hp2, phi_apply hA hB hq1 hq2] at this
    simpa using this
  · intro h x
    apply Fin.ext
    rw [phi_apply hA hB hp1 hp2, phi_apply hA hB hq1 hq2]
    simpa using h x.val x.isLt

theorem qmList_eq {tP : ℕ}
    (hD : pairs64.pwFilter (fun p q => sigNe tA tB p q = true) = (List.range 32).map (pairOf tP)) :
    qmList () = (List.range 32).map (psi tP) := by
  rw [qmList_pairs, List.dedup, List.pwFilter_map]
  rw [pwFilter_congr_mem (R' := fun p q => sigNe tA tB p q = true) pairs64 fun p hp q hq => by
      obtain ⟨hp1, hp2⟩ := mem_pairs64 hp
      obtain ⟨hq1, hq2⟩ := mem_pairs64 hq
      simp [phi_eq_iff hA hB hp1 hp2 hq1 hq2]]
  rw [hD, List.map_map]
  rfl

end Tables

theorem check_of {tA tB : ℕ → ℕ} {tP t e : ℕ}
    (hA : ∀ k < 8, ∀ x : Fin 81, (thetaHom ((q8List ()).getD k 1, 1) x).val = laneW 7 (tA k) x.val)
    (hB : ∀ l < 8, ∀ x : Fin 81, (thetaHom (1, (q8List ()).getD l 1) x).val = laneW 7 (tB l) x.val)
    (hD : pairs64.pwFilter (fun p q => sigNe tA tB p q = true) = (List.range 32).map (pairOf tP))
    (hM : mulChk tA tB tP t = true) (he : e < 32) (hO : oneChk tA tB tP e = true)
    (hC : chainChkP (lq t e) (invsOfP (lq t e)) = true) : check () = true := by
  have hq := qmList_eq hA hB hD
  have hpsi : ∀ i x, (psi tP i x).val = imgI tA tB tP i x.val := fun i x =>
    phi_apply hA hB (pairOf_lt tP i).1 (pairOf_lt tP i).2 x
  let ι : QT t e → S81 := fun q => psi tP q.v.val
  have hnd : ((List.range 32).map (psi tP)).Nodup := hq ▸ List.nodup_dedup _
  have hG : Good ι := by
    refine ⟨fun a b hab => ?_, fun a b => ?_, ?_⟩
    · have := List.inj_on_of_nodup_map hnd (List.mem_range.2 a.v.isLt) (List.mem_range.2 b.v.isLt)
        hab
      exact QT.eq_iff.2 this
    · refine Equiv.ext fun x => Fin.ext ?_
      simp only [ι]
      rw [Equiv.Perm.mul_apply, hpsi, hpsi, hpsi]
      have := (allLt_iff.1 ((allLt_iff.1 (allLt_iff.1 hM a.v.val a.v.isLt)) b.v.val b.v.isLt))
        x.val x.isLt
      exact (beq_iff_eq.1 this).symm
    · refine Equiv.ext fun x => Fin.ext ?_
      have hm : (1 : QT t e).v.val = e := Nat.mod_eq_of_lt he
      change (psi tP (1 : QT t e).v.val x).val = x.val
      rw [hpsi, hm]
      exact beq_iff_eq.1 (allLt_iff.1 hO x.val x.isLt)
  have hl : qmList () = (lq t e).map ι := by
    rw [hq, lq, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, ι, Nat.mod_eq_of_lt (List.mem_range.1 hi)]
  simp only [check]
  rw [hl, invsOf_map hG, chainChk_map hG]
  exact hC

end CFSG.KC.OmegaAutQ
