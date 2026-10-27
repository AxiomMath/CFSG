module

public import CFSG.Certificates.Kernel.SporSch.Co1RankTabSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankTab CFSG.KC.Co1B CFSG.KC.Co1Cl
  CFSG.KC.Co1RankBnd CFSG.Sporadic.Co1Schreier

@[expose] noncomputable def qPackRk (B : List ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => oneK
  | n + 1 => if v.testBit n then mulWK (qPackRk B v n) (getM B n) else qPackRk B v n

theorem qPackRk_congr (B : List ℕ) : ∀ n {u v : ℕ}, (∀ s < n, u.testBit s = v.testBit s) →
    qPackRk B u n = qPackRk B v n
  | 0, _, _, _ => rfl
  | n + 1, u, v, h => by
    rw [qPackRk, qPackRk, h n (Nat.lt_succ_self n),
      qPackRk_congr B n fun s hs => h s (Nat.lt_succ_of_lt hs)]

theorem qPackRk_high (B : List ℕ) {n v : ℕ} (hv : v < 2 ^ n) : ∀ k, qPackRk B v (n + k) = qPackRk B v n
  | 0 => rfl
  | k + 1 => by
    rw [← Nat.add_assoc, qPackRk, Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by norm_num) (by omega))), if_neg Bool.false_ne_true, qPackRk_high B hv k]

theorem qOf_eq_qPackRk (D : Co1RankTab.Dat) (v : ℕ) : ∀ n, Nat.rec (motive := fun _ => ℕ) oneK
    (fun s acc => nIf(Nat.beq (Nat.land (Nat.shiftRight v s) 1) 1,
      strictN acc fun a => mulWK a (getM D.BS s), acc)) n = qPackRk D.BS v n
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => ℕ) _ _ (bitB v n) = _
    rw [qPackRk, bitB_eq]
    cases v.testBit n
    · exact qOf_eq_qPackRk D v n
    · change strictN _ _ = _
      rw [strictN_eq, qOf_eq_qPackRk D v n]
      rfl

set_option exponentiation.threshold 600 in
theorem mulWK_lt_rk (A B : ℕ) : mulWK A B < 2 ^ (24 * 24) := by
  rw [mulWK, CFSG.KC.F2W.mulW_eq, CFSG.KC.F2W.mulF_eq_orN]
  exact CFSG.KC.F2W.orN_fields_lt fun i _ => CFSG.KC.F2W.vmF_lt _ _ _

theorem oneK_lt_rk : oneK < 2 ^ (24 * 24) := by
  decide +kernel

theorem matK_entry_rk (X : ℕ) (i j : Fin 24) :
    matK X i j = if X.testBit (j.val + 24 * i.val) then 1 else 0 := by
  simp only [matK, CFSG.Sporadic.SmallF2.rowsMatrix, CFSG.Sporadic.SmallF2.toVecD, Matrix.of_apply,
    CFSG.KC.Co1F2.unpackR, Array.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true j.isLt, Bool.true_and]

set_option exponentiation.threshold 600 in
theorem matK_inj_rk {A B : ℕ} (hA : A < 2 ^ (24 * 24)) (hB : B < 2 ^ (24 * 24))
    (h : matK A = matK B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 24 * 24
  · have e1 := matK_entry_rk A ⟨b / 24, by omega⟩ ⟨b % 24, by omega⟩
    have e2 := matK_entry_rk B ⟨b / 24, by omega⟩ ⟨b % 24, by omega⟩
    rw [h, e2] at e1
    have hb' : b % 24 + 24 * (b / 24) = b := by omega
    simp only [hb'] at e1
    cases hA' : A.testBit b <;> cases hB' : B.testBit b
    · rfl
    · rw [hA', hB'] at e1
      exact absurd e1 (by decide)
    · rw [hA', hB'] at e1
      exact absurd e1 (by decide)
    · rfl
  · have hle : 2 ^ (24 * 24) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA hle), Nat.testBit_lt_two_pow (lt_of_lt_of_le hB hle)]

theorem qPackRk_lt (B : List ℕ) (v : ℕ) : ∀ n, qPackRk B v n < 2 ^ (24 * 24)
  | 0 => oneK_lt_rk
  | n + 1 => by
    rw [qPackRk]
    split
    · exact mulWK_lt_rk _ _
    · exact qPackRk_lt B v n

theorem getM_eq_rk : ∀ (B : List ℕ) (n : ℕ) (h : n < B.length), getM B n = B[n]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: B, n + 1, h => getM_eq_rk B n (by simpa using h)

theorem mapB_rk (b : ℕ) (L : List ℕ) :
    List.rec (motive := fun _ => List ℕ) [] (fun a _ ih => List.cons (mulWK a b) ih) L =
      L.map fun a => mulWK a b := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, ← ih]

theorem noOne_rk : ∀ L : List ℕ, List.rec (motive := fun _ => Bool) true
    (fun x _ ih2 => bIf(Nat.beq x oneK, false, ih2)) L = true → ∀ x ∈ L, x ≠ oneK
  | [], _, _, hx => absurd hx List.not_mem_nil
  | y :: L, h, x, hx => by
    cases hy : Nat.beq y oneK
    · have h' : List.rec (motive := fun _ => Bool) true
          (fun x _ ih2 => bIf(Nat.beq x oneK, false, ih2)) L = true := by
        change Bool.rec (motive := fun _ => Bool) _ false (Nat.beq y oneK) = true at h
        rw [hy] at h
        exact h
      rcases List.mem_cons.1 hx with rfl | hx
      · intro e
        rw [e, Nat.beq_refl] at hy
        exact absurd hy (by decide)
      · exact noOne_rk L h' x hx
    · change Bool.rec (motive := fun _ => Bool) _ false (Nat.beq y oneK) = true at h
      rw [hy] at h
      exact absurd h Bool.false_ne_true

theorem doubling_rk (B : List ℕ) : ∀ k n (L : List ℕ), n + k = B.length →
    L = (List.range (2 ^ n)).map (fun v => qPackRk B v n) →
    List.rec (motive := fun _ => List ℕ → Bool) (fun _ => true)
      (fun b _ ih L =>
        (fun L' => bAnd(List.rec (motive := fun _ => Bool) true
          (fun x _ ih2 => bIf(Nat.beq x oneK, false, ih2)) L', ih (List.append L L')))
        (List.rec (motive := fun _ => List ℕ) [] (fun a _ ih => List.cons (mulWK a b) ih) L))
      (B.drop n) L = true →
    ∀ v, 2 ^ n ≤ v → v < 2 ^ (n + k) → qPackRk B v (n + k) ≠ oneK
  | 0, n, _, _, _, _, v, h1, h2 => absurd h2 (by rw [Nat.add_zero]; omega)
  | k + 1, n, L, hk, hL, h, v, h1, h2 => by
    have hn : n < B.length := by omega
    rw [List.drop_eq_getElem_cons hn, ← getM_eq_rk B n hn] at h
    obtain ⟨a1, a2⟩ := bAnd_rk h
    have hno := noOne_rk _ a1
    rw [mapB_rk] at hno
    rw [mapB_rk] at a2
    have hlow : ∀ u < 2 ^ n, qPackRk B u (n + 1) = qPackRk B u n := fun u hu =>
      qPackRk_high B hu 1
    have hup : ∀ u < 2 ^ n, qPackRk B (2 ^ n + u) (n + 1) = mulWK (qPackRk B u n) (getM B n) := by
      intro u hu
      have hb : (2 ^ n + u).testBit n = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hu]
        rfl
      rw [qPackRk, hb, if_pos rfl]
      congr 1
      exact qPackRk_congr B n fun s hs => Nat.testBit_two_pow_add_gt hs u
    by_cases hv : v < 2 ^ (n + 1)
    · obtain ⟨u, rfl⟩ : ∃ u, v = 2 ^ n + u := ⟨v - 2 ^ n, by omega⟩
      have hu : u < 2 ^ n := by rw [pow_succ] at hv; omega
      rw [Nat.add_comm k 1, ← Nat.add_assoc, qPackRk_high B hv k, hup u hu]
      refine hno _ (List.mem_map.2 ⟨qPackRk B u n, ?_, rfl⟩)
      rw [hL]
      exact List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩
    · have e := doubling_rk B k (n + 1) (List.append L (L.map fun a => mulWK a (getM B n)))
        (by omega) ?_ a2 v (by omega) (by rw [Nat.add_assoc, Nat.add_comm 1 k]; exact h2)
      · rwa [Nat.add_assoc, Nat.add_comm 1 k] at e
      · change L ++ _ = _
        rw [pow_succ, Nat.mul_two, List.range_add, List.map_append, List.map_map, hL,
          List.map_map]
        congr 1
        · exact List.map_congr_left fun u hu => (hlow u (List.mem_range.1 hu)).symm
        · exact List.map_congr_left fun u hu => (hup u (List.mem_range.1 hu)).symm

theorem indepOK_sound {D : Co1RankTab.Dat} (h : indepOK D.BS = true) (hlen : D.BS.length = D.d) :
    ∀ v < 2 ^ D.d, v ≠ 0 → matK (qOf D v) ≠ 1 := by
  intro v hv hv0 h1
  have hq : qOf D v = qPackRk D.BS v D.d := qOf_eq_qPackRk D v D.d
  have hne := doubling_rk D.BS D.d 0 [oneK] (by omega) rfl h v (by rw [pow_zero]; omega)
    (by rw [Nat.zero_add]; exact hv)
  rw [Nat.zero_add, ← hq] at hne
  rw [← matK_oneK] at h1
  have hlt : qOf D v < 2 ^ (24 * 24) := by
    rw [hq]
    exact qPackRk_lt _ _ _
  exact hne (matK_inj_rk hlt oneK_lt_rk h1)

theorem testBit_fld (x o w t : ℕ) :
    (Nat.land (Nat.shiftRight x o) (mask w)).testBit t = (decide (t < w) && x.testBit (o + t)) := by
  rw [land_mask, Nat.testBit_mod_two_pow]
  change (decide (t < w) && (x >>> o).testBit t) = _
  rw [Nat.testBit_shiftRight]

theorem phRow_eq {D : Co1RankTab.Dat} {i j : ℕ}
    (h : ∀ s < D.d, fld(D.PHt, Nat.mul D.d (Nat.add (Nat.mul D.d i) s), mask D.d) =
      fld(D.PHt, Nat.mul D.d (Nat.add (Nat.mul D.d j) s), mask D.d)) : phRow D i = phRow D j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [phRow, phRow, testBit_fld, testBit_fld]
  by_cases ht : t < D.d * D.d
  · have hd : 0 < D.d := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at ht; simp at ht)
    have hs : t / D.d < D.d := Nat.div_lt_of_lt_mul ht
    have hr : t % D.d < D.d := Nat.mod_lt _ hd
    have e := congrArg (fun x => Nat.testBit x (t % D.d)) (h (t / D.d) hs)
    simp only [testBit_fld, decide_eq_true hr, Bool.true_and] at e
    have ei : ∀ k, D.d * D.d * k + t = D.d * (D.d * k + t / D.d) + t % D.d := fun k => by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, Nat.div_add_mod]
    have hdec : decide (t < Nat.mul D.d D.d) = true := decide_eq_true ht
    rw [hdec, Bool.true_and, Bool.true_and]
    change D.PHt.testBit (D.d * D.d * i + t) = D.PHt.testBit (D.d * D.d * j + t)
    rw [ei i, ei j]
    exact e
  · have hdec : decide (t < Nat.mul D.d D.d) = false := decide_eq_false ht
    rw [hdec, Bool.false_and, Bool.false_and]

variable {G : Type*} [Group G]

theorem wordP_mem {gg : ℕ → G} {nG : ℕ} {S : Subgroup G} (hgg : ∀ g < nG, gg g ∈ S) :
    ∀ n w, wordOKn nG n w = true → wordP gg n w ∈ S
  | 0, _, _ => S.one_mem
  | n + 1, w, h => by
    rw [wordOKn] at h
    rw [wordP]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw]
      exact S.one_mem
    · rw [if_neg hw] at h ⊢
      obtain ⟨hl, h⟩ := Bool.and_eq_true_iff.1 h
      have := of_decide_eq_true hl
      exact S.mul_mem (hgg _ (by omega)) (wordP_mem hgg n _ h)

theorem w_inj {C : Co1RankCoord.Dat} {b w : ℕ → G} (hM : Model C b w)
    (hq : ∀ v < 2 ^ C.d, qProd b C.d v = 1 → v = 0)
    (hrows : ∀ i < 128, ∀ j < 128,
      (∀ s < C.d, fld(C.PHt, Nat.mul C.d (Nat.add (Nat.mul C.d i) s), mask C.d) =
        fld(C.PHt, Nat.mul C.d (Nat.add (Nat.mul C.d j) s), mask C.d)) → i = j)
    {i j : ℕ} (hi : i < 128) (hj : j < 128) {z : ℕ} (h : w i = qProd b C.d z * w j) : i = j := by
  refine hrows i hi j hj fun s hs => ?_
  have hcq : ∀ u v, qProd b C.d u * qProd b C.d v = qProd b C.d v * qProd b C.d u := fun u v => by
    rw [← qProd_xor' hM.comm hM.sq, ← qProd_xor' hM.comm hM.sq]
    exact congrArg _ (Nat.xor_comm u v)
  refine qProd_inj hM.comm hM.sq hq (land_mask_lt _ _) (land_mask_lt _ _) ?_
  rw [← hM.row i hi s hs, ← hM.row j hj s hs, h, mul_inv_rev, qProd_inv hM.comm hM.sq]
  calc qProd b C.d z * w j * b s * ((w j)⁻¹ * qProd b C.d z)
      = qProd b C.d z * (w j * b s * (w j)⁻¹) * qProd b C.d z := by group
    _ = (w j * b s * (w j)⁻¹) * (qProd b C.d z * qProd b C.d z) := by
      rw [hM.row j hj s hs, hcq z, mul_assoc]
    _ = w j * b s * (w j)⁻¹ := by rw [qProd_mul_self hM.comm hM.sq, mul_one]

theorem wU_eq (D : Co1RankTab.Dat) (gens : ℕ → GL24) (j : ℕ) :
    wU D gens j = wordP gens 8 (getL D.CW j) := rfl

attribute [local irreducible] bU wU qProd el

theorem closure_eq_of_checks {D : Co1RankTab.Dat} {gens : ℕ → GL24} (hM : chkM D = true)
    (hT : chkT D = true) (htab : tabOK D = true) (hlen : D.BS.length = D.d)
    (hG : ∀ g < D.nG, matK (getM D.G g) = (gens g : Matrix (Fin 24) (Fin 24) (ZMod 2))) :
    ∃ (hMod : Model (toC D) (bU D) (wU D gens)) (h0 : wU D gens 0 = 1),
      Subgroup.closure (gens '' {g | g < D.nG}) = elSub hMod h0 ∧
      Nat.card (Subgroup.closure (gens '' {g | g < D.nG})) = 2 ^ (D.d + 7) ∧
      ∀ x < 2 ^ (D.d + 7), ∀ y < 2 ^ (D.d + 7),
        el D.d (bU D) (wU D gens) x = el D.d (bU D) (wU D gens) y → x = y := by
  obtain ⟨hMod, h0, hrel⟩ := model_of_checks hM hT htab hG
  obtain ⟨-, hsqN, hind, -, -, -, -, -⟩ := chkM_sound hM
  obtain ⟨-, -, hdist⟩ := chkT_sound hT
  obtain ⟨hword, hspan⟩ := tabOK_sound htab
  have hsqM : ∀ s < D.d, matK (getM D.BS s) * matK (getM D.BS s) = 1 := fun s hs => by
    rw [← matK_mulWK, hsqN s hs, matK_oneK]
  have hq : ∀ v < 2 ^ D.d, qProd (bU D) D.d v = 1 → v = 0 := by
    intro v hv h1
    by_contra hv0
    refine indepOK_sound hind hlen v hv hv0 ?_
    have e := qProd_map (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))) (bU D) D.d v
    simp only [Units.coeHom_apply] at e
    rw [matK_qOf', ← qProd_congr_fun D.d (fun s hs => val_bU (hsqM s hs)) v, ← e, h1,
      Units.val_one]
  have hw : ∀ i < 128, ∀ j < 128, ∀ z, wU D gens i = qProd (bU D) D.d z * wU D gens j → i = j :=
    fun i hi j hj z h => w_inj hMod hq (fun i hi j hj hr => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hdist i hi j hj hlt (phRow_eq hr)
      · exact hdist j hj i hi hlt (phRow_eq fun s hs => (hr s hs).symm)) hi hj h
  have hinj := fun x (hx : x < 2 ^ (D.d + 7)) y (hy : y < 2 ^ (D.d + 7)) =>
    el_injective (C := toC D) hMod hq hw hx hy
  have hcl : Subgroup.closure (gens '' {g | g < D.nG}) = elSub hMod h0 := by
    have hgS : ∀ g < D.nG, gens g ∈ Subgroup.closure (gens '' {g | g < D.nG}) := fun g hg =>
      Subgroup.subset_closure ⟨g, hg, rfl⟩
    have hwS : ∀ j < 128, wU D gens j ∈ Subgroup.closure (gens '' {g | g < D.nG}) := fun j hj => by
      have := wordP_mem hgS 8 _ (hword j hj)
      rw [← wU_eq] at this
      exact this
    refine closure_eq_elSub hMod h0 (fun g hg => ?_) hwS (fun v hv => ?_)
    · obtain ⟨h1, h2⟩ := el_stepC (D := D) (b := bU D) (w := wU D gens) (gg := gens)
        hMod.comm hMod.sq hrel (x := 0) (Nat.two_pow_pos _) hg
      refine ⟨stepC D 0 g, h1, ?_⟩
      change wU D gens 0 * gens g = el D.d (bU D) (wU D gens) (stepC D 0 g)
      rw [h2, el_zero _ _ _ h0, one_mul, h0, one_mul]
    · change qProd (bU D) D.d v ∈ _
      obtain ⟨L, hL, rfl⟩ := hspan v hv
      clear hv
      induction L with
      | nil => rw [List.foldr_nil, qProd_zero]; exact Subgroup.one_mem _
      | cons p L ih =>
        have hB := ih fun p hp => hL p (List.mem_cons_of_mem _ hp)
        obtain ⟨hp1, hp2⟩ := hL p List.mem_cons_self
        have e := hrel p.1 hp1 p.2 hp2
        have e' : qProd (bU D) D.d (Nat.shiftRight (relK D p.1 p.2) 7) =
            wU D gens p.1 * gens p.2 * (wU D gens (Nat.land (relK D p.1 p.2) 127))⁻¹ := by
          rw [e]
          group
        have hA : qProd (bU D) D.d (Nat.shiftRight (relK D p.1 p.2) 7) ∈
            Subgroup.closure (gens '' {g | g < D.nG}) :=
          e' ▸ Subgroup.mul_mem _ (Subgroup.mul_mem _ (hwS _ hp1) (hgS _ hp2))
            (Subgroup.inv_mem _ (hwS _ (land127_lt _)))
        have hx := qProd_xor' hMod.comm hMod.sq (Nat.shiftRight (relK D p.1 p.2) 7)
          (List.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0 L)
        change qProd (bU D) (toC D).d (Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7)
          (List.foldr (fun p acc => Nat.xor (Nat.shiftRight (relK D p.1 p.2) 7) acc) 0 L)) ∈ _
        rw [hx]
        exact Subgroup.mul_mem _ hA hB
  refine ⟨hMod, h0, hcl, ?_, hinj⟩
  rw [hcl]
  exact card_elSub hMod h0 hq hw

theorem chkP_sound {D : Co1RankTab.Dat} (h : chkP D = true) :
    ∀ g < D.nG, ∀ u < D.nU, fld(getL D.P g, Nat.mul 12 u, 4095) < D.nU ∧
      mulC (toC D) (stepC D 0 g) (CFSG.KC.Co1RankRec.uC D u) =
        stepC D (CFSG.KC.Co1RankRec.uC D (fld(getL D.P g, Nat.mul 12 u, 4095))) g := by
  have hm : D.nU ≤ 64 * Nat.succ (Nat.shiftRight D.nU 6) := by
    change D.nU ≤ 64 * (D.nU >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  unfold chkP at h
  refine recAnd_rk (p := fun g => ∀ u < D.nU, fld(getL D.P g, Nat.mul 12 u, 4095) < D.nU ∧
      mulC (toC D) (stepC D 0 g) (CFSG.KC.Co1RankRec.uC D u) =
        stepC D (CFSG.KC.Co1RankRec.uC D (fld(getL D.P g, Nat.mul 12 u, 4095))) g) h
    (fun g b hb => ?_)
  beta_reduce at hb
  rw [strictB_eq', strictB_eq'] at hb
  obtain ⟨a1, a2⟩ := bAnd_rk hb
  refine ⟨fun u hu => ?_, a2⟩
  have e := allBelow_rk a1 hm u hu
  beta_reduce at e
  rw [strictB_eq'] at e
  obtain ⟨c1, c2⟩ := bAnd_rk e
  exact ⟨Nat.blt_eq.mp c1, Nat.eq_of_beq_eq_true c2⟩

theorem uC_lt (D : Co1RankTab.Dat) (u : ℕ) : CFSG.KC.Co1RankRec.uC D u < 2 ^ (D.d + 7) :=
  land_mask_lt _ _

theorem P_conj_of_checks {D : Co1RankTab.Dat} {gens : ℕ → GL24}
    (hMod : Model (toC D) (bU D) (wU D gens)) (h0 : wU D gens 0 = 1)
    (hrel : ∀ j < 128, ∀ g < D.nG, wU D gens j * gens g =
      qProd (bU D) D.d (Nat.shiftRight (relK D j g) 7) * wU D gens (Nat.land (relK D j g) 127))
    (hP : chkP D = true) :
    ∀ g < D.nG, ∀ u < D.nU, fld(getL D.P g, Nat.mul 12 u, 4095) < D.nU ∧
      el D.d (bU D) (wU D gens) (CFSG.KC.Co1RankRec.uC D (fld(getL D.P g, Nat.mul 12 u, 4095))) =
        gens g * el D.d (bU D) (wU D gens) (CFSG.KC.Co1RankRec.uC D u) * (gens g)⁻¹ := by
  intro g hg u hu
  obtain ⟨h1, h2⟩ := chkP_sound hP g hg u hu
  refine ⟨h1, ?_⟩
  have hs0 := el_stepC (D := D) (b := bU D) (w := wU D gens) (gg := gens) hMod.comm hMod.sq hrel
    (x := 0) (Nat.two_pow_pos _) hg
  have hs1 := el_stepC (D := D) (b := bU D) (w := wU D gens) (gg := gens) hMod.comm hMod.sq hrel
    (x := CFSG.KC.Co1RankRec.uC D (fld(getL D.P g, Nat.mul 12 u, 4095))) (uC_lt D _) hg
  have hm := el_mulC hMod hs0.1 (uC_lt D u)
  have e0 : el D.d (bU D) (wU D gens) 0 = 1 := el_zero _ _ _ h0
  have e : gens g * el D.d (bU D) (wU D gens) (CFSG.KC.Co1RankRec.uC D u) =
      el D.d (bU D) (wU D gens) (CFSG.KC.Co1RankRec.uC D (fld(getL D.P g, Nat.mul 12 u, 4095))) *
        gens g := by
    have e1 : el D.d (bU D) (wU D gens) (mulC (toC D) (stepC D 0 g) (CFSG.KC.Co1RankRec.uC D u)) =
        el D.d (bU D) (wU D gens) (stepC D 0 g) * el D.d (bU D) (wU D gens)
          (CFSG.KC.Co1RankRec.uC D u) := hm
    rw [h2, hs1.2, hs0.2, e0, one_mul] at e1
    exact e1.symm
  rw [e]
  group

end CFSG.KS.SporSch.Co1Rank

end
