module

public import CFSG.Certificates.Kernel.MonsterB.Rep4371RowEq
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XTab

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Trace6091 CFSG.KC.Rep4371Row CFSG.Monster.B

@[expose] def kd (κ : Nat) : Model.Key := (κ % 4, κ / 4 % 4096, κ / 16384)

@[expose] def td (t : Nat × Int) : Model.Key × Int := (kd t.1, t.2)

theorem kc_eq (t x y : Nat) : kc t x y = t + 4 * x + 16384 * y := by
  unfold kc
  change t + (4 * x + 16384 * y) = _
  omega

theorem kd_kc {t x y : Nat} (ht : t < 4) (hx : x < 4096) : kd (kc t x y) = (t, x, y) := by
  rw [kc_eq]
  have h1 : (t + 4 * x + 16384 * y) % 4 = t := by omega
  have h2 : (t + 4 * x + 16384 * y) / 4 % 4096 = x := by omega
  have h3 : (t + 4 * x + 16384 * y) / 16384 = y := by omega
  unfold kd
  rw [h1, h2, h3]

theorem kc_kd (κ : Nat) : kc (κ % 4) (κ / 4 % 4096) (κ / 16384) = κ := by
  rw [kc_eq]
  omega

theorem kd_inj {κ κ' : Nat} (h : kd κ = kd κ') : κ = κ' := by
  rw [← kc_kd κ, ← kc_kd κ']
  unfold kd at h
  simp only [Prod.mk.injEq] at h
  rw [h.1, h.2.1, h.2.2]

theorem kt_eq (κ : Nat) : kt κ = κ % 4 := Nat.and_two_pow_sub_one_eq_mod κ 2

theorem kx_eq (κ : Nat) : kx κ = κ / 4 % 4096 := by
  change (κ >>> 2) &&& (2 ^ 12 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ky_eq (κ : Nat) : ky κ = κ / 16384 := by
  change κ >>> 14 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem sk_eq (s κ : Nat) : sk s κ = s + 2 * κ := rfl

theorem strictL_eq (y : Nat) (k : Nat → Terms) : strictL y k = k y := by
  cases y <;> rfl

theorem strictP_eq (y : Nat) (k : Nat → Nat × Int) : strictP y k = k y := by
  cases y <;> rfl

theorem sgI_toNat (b : Bool) (m : Int) : sgI b.toNat m = Model.sgnI b * m := by
  cases b
  · exact (Int.one_mul m).symm
  · exact (Int.neg_one_mul m).symm

theorem sgI_not (b : Bool) (m : Int) : sgI (Nat.xor b.toNat 1) m = -(m * Model.sgnI b) := by
  cases b
  · change -m = -(m * 1)
    rw [Int.mul_one]
  · change m = -(m * -1)
    rw [Int.mul_neg_one, Int.neg_neg]

theorem one_sk (b : Bool) (κ : Nat) : one (sk b.toNat κ) = [(κ, Model.sgnI b * 64)] := by
  unfold one
  rw [strictL_eq]
  have hb := toNat_lt b
  have h1 : Nat.shiftRight (sk b.toNat κ) 1 = κ := by
    change (b.toNat + 2 * κ) >>> 1 = κ
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  have h2 : Nat.land (sk b.toNat κ) 1 = b.toNat := by
    change (b.toNat + 2 * κ) &&& 1 = b.toNat
    rw [Nat.and_one_is_mod]
    omega
  rw [h1, h2, sgI_toNat]

theorem one_map (b : Bool) {t x y : Nat} (ht : t < 4) (hx : x < 4096) :
    (one (sk b.toNat (kc t x y))).map td = [Model.signedTerm (t, x, y) b] := by
  rw [one_sk]
  simp only [List.map_cons, List.map_nil, td, kd_kc ht hx]
  rfl

theorem keyW_eq (η : Bool) (c : Nat) : Model.Key.W η c = (2, η.toNat, c) := by
  cases η <;> rfl

theorem wk_enc (r : Bool × Bool × Nat) (e : Bool) :
    wk (encB r) e.toNat = sk (r.1 ^^ e).toNat (kc 2 r.2.1.toNat r.2.2) := by
  unfold wk
  rw [strictN_eq]
  simp only [encB]
  rw [land1_enc _ _ _ (toNat_lt _), bit1_enc _ _ _ (toNat_lt _) (toNat_lt _),
    shr2_enc _ _ _ (toNat_lt _) (toNat_lt _), Nat.xor_eq, ← toNat_xor]

theorem one_W (r : Bool × Bool × Nat) (e : Bool) :
    (one (wk (encB r) e.toNat)).map td = [Model.signedTerm (Model.Key.W r.2.1 r.2.2) (r.1 ^^ e)] := by
  rw [wk_enc, keyW_eq]
  exact one_map _ (by decide) (Nat.lt_of_lt_of_le (toNat_lt _) (by decide))

theorem one_W0 (r : Bool × Bool × Nat) :
    (one (wk (encB r) 0)).map td = [Model.signedTerm (Model.Key.W r.2.1 r.2.2) r.1] := by
  have h := one_W r false
  rw [Bool.xor_false] at h
  exact h

theorem nz_eq (e : Nat) : nz e = (e != 0).toNat := by
  cases e <;> rfl

theorem thH_eq {TH : Nat} (h : thOK TH = true) (a : Nat) : thH TH a = thetaT a := by
  unfold thH
  by_cases ha : a < 4096
  · have hb : Nat.blt a (nat_lit 4096) = true := by
      rw [Nat.blt_eq]
      exact ha
    rw [hb]
    change f12 TH a = thetaT a
    rw [KeysOKAux.f12_th h ha, KeysOKAux.thetaN_eq, thetaT_eq]
  · have hb : Nat.blt a (nat_lit 4096) = false := by
      rw [Bool.eq_false_iff]
      intro h'
      rw [Nat.blt_eq] at h'
      exact ha h'
    rw [hb]

theorem eYH_eq {TH : Nat} (h : thOK TH = true) (a : Nat) (η : Bool) (c : Nat) :
    eYH TH a η.toNat c = encB (Model.eYN a η c) := by
  rw [← eYT_eq]
  unfold eYH eYT
  simp only [thH_eq h]

theorem coeffN_lt (w : Nat) : Model.coeffN w < 4096 := KeysOKAux.packN_lt' _ 12

theorem pairN_zero (x : Nat) : Model.pairN x 0 = false := by
  unfold Model.pairN
  rw [Nat.and_zero]
  rfl

theorem toNat_xor_one (b : Bool) : b.toNat ^^^ 1 = (!b).toNat := by
  cases b <;> rfl

theorem toNat_xor_eq (a b : Bool) : Nat.xor a.toNat b.toNat = (a ^^ b).toNat := (toNat_xor a b).symm

theorem toNat_and_eq (a b : Bool) : Nat.land a.toNat b.toNat = (a && b).toNat := (toNat_and a b).symm

theorem toNat_xor1_eq (b : Bool) : Nat.xor b.toNat 1 = (!b).toNat := toNat_xor_one b

theorem pT_model (c : Nat) : pT c = (Model.pN c).toNat := by
  rw [KeysOKAux.pT_eq, Rep4371.native_pN]

theorem xPauliT_eq (s : Bool) (qa qd a d : Nat) :
    xPauliT qa qd a d = sk (Model.conjPauliN (s, qa, qd) (false, a, d)).1.toNat (kc 1 a d) := by
  unfold xPauliT
  rw [pairT_eq, pairT_eq, toNat_xor_eq]
  simp only [Model.conjPauliN, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Bool.false_xor]

theorem actPauli_eq (q : Model.Pauli) (κ : Nat) :
    Model.keyActPauli q (kd κ) = (actPauliT q.s.toNat q.a q.d κ).map td := by
  obtain ⟨s, qa, qd⟩ := q
  unfold actPauliT
  rw [kt_eq, kx_eq, ky_eq]
  unfold kd
  have hx : κ / 4 % 4096 < 4096 := Nat.mod_lt _ (by decide)
  have ht : κ % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize κ / 4 % 4096 = x at hx ⊢
  generalize κ / 16384 = y
  generalize κ % 4 = t at ht ⊢
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · change _ = (one (sk false.toNat (kc 0 x 0))).map td
    rw [one_map false (by decide) hx]
    rfl
  · change _ = (one (xPauliT qa qd x y)).map td
    rw [xPauliT_eq s, one_map _ (by decide) hx]
    rfl
  · change _ = (one (wk (ePauliT s.toNat qa qd (nz x) y) 0)).map td
    rw [nz_eq, ePauliT_eq, one_W0]
    rfl
  · change _ = (one (wk (ePauliT s.toNat qa qd (nz x) y) 0)).map td
    rw [nz_eq, ePauliT_eq, one_W0]
    rfl

theorem pe_all {P : Nat} {p : Array Nat} (h24 : ∀ i < 24, pe P i = p[i]!) (hs : p.size = 24)
    (hP : P < 2 ^ 120) : ∀ i, pe P i = p[i]! := by
  intro i
  by_cases hi : i < 24
  · exact h24 i hi
  · have hn : ¬ i < p.size := by
      rw [hs]
      exact hi
    have h1 : p[i]! = 0 := by
      rw [getElem!_neg p i hn]
      rfl
    rw [h1]
    have hle : (2 : Nat) ^ 120 ≤ 2 ^ (5 * i) := Nat.pow_le_pow_right (by decide) (by omega)
    change (P >>> (5 * i)) &&& 31 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP hle), Nat.zero_and]

section Perm

variable {TH : Nat} (hTH : thOK TH = true) {P : Nat} {p : Array Nat} (hP : ∀ i, pe P i = p[i]!)
  {BT K : Nat} (hBT : betaTabT P = BT) (hK : (Model.kappaN p 63).toNat = K)

include hTH hP hBT in
theorem xPermT_eq (a d : Nat) :
    xPermT TH P BT a d = sk (Model.conjPermN p (false, a, d)).1.toNat
      (kc 1 (Model.conjPermN p (false, a, d)).2.1 (Model.conjPermN p (false, a, d)).2.2) := by
  have hP' : ∀ i < 24, pe P i = p[i]! := fun i _ => hP i
  unfold xPermT
  simp only [strictN_eq, thH_eq hTH]
  rw [permCT_eq hP', ← hBT, kappaT_eq hP', thetaT_eq, thetaT_eq, permDT_eq hP']
  simp only [Model.conjPermN, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Bool.false_xor, Nat.xor_eq]

theorem conjPermN_lt (p : Array Nat) (a d : Nat) : (Model.conjPermN p (false, a, d)).2.1 < 4096 :=
  coeffN_lt _

include hTH hP hBT hK in
theorem actPerm_eq (κ : Nat) : Model.keyActPerm p (kd κ) = (actPermT TH P BT K κ).map td := by
  have hP' : ∀ i < 24, pe P i = p[i]! := fun i _ => hP i
  unfold actPermT
  rw [kt_eq, kx_eq, ky_eq]
  unfold kd
  have hx : κ / 4 % 4096 < 4096 := Nat.mod_lt _ (by decide)
  have ht : κ % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize κ / 4 % 4096 = x at hx ⊢
  generalize κ / 16384 = y
  generalize κ % 4 = t at ht ⊢
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · change _ = (one (sk (nz (pe P 0)) (kc 0 (pe P x) 0))).map td
    have hb : pe P x < 4096 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    rw [nz_eq, one_map _ (by decide) hb, hP, hP]
    rfl
  · change _ = (one (xPermT TH P BT x y)).map td
    rw [xPermT_eq hTH hP hBT, one_map _ (by decide) (conjPermN_lt p x y)]
    rfl
  · change _ = (one (wk (ePermT P BT K (nz x) y) (nz (pe P 0)))).map td
    rw [nz_eq, nz_eq, ePermT_eq hP' hBT hK, hP, one_W]
    rfl
  · change _ = (one (wk (ePermT P BT K (nz x) y) (nz (pe P 0)))).map td
    rw [nz_eq, nz_eq, ePermT_eq hP' hBT hK, hP, one_W]
    rfl

end Perm

theorem conjYN_lt {A b : Nat} (hA : A < 4096) (hb : b < 4096) (s : Bool) (d : Nat) :
    (Model.conjYN A (s, b, d)).2.1 < 4096 := by
  have h12 : (4096 : Nat) = 2 ^ 12 := rfl
  have h63 : ∀ (P : Prop) [Decidable P], (if P then 63 else 0 : Nat) < 2 ^ 12 := by
    intro P _
    split <;> decide
  simp only [Model.conjYN, Model.Pauli.mul, Model.conjTN, Model.conjDN, Model.Pauli.a, Model.Pauli.d,
    Model.Pauli.s]
  rw [h12] at hA hb ⊢
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.lt_of_le_of_lt (Nat.le_refl 0) (by decide))
    (Nat.xor_lt_two_pow hb (h63 _))) (Nat.xor_lt_two_pow ?_ (h63 _))
  split
  · exact hA
  · decide

theorem yT_eq {TH : Nat} (hTH : thOK TH = true) {A WA TA PA : Nat} (hW : wordT A = WA)
    (hT : thetaT A = TA) (hPA : pT A = PA) (s : Bool) (b d : Nat) :
    yT TH A WA TA PA s.toNat b d = sk (Model.conjYN A (s, b, d)).1.toNat
      (kc 1 (Model.conjYN A (s, b, d)).2.1 (Model.conjYN A (s, b, d)).2.2) := by
  subst hW hT hPA
  unfold yT
  simp only [strictN_eq, thH_eq hTH]
  simp only [pairT_eq, thetaT_eq, wordT_eq, dualT_eq, pT_model, selB_toNat, toNat_xor_eq,
    toNat_and_eq, toNat_xor1_eq]
  simp only [Model.conjYN, Model.Pauli.mul, Model.conjTN, Model.conjDN, Model.Pauli.a, Model.Pauli.d,
    Model.Pauli.s, Model.thetaBit, Model.acodeN, pairN_zero, Bool.xor_false, Nat.zero_xor,
    Nat.xor_eq, Nat.land_eq]
  rfl

theorem actSign_eq {TH : Nat} (hTH : thOK TH = true) {A WA TA PA : Nat} (hA : A < 4096)
    (hW : wordT A = WA) (hT : thetaT A = TA) (hPA : pT A = PA) (κ : Nat) :
    Model.keyActSign A (kd κ) = (actSignT TH A WA TA PA κ).map td := by
  unfold actSignT
  rw [kt_eq, kx_eq, ky_eq]
  unfold kd
  have hx : κ / 4 % 4096 < 4096 := Nat.mod_lt _ (by decide)
  have ht : κ % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize κ / 4 % 4096 = x at hx ⊢
  generalize κ / 16384 = y
  generalize κ % 4 = t at ht ⊢
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · change _ = (one (sk (Nat.xor (bitN WA 0) (bitN WA x)) (kc 0 x 0))).map td
    rw [← hW, bitN_eq, bitN_eq, toNat_xor_eq, one_map _ (by decide) hx, wordT_eq]
    rfl
  · change _ = (one (yT TH A WA TA PA false.toNat x y)).map td
    rw [yT_eq hTH hW hT hPA, one_map _ (by decide) (conjYN_lt hA hx false y)]
    rfl
  · change _ = (one (wk (eYH TH A (nz x) y) (bitN WA 0))).map td
    rw [nz_eq, eYH_eq hTH, ← hW, bitN_eq, wordT_eq, one_W]
    rfl
  · change _ = (one (wk (eYH TH A (nz x) y) (bitN WA 0))).map td
    rw [nz_eq, eYH_eq hTH, ← hW, bitN_eq, wordT_eq, one_W]
    rfl

theorem land63 (x : Nat) : Nat.land x 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem mod64_lt (x : Nat) : x % 64 < 64 := Nat.mod_lt _ (by decide)

theorem lt64_xor {a b : Nat} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem ite63_lt (P : Prop) [Decidable P] : (if P then 63 else 0 : Nat) < 64 := by
  split <;> decide

theorem gamT_eq {x : Nat} (hx : x < 64) : gamT x = Model.gammaLowN x := by
  unfold gamT
  rw [par6_tab x hx, selB_toNat, land63]
  rfl

theorem bgT_eq {μ ν : Nat} (hμ : μ < 64) (hν : ν < 64) : bgT μ ν = (Model.bGN μ ν).toNat := by
  unfold bgT
  have hμν : Nat.land μ ν < 64 := Nat.lt_of_le_of_lt Nat.and_le_left hμ
  rw [par6_tab μ hμ, par6_tab ν hν, par6_tab _ hμν, toNat_and_eq, toNat_xor_eq]
  rfl

theorem xiX_lt (a d : Nat) : (Model.conjXiN (false, a, d)).2.1 < 4096 := by
  simp only [Model.conjXiN, Model.Pauli.a, Model.Pauli.d]
  have h1 : (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0)) < 2 ^ 12 :=
    Nat.lt_of_lt_of_le (lt64_xor (mod64_lt d) (ite63_lt _)) (by decide)
  have h2 : a &&& 4032 < 2 ^ 12 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact Nat.xor_lt_two_pow h1 h2

theorem W1_eq : wordT 1 = W1 := by decide +kernel

theorem T1_eq : thetaT 1 = 0 := by decide +kernel

theorem P1_eq : pT 1 = 0 := by decide +kernel

theorem and63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem conjXiN_eq (a d : Nat) : Model.conjXiN (false, a, d) =
    (Model.qGN (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0)) ^^
      Model.bGN (a % 64) (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0)),
     (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0)) ^^^ (a &&& 4032),
     Model.gammaLowN (a % 64 ^^^ (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0))) ^^^
      (d &&& 4032)) := by
  unfold Model.conjXiN
  simp only [Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Bool.false_xor]

theorem xXiT_eq {TH : Nat} (hTH : thOK TH = true) (a d : Nat) :
    xXiT TH a d = sk (Model.conjYN 1 (Model.conjXiN (false, a, d))).1.toNat
      (kc 1 (Model.conjYN 1 (Model.conjXiN (false, a, d))).2.1
        (Model.conjYN 1 (Model.conjXiN (false, a, d))).2.2) := by
  have hμ := mod64_lt a
  have hl := mod64_lt d
  have hν : (d % 64 ^^^ (if Model.parN 6 (d % 64) = true then 63 else 0)) < 64 :=
    lt64_xor hl (ite63_lt _)
  rw [conjXiN_eq]
  unfold xXiT
  simp only [strictN_eq, Nat.xor_eq, Nat.land_eq]
  rw [and63, and63, par6_tab _ hl, selB_toNat, qgT_tab _ hν, bgT_eq hμ hν, ← toNat_xor,
    gamT_eq (lt64_xor hμ hν)]
  exact yT_eq hTH W1_eq T1_eq P1_eq _ _ _

theorem c4_tab : ∀ r < 4, ∀ r' < 4, ∀ b : Bool,
    sgI (Nat.xor (Nat.xor (c4s r r') b.toNat) 1) 32 = -(Model.c4N r r' * Model.sgnI b) := by
  decide +kernel

theorem xiA1_eq {x : Nat} (hx : x < 4096) {r' : Nat} (hr' : r' < 4) :
    td (xiA1 (4 * (x / 4)) (x % 4) r') = (Model.Key.A (4 * (x / 4) + r'),
      -(Model.c4N (x % 4) r' * Model.sgnI ((Model.bmaskN 0).testBit (4 * (x / 4) + r')))) := by
  unfold xiA1 td
  have hb : 4 * (x / 4) + r' < 4096 := by omega
  rw [bitN_eq]
  change (kd (kc 0 (4 * (x / 4) + r') 0), sgI (Nat.xor (Nat.xor (c4s (x % 4) r')
    ((Model.bmaskN 0).testBit (4 * (x / 4) + r')).toNat) 1) 32) = _
  rw [kd_kc (by decide) hb, c4_tab _ (Nat.mod_lt _ (by decide)) _ hr']
  rfl

theorem xiA_eq {x : Nat} (hx : x < 4096) (y : Nat) :
    Model.keyActXi (0, x, y) = (xiAT x).map td := by
  unfold xiAT
  simp only [strictL_eq]
  have h1 : Nat.mul 4 (Nat.shiftRight x 2) = 4 * (x / 4) := by
    rw [Nat.mul_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land x 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2
  change _ = (List.map td [xiA1 (Nat.mul 4 (Nat.shiftRight x 2)) (Nat.land x 3) 0,
    xiA1 (Nat.mul 4 (Nat.shiftRight x 2)) (Nat.land x 3) 1, xiA1 (Nat.mul 4 (Nat.shiftRight x 2)) (Nat.land x 3) 2,
    xiA1 (Nat.mul 4 (Nat.shiftRight x 2)) (Nat.land x 3) 3])
  rw [h1, h2]
  simp only [List.map_cons, List.map_nil]
  rw [xiA1_eq hx (by decide), xiA1_eq hx (by decide), xiA1_eq hx (by decide), xiA1_eq hx (by decide)]
  rfl

theorem buildL_aux (n : Nat) (g : Nat → Nat × Int) : ∀ m ≤ n,
    Nat.rec (motive := fun _ => Terms) List.nil
      (fun i acc => List.cons (g (Nat.sub (Nat.sub n (nat_lit 1)) i)) acc) m =
      (List.range' (n - m) m).map g
  | 0, _ => rfl
  | m + 1, h => by
    change List.cons (g (n - 1 - m)) (Nat.rec (motive := fun _ => Terms) List.nil
      (fun i acc => List.cons (g (Nat.sub (Nat.sub n (nat_lit 1)) i)) acc) m) = _
    rw [buildL_aux n g m (by omega), List.range'_succ, List.map_cons]
    have e1 : n - 1 - m = n - (m + 1) := by omega
    have e2 : n - (m + 1) + 1 = n - m := by omega
    rw [e1, e2]

theorem buildL_eq (n : Nat) (g : Nat → Nat × Int) : buildL n g = (List.range n).map g := by
  unfold buildL
  rw [buildL_aux n g n (Nat.le_refl n), Nat.sub_self, ← List.range_eq_range']

theorem pi0_mod_and (c : Nat) {g : Nat} (hg : g < 64) :
    Model.pi0N c % 64 &&& g = Model.pi0N c &&& g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and]
  by_cases hi : i < 6
  · have h64 : (64 : Nat) = 2 ^ 6 := rfl
    rw [h64, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  · have h6 : (2 : Nat) ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hgi : g.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg h6)
    rw [hgi, Bool.and_false, Bool.and_false]

theorem gammaLowN_lt (μ : Nat) : Model.gammaLowN μ < 64 := by
  unfold Model.gammaLowN
  exact lt64_xor (mod64_lt μ) (ite63_lt _)

theorem xiGamma_mod (c : Nat) (f : Bool) :
    Model.xiGammaN c f = Model.xiGammaN (Model.pi0N c % 64) f := by
  have hp : Model.pi0N (Model.pi0N c % 64) = Model.pi0N c % 64 := by
    apply pi0_of
    have h64 : (64 : Nat) = 2 ^ 6 := rfl
    rw [h64, Nat.testBit_mod_two_pow, pi0_testBit]
    rfl
  unfold Model.xiGammaN
  rw [hp]
  congr 1
  funext μ
  unfold Model.pairN
  rw [pi0_mod_and c (gammaLowN_lt μ)]

theorem gT_xi (c : Nat) (f : Bool) : gT (Nat.land (Model.pi0N c) 63) f.toNat = Model.xiGammaN c f := by
  rw [land63, xiGamma_mod c f]
  cases f
  · exact (gT_tab _ (mod64_lt _)).1
  · exact (gT_tab _ (mod64_lt _)).2

theorem enc_shr6 (f : Bool) {ν : Nat} (hν : ν < 64) :
    Nat.shiftRight (64 * f.toNat + ν) 6 = f.toNat := by
  rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  have := toNat_lt f
  change (64 * f.toNat + ν) / 64 = f.toNat
  omega

theorem enc_and63 (f : Bool) {ν : Nat} (hν : ν < 64) : Nat.land (64 * f.toNat + ν) 63 = ν := by
  rw [land63]
  omega

theorem xiTerm_eq {TH : Nat} (hTH : thOK TH = true) (e : Bool) (c : Nat) (f : Bool) {ν : Nat}
    (hν : ν < 64) :
    td (xiTerm TH e.toNat (pi0T c) (64 * f.toNat + ν)) =
      (Model.Key.W (Model.eYN 1 (Model.xiGTerm (e ^^ f) c ν).2.1 (Model.xiGTerm (e ^^ f) c ν).2.2).2.1
        (Model.eYN 1 (Model.xiGTerm (e ^^ f) c ν).2.1 (Model.xiGTerm (e ^^ f) c ν).2.2).2.2,
        -(Model.xiGammaN c f * Model.sgnI ((Model.xiGTerm (e ^^ f) c ν).1 ^^
          (Model.eYN 1 (Model.xiGTerm (e ^^ f) c ν).2.1 (Model.xiGTerm (e ^^ f) c ν).2.2).1))) := by
  unfold xiTerm
  simp only [strictP_eq]
  rw [enc_shr6 f hν, enc_and63 f hν, toNat_xor_eq, pi0T_eq, shiftT_eq, eYH_eq hTH, gT_xi]
  generalize hu : Model.eYN 1 (e ^^ f) (Model.shiftN ν (Model.pi0N c)) = u
  have hxi : Model.xiGTerm (e ^^ f) c ν = (Model.qGN ν ^^ ((e ^^ f) && Model.mu0N ν), e ^^ f,
      Model.shiftN ν (Model.pi0N c)) := rfl
  rw [hxi]
  simp only [hu]
  unfold td
  simp only [encB]
  rw [bit1_enc _ _ _ (toNat_lt _) (toNat_lt _), shr2_enc _ _ _ (toNat_lt _) (toNat_lt _),
    kd_kc (by decide) (Nat.lt_of_lt_of_le (toNat_lt _) (by decide)), ← keyW_eq,
    land1_enc _ _ _ (toNat_lt _), qgT_tab ν hν, bitN_eq, toNat_and_eq, toNat_xor_eq, toNat_xor_eq,
    sgI_not]
  rfl

theorem xiW_eq {TH : Nat} (hTH : thOK TH = true) (e c : Nat) {t : Nat} (ht : 2 ≤ t) :
    Model.keyActXi (t, e, c) = (xiWT TH (nz e) c).map td := by
  have hm : Model.keyActXi (t, e, c) = [false, true].flatMap fun f => (List.range 64).map fun ν =>
      (Model.Key.W (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1
          (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).2.1
        (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).2.2,
        -(Model.xiGammaN c f * Model.sgnI ((Model.xiGTerm ((e != 0) ^^ f) c ν).1 ^^
          (Model.eYN 1 (Model.xiGTerm ((e != 0) ^^ f) c ν).2.1
            (Model.xiGTerm ((e != 0) ^^ f) c ν).2.2).1))) := by
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    rfl
  rw [hm]
  unfold xiWT
  rw [strictL_eq, buildL_eq, nz_eq]
  have h128 : (nat_lit 128 : Nat) = 64 + 64 := rfl
  rw [h128, List.range_add, List.map_append, List.map_map]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro ν hν
    have hν' : ν < 64 := List.mem_range.mp hν
    have := xiTerm_eq hTH (e != 0) c false hν'
    rw [Bool.toNat_false, Nat.mul_zero, Nat.zero_add] at this
    exact this.symm
  · apply List.map_congr_left
    intro ν hν
    have hν' : ν < 64 := List.mem_range.mp hν
    have := xiTerm_eq hTH (e != 0) c true hν'
    rw [Bool.toNat_true, Nat.mul_one] at this
    exact this.symm

theorem actXi_eq {TH : Nat} (hTH : thOK TH = true) (κ : Nat) :
    Model.keyActXi (kd κ) = (actXiT TH κ).map td := by
  unfold actXiT
  rw [kt_eq, kx_eq, ky_eq]
  unfold kd
  have hx : κ / 4 % 4096 < 4096 := Nat.mod_lt _ (by decide)
  have ht : κ % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize κ / 4 % 4096 = x at hx ⊢
  generalize κ / 16384 = y
  generalize κ % 4 = t at ht ⊢
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · change _ = (xiAT x).map td
    exact xiA_eq hx y
  · change _ = (one (xXiT TH x y)).map td
    rw [xXiT_eq hTH, one_map _ (by decide) (conjYN_lt (by decide) (xiX_lt x y) _ _)]
    rfl
  · change _ = (xiWT TH (nz x) y).map td
    exact xiW_eq hTH x y (by decide)
  · change _ = (xiWT TH (nz x) y).map td
    exact xiW_eq hTH x y (by decide)

end CFSG.KC.Rep4371X

end
