module

public import Certificates.Data.Kernel.Co1BSpin
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.Co1BInvSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpinCheck

public section

namespace CFSG.KC.Co1BSpin

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.F2W
  CFSG.Sporadic.SmallF2.Native CFSG.EvenSporadicStandard.Induction.AutBound.Spin

theorem leqK_sound : ∀ {L L' : List Nat}, leqK L L' = true → L = L'
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | a :: L, b :: L', h => by
    change andB (Nat.beq a b) (leqK L L') = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    rw [Nat.eq_of_beq_eq_true h1, leqK_sound h2]

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem packL_cons (v : Nat) (L : List Nat) : packL (v :: L) = v + packL L * 2 ^ 24 := by
  change v + packL L <<< 24 = _
  rw [Nat.shiftLeft_eq]

theorem packL_field : ∀ (L : List Nat), (∀ v ∈ L, v < 2 ^ 24) → ∀ i,
    packL L / 2 ^ (24 * i) % 2 ^ 24 = L.getD i 0
  | [], _, i => by
    change 0 / 2 ^ (24 * i) % 2 ^ 24 = 0
    simp
  | v :: L, h, 0 => by
    rw [packL_cons, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (h v (by simp))]
    rfl
  | v :: L, h, i + 1 => by
    have hv : v < 2 ^ 24 := h v (by simp)
    have e : (v + packL L * 2 ^ 24) / 2 ^ 24 = packL L := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 24), Nat.div_eq_of_lt hv, Nat.zero_add]
    rw [packL_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (24 * i)), ← Nat.div_div_eq_div_mul,
      e, packL_field L (fun w hw => h w (by simp [hw])) i]
    rfl

theorem toArray_packL {L : List Nat} (hl : L.length = 24) (hb : ∀ v ∈ L, v < 2 ^ 24) :
    L.toArray = unpackR 24 (packL L) := by
  apply Array.ext
  · simp [unpackR, hl]
  · intro i h1 _
    simp only [unpackR, Array.getElem_ofFn, List.getElem_toArray]
    rw [packL_field L hb i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
    rfl

theorem addRows_unpack (A B : Nat) :
    addRows 24 (unpackR 24 A) (unpackR 24 B) = unpackR 24 (A ^^^ B) := by
  unfold addRows unpackR
  congr 1
  funext i
  simp only [Array.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_xor, testBit_field, testBit_field, testBit_field, Nat.testBit_xor]
  cases decide (b < 24) <;> rfl

theorem zeroRows_eq : zeroRows 24 = unpackR 24 0 := by
  unfold zeroRows unpackR
  apply Array.ext
  · simp
  · intro i h1 _
    simp

theorem idRows_eq' : idRows 24 = unpackR 24 oneK := one_eq

theorem getD_map_unpack (x : Nat) (L : List Nat) (j : Nat) :
    (L.map (unpackR 24)).getD j (unpackR 24 x) = unpackR 24 (getL x L j) := by
  rw [getL_eq, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? <;> rfl

theorem getD_map_unpack_lt {L : List Nat} {j : Nat} (hj : j < L.length) (x : Array Nat) :
    (L.map (unpackR 24)).getD j x = unpackR 24 (getL 0 L j) := by
  rw [getL_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem getD_eq_getL (L : List Nat) (i : Nat) : L.getD i 0 = getL 0 L i := by
  rw [getL_eq, List.getD_eq_getElem?_getD]

theorem rowK_eq (N r : Nat) : (unpackR 24 N)[r]?.getD 0 = rowK N r := by
  change _ = Bool.rec (motive := fun _ => Nat) 0 (rowF 24 N r) (Nat.blt r 24)
  by_cases hr : r < 24
  · have : Nat.blt r 24 = true := Eq.mpr Nat.blt_eq hr
    rw [this]
    simp [unpackR, hr, rowF_eq]
  · have : Nat.blt r 24 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hr (Eq.mp Nat.blt_eq h)
    rw [this]
    simp [unpackR, hr]

theorem rowK_lt (N r : Nat) : rowK N r < 2 ^ 24 := by
  rw [← rowK_eq]
  by_cases hr : r < 24
  · simp [unpackR, hr, Nat.mod_lt]
  · simp [unpackR, hr]

theorem cact_unpack (X v : Nat) : cact 24 (unpackR 24 X) v = vmF 24 (trK 24 X) v := by
  rw [cact, transposeRows_unpackR, vecMulN_unpackR]

theorem bit_eq' (X i : Nat) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by simp only [Nat.beq_eq, decide_eq_true_eq])

theorem fold_sumAK (AK : List Nat) (c : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc k => if c.testBit k = true then
      addRows 24 acc ((AK.map (unpackR 24)).getD k (unpackR 24 0)) else acc) (unpackR 24 acc) =
      unpackR 24 (sumAK AK c l acc)
  | [], _ => rfl
  | k :: l, acc => by
    have e : (if c.testBit k = true then
        addRows 24 (unpackR 24 acc) ((AK.map (unpackR 24)).getD k (unpackR 24 0)) else unpackR 24 acc) =
        unpackR 24 (nIf(c.testBit k, Nat.xor acc (getL 0 AK k), acc)) := by
      rw [getD_map_unpack, addRows_unpack]
      cases c.testBit k <;> rfl
    change _ = unpackR 24 (sumAK AK c l (nIf(bit c k, Nat.xor acc (getL 0 AK k), acc)))
    rw [bit_eq', List.foldl_cons, e, fold_sumAK AK c l]

theorem annW_unpack (RS AK bK : List Nat) (CP j i : Nat) :
    annW 24 (RS.map (unpackR 24)) (unpackR 24 CP) (AK.map (unpackR 24)) bK j i =
      unpackR 24 (annK RS AK bK CP j i) := by
  unfold annW annK
  dsimp only
  rw [strictN_eq, strictN_eq, idRows_eq', getD_map_unpack, cact_unpack, vecMulN_unpackR,
    getD_eq_getL, zeroRows_eq, fold_sumAK, getD_map_unpack, mulWK_unpack,
    addRows_unpack]
  rfl

theorem selK_sound {RS AK bK : List Nat} {CP v0 : Nat} : ∀ {sel : List (Nat × Nat × Nat)},
    selK RS AK bK CP v0 sel = true →
      ∀ t ∈ sel, vmF 24 (trK 24 (annK RS AK bK CP t.1 t.2.1)) v0 = 0
  | [], _ => by simp
  | t :: sel, h => by
    change andB (Nat.beq (vmF 24 (trK 24 (annK RS AK bK CP t.1 t.2.1)) v0) 0)
      (selK RS AK bK CP v0 sel) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    intro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact Nat.eq_of_beq_eq_true h1
    · exact selK_sound h2 t' ht'

theorem allN_true' {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    change andB (f n) (allN n f) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem beq_of_eqK {A B : Nat} (h : eqK A B = true) : unpackR 24 A = unpackR 24 B := by
  rw [← beq_unpack] at h
  exact beq_iff_eq.1 h

theorem wordRows_eq (rs is : List (Array Nat)) (w : List Int) :
    wordRows 24 rs is w = CFSG.Sporadic.Co1Schreier.Native.word rs is w := rfl

theorem map_vmF_lt (L : List Nat) (f : Nat → Nat) : ∀ v ∈ L.map (fun T => vmF 24 T (f T)), v < 2 ^ 24 := by
  intro v hv
  obtain ⟨T, -, rfl⟩ := List.mem_map.1 hv
  exact vmF_lt 24 T _

theorem pow_unpack' (M : Nat) : ∀ e : Nat,
    CFSG.Sporadic.Co1Schreier.Native.pow (unpackR 24 M) e = unpackR 24 (powWK M e)
  | 0 => one_eq
  | e + 1 => by
    have h : powWK M (e + 1) = strictN (powWK M e) (fun a => mulWK a M) := rfl
    rw [strictN_eq] at h
    rw [CFSG.Sporadic.Co1Schreier.Native.pow, pow_unpack' M e, mul_unpackW, h]
    rfl

theorem invsK_map : ∀ {RS RIS : List Nat}, invsK RS RIS = true →
    (RS.map (unpackR 24)).map CFSG.Sporadic.Co1Schreier.Native.inv = RIS.map (unpackR 24)
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | m :: RS, mi :: RIS, h => by
    change andB (andB (canK m) (canK mi)) (andB (Nat.beq (mulK m mi) oneK) (invsK RS RIS)) = true at h
    obtain ⟨-, h2⟩ := andB_true h
    obtain ⟨h3, h4⟩ := andB_true h2
    simp only [List.map_cons]
    rw [inv_unpackR (Nat.eq_of_beq_eq_true h3), invsK_map h4]

theorem spinK_invs {RS RIS : List Nat} {bw : List (List Int)} {v0 : Nat} {sel : List (Nat × Nat × Nat)}
    {m : Nat} {AK ATK bK : List Nat} {CP LP WC PP : Nat}
    (h : spinK RS RIS bw v0 sel m AK ATK bK CP LP WC PP = true) : invsK RS RIS = true :=
  (andB_true h).1

theorem spinK_ATK {RS RIS : List Nat} {bw : List (List Int)} {v0 : Nat} {sel : List (Nat × Nat × Nat)}
    {m : Nat} {AK ATK bK : List Nat} {CP LP WC PP : Nat}
    (h : spinK RS RIS bw v0 sel m AK ATK bK CP LP WC PP = true) :
    AK = bw.map (wordK RS RIS) ∧ ATK = AK.map (trK 24) ∧ bw.length = 24 := by
  unfold spinK at h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, -⟩ := andB_true h
  exact ⟨leqK_sound h3, leqK_sound h4, Nat.eq_of_beq_eq_true h2⟩

theorem A_unpack {D : SpinData} {RS RIS AK : List Nat} (hd : D.d = 24)
    (hrs : D.rs = RS.map (unpackR 24)) (his : D.is = RIS.map (unpackR 24))
    (hAK : AK = D.bw.map (wordK RS RIS)) : D.A = AK.map (unpackR 24) := by
  obtain ⟨d, rs, is, v0, bw, C, sel, lam, wcols, pcoords⟩ := D
  dsimp only at hd hrs his hAK
  subst hd hrs his hAK
  change bw.map (wordRows 24 _ _) = _
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, wordRows_eq, word_sound]

theorem mx_unpack {D : SpinData} {AK ATK : List Nat} {CP WC : Nat} (hd : D.d = 24)
    (hC : D.C = unpackR 24 CP) (hW : D.wcolsArr = unpackR 24 WC) (hA : D.A = AK.map (unpackR 24))
    (hATK : ATK = AK.map (trK 24)) (hl : AK.length = 24) (x : Nat) :
    D.mx x = unpackR 24 (mxK ATK CP WC x) := by
  obtain ⟨d, rs, is, v0, bw, C, sel, lam, wcols, pcoords⟩ := D
  dsimp only at hd hC
  subst hd hC
  change mxW 24 (unpackR 24 CP) (SpinData.A _) (vecMulN 24 (SpinData.wcolsArr _) x) = _
  rw [hA, hW, vecMulN_unpackR]
  unfold mxW mxK
  have e : (AK.map (unpackR 24)).map (fun X => cact 24 X (vmF 24 WC x)) =
      ATK.map fun T => vmF 24 T (vmF 24 WC x) := by
    rw [List.map_map, hATK, List.map_map]
    refine List.map_congr_left fun X _ => ?_
    rw [Function.comp_apply, Function.comp_apply, cact_unpack]
  rw [e, toArray_packL (by rw [List.length_map, hATK, List.length_map, hl]) (map_vmF_lt ATK _),
    mulWK_unpack, transposeRows_unpackR]

theorem spinOK_of {D : SpinData} {RS RIS AK ATK bK : List Nat} {CP LP WC PP : Nat}
    (hd : D.d = 24) (hrs : D.rs = RS.map (unpackR 24)) (his : D.is = RIS.map (unpackR 24))
    (hC : D.C = unpackR 24 CP) (hlam : D.lam = unpackR 24 LP)
    (hW : D.wcolsArr = unpackR 24 WC) (hP : D.Pp = unpackR 24 PP)
    (h : spinK RS RIS D.bw D.v0 D.sel D.wcols.length AK ATK bK CP LP WC PP = true) :
    spinOK D = true := by
  obtain ⟨d, rs, is, v0, bw, C, sel, lam, wcols, pcoords⟩ := D
  dsimp only at hd hrs his hC hlam h
  subst hd hrs his hC hlam
  unfold spinK at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h⟩ := andB_true h
  obtain ⟨h6, h⟩ := andB_true h
  obtain ⟨h7, h⟩ := andB_true h
  obtain ⟨h8, h⟩ := andB_true h
  obtain ⟨h9, h⟩ := andB_true h
  obtain ⟨h10, h11⟩ := andB_true h
  obtain ⟨hlen, hinv⟩ := invsK_sound RS RIS h1
  have hbw : bw.length = 24 := Nat.eq_of_beq_eq_true h2
  have hAK : AK = bw.map (wordK RS RIS) := leqK_sound h3
  have hATK : ATK = AK.map (trK 24) := leqK_sound h4
  have hbK : bK = ATK.map fun T => vmF 24 T v0 := leqK_sound h5
  have hsel : sel.length = 24 := Nat.eq_of_beq_eq_true h7
  have hm : wcols.length ≤ 24 := Nat.le_of_ble_eq_true h9
  have hAKl : AK.length = 24 := by rw [hAK, List.length_map, hbw]
  have hATKl : ATK.length = 24 := by rw [hATK, List.length_map, hAKl]
  have hbKl : bK.length = 24 := by rw [hbK, List.length_map, hATKl]
  have hA : SpinData.A ⟨24, RS.map (unpackR 24), RIS.map (unpackR 24), v0, bw, unpackR 24 CP, sel,
      unpackR 24 LP, wcols, pcoords⟩ = AK.map (unpackR 24) := by
    change bw.map (wordRows 24 _ _) = _
    rw [hAK, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    rw [Function.comp_apply, wordRows_eq, word_sound]
  have hb : SpinData.b ⟨24, RS.map (unpackR 24), RIS.map (unpackR 24), v0, bw, unpackR 24 CP, sel,
      unpackR 24 LP, wcols, pcoords⟩ = bK := by
    change (SpinData.A _).map _ = _
    rw [hA, List.map_map, hbK, hATK, List.map_map]
    refine List.map_congr_left fun X _ => ?_
    rw [Function.comp_apply, Function.comp_apply, cact_unpack]
  have hbB : ∀ v ∈ bK, v < 2 ^ 24 := by
    rw [hbK]
    intro v hv
    obtain ⟨T, -, rfl⟩ := List.mem_map.1 hv
    exact vmF_lt 24 T _
  unfold spinOK
  simp only [hA, hb, Bool.and_eq_true, decide_eq_true_eq, List.length_map, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, ?_⟩, hbw⟩, hbKl⟩, ?_⟩, ?_⟩, hsel⟩, ?_⟩, hm⟩, ?_⟩, ?_⟩
  ·
    intro j hj
    have hj' : j < RIS.length := hlen ▸ hj
    rw [getD_map_unpack_lt hj, getD_map_unpack_lt hj', mulRows_unpackR, idRows_eq',
      getL_eq, getL_eq, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
    obtain ⟨-, h⟩ := andB_true (hinv j hj hj')
    exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true h)
  · simp [unpackR]
  ·
    rw [toArray_packL hbKl hbB, mulWK_unpack, idRows_eq']
    exact beq_of_eqK h6
  ·
    intro t ht
    rw [annW_unpack, cact_unpack]
    exact selK_sound h8 t ht
  ·
    change addRows 24 (idRows 24) (mulRows 24 (transposeRows 24 (SpinData.wcolsArr _)) (SpinData.Pp _)) =
      mulRows 24 (unpackR 24 LP) (eselW 24 _ _ _ _ _)
    rw [hW, hP, transposeRows_unpackR, mulWK_unpack, idRows_eq', addRows_unpack]
    have he : eselW 24 (RS.map (unpackR 24)) (unpackR 24 CP) (AK.map (unpackR 24)) bK sel =
        unpackR 24 (packL (eselK RS AK bK CP sel)) := by
      unfold eselW
      rw [← toArray_packL]
      · rw [eselK]
        refine congrArg List.toArray (List.map_congr_left fun t _ => ?_)
        rw [annW_unpack, rowK_eq]
      · rw [eselK, List.length_map, hsel]
      · intro v hv
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 (by rwa [eselK] at hv)
        exact rowK_lt _ _
    rw [he, mulWK_unpack]
    exact beq_of_eqK h10
  ·
    intro x hx
    have hcand := allN_true' h11 x (by simpa using hx)
    unfold candK at hcand
    rw [strictB_eq', strictB_eq'] at hcand
    have hwx : SpinData.wx ⟨24, RS.map (unpackR 24), RIS.map (unpackR 24), v0, bw, unpackR 24 CP, sel,
        unpackR 24 LP, wcols, pcoords⟩ x = vmF 24 WC x := by
      change vecMulN 24 (SpinData.wcolsArr _) x = _
      rw [hW, vecMulN_unpackR]
    rw [hwx]
    have hmx : transposeRows 24 (mxW 24 (unpackR 24 CP) (AK.map (unpackR 24)) (vmF 24 WC x)) =
        unpackR 24 (mtK ATK CP (vmF 24 WC x)) := by
      unfold mxW mtK
      have hl : (AK.map (unpackR 24)).map (fun X => cact 24 X (vmF 24 WC x)) =
          ATK.map fun T => vmF 24 T (vmF 24 WC x) := by
        rw [List.map_map, hATK, List.map_map]
        refine List.map_congr_left fun X _ => ?_
        rw [Function.comp_apply, Function.comp_apply, cact_unpack]
      rw [hl, toArray_packL (by rw [List.length_map, hATKl]) (map_vmF_lt ATK _), mulWK_unpack,
        transposeRows_unpackR, transposeRows_unpackR]
    rw [hmx]
    intro i hi
    have hc := allN_true' hcand i hi
    have hAt : ((AK.map (unpackR 24)).map (transposeRows 24)).getD i #[] = unpackR 24 (getL 0 ATK i) := by
      rw [List.map_map]
      have : (transposeRows 24 ∘ unpackR 24) = unpackR 24 ∘ trK 24 := by
        funext X
        exact transposeRows_unpackR 24 X
      rw [this, ← List.map_map, ← hATK]
      exact getD_map_unpack_lt (by rw [hATKl]; exact hi) _
    rw [hAt, vecMulN_unpackR, vecMulN_unpackR, getD_eq_getL]
    exact Nat.eq_of_beq_eq_true hc

end CFSG.KC.Co1BSpin

end
