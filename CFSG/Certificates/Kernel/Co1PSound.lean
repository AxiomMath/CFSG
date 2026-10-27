module

public import Certificates.Data.Kernel.Co1P
public import CFSG.Certificates.Kernel.TreeKSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Certificates.Kernel.LocalCompExcTextSound
public import CFSG.Sporadic.Co1Patterson.GraphInputs
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native

theorem shiftLeft_one (w : Nat) : Nat.shiftLeft 1 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem fieldsK_eq (w : Nat) : ∀ (per c : Nat),
    fieldsK w per c = (List.range per).map fun j => (c >>> (w * j)) % 2 ^ w
  | 0, _ => rfl
  | per + 1, c => by
    change List.cons (Nat.mod c (Nat.shiftLeft 1 w)) (fieldsK w per (Nat.shiftRight c w)) = _
    rw [fieldsK_eq w per, List.range_succ_eq_map, List.map_cons, List.map_map, shiftLeft_one]
    congr 1
    apply List.map_congr_left
    intro a _
    change c >>> w >>> (w * a) % 2 ^ w = c >>> (w * (a + 1)) % 2 ^ w
    rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm (w * a) w]

theorem masksK_eq (w per : Nat) : ∀ chunks : List Nat,
    masksK w per chunks = CFSG.Sporadic.Co1Block.masksOf w per chunks
  | [] => rfl
  | c :: cs => by
    change List.append (fieldsK w per c) (masksK w per cs) = _
    rw [masksK_eq w per cs, fieldsK_eq]
    simp only [CFSG.Sporadic.Co1Block.masksOf, List.flatMap_cons]
    rfl

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem bit_eq (m l : Nat) : Nat.beq (Nat.land (Nat.shiftRight m l) 1) 1 = m.testBit l := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((m >>> l) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  cases h : m / 2 ^ l % 2 == 1
  · have : m / 2 ^ l % 2 ≠ 1 := by simpa using h
    rw [decide_eq_false this]
    exact beq_false_of_ne this
  · have : m / 2 ^ l % 2 = 1 := by simpa using h
    rw [decide_eq_true this, this]
    rfl

theorem bitsK_eq (h m : Nat) : ∀ (k l : Nat),
    bitsK h m k l = ((List.range' l k).filter fun j => m.testBit j).map fun j => (h, j)
  | 0, _ => rfl
  | k + 1, l => by
    change Bool.rec (motive := fun _ => List (Nat × Nat)) (bitsK h m k (Nat.succ l))
      (List.cons (Prod.mk h l) (bitsK h m k (Nat.succ l)))
      (Nat.beq (Nat.land (Nat.shiftRight m l) 1) 1) = _
    rw [bit_eq, bitsK_eq h m k, List.range'_succ, List.filter_cons]
    cases m.testBit l <;> rfl

theorem recsFrom_eq (w : Nat) : ∀ (ms : List Nat) (h : Nat),
    recsFrom w ms h = (ms.zipIdx h).flatMap fun p =>
      ((List.range w).filter fun l => p.1.testBit l).map fun l => (p.2, l)
  | [], _ => rfl
  | m :: ms, h => by
    change List.append (bitsK h m w 0) (recsFrom w ms (h + 1)) = _
    rw [recsFrom_eq w ms (h + 1), bitsK_eq, List.zipIdx_cons, List.flatMap_cons, List.range_eq_range']
    rfl

theorem recsK_eq (w : Nat) (ms : List Nat) : recsK w ms = CFSG.Sporadic.Co1Block.recsOf w ms := by
  rw [recsK, recsFrom_eq, CFSG.Sporadic.Co1Block.recsOf]

theorem treeOfMasks_eq (w per : Nat) (chunks : List Nat) :
    CFSG.Sporadic.Co1Block.treeOfMasks w per chunks =
      ((0 :: (recsK w (masksK w per chunks)).map Prod.fst).toArray,
        (0 :: (recsK w (masksK w per chunks)).map Prod.snd).toArray) := by
  rw [recsK_eq, masksK_eq]
  rfl

@[expose] def foldPush {α : Type} (n : Nat) (step : Nat → Array α → α) : Array α :=
  (List.range n).foldl (fun acc i => acc.push (step i acc)) #[]

theorem foldPush_spec {α : Type} [Inhabited α] {step : Nat → Array α → α} {f : Nat → α} :
    ∀ n : Nat, (∀ i < n, ∀ acc : Array α, acc.size = i → (∀ j < i, acc[j]! = f j) →
      step i acc = f i) → (foldPush n step).size = n ∧ ∀ j < n, (foldPush n step)[j]! = f j
  | 0, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hs => by
    obtain ⟨h1, h2⟩ := foldPush_spec n fun i hi => hs i (by omega)
    have e : foldPush (n + 1) step = (foldPush n step).push (step n (foldPush n step)) := by
      unfold foldPush
      rw [List.range_succ, List.foldl_append]
      rfl
    have hn := hs n (by omega) _ h1 h2
    rw [e]
    refine ⟨by rw [Array.size_push, h1], fun j hj => ?_⟩
    rw [getElem!_pos _ j (by rw [Array.size_push, h1]; exact hj), Array.getElem_push]
    split
    · rename_i hlt
      rw [← getElem!_pos _ j hlt, h2 j (by rw [h1] at hlt; exact hlt)]
    · rename_i hlt
      have : j = n := by rw [h1] at hlt; omega
      subst this
      exact hn

variable {rs : List (Nat × Nat)} {ng : Nat}

@[expose] def treeArr (rs : List (Nat × Nat)) : Array Nat × Array Nat :=
  ((0 :: rs.map Prod.fst).toArray, (0 :: rs.map Prod.snd).toArray)

theorem treeArr_par {i : Nat} (hi : i < rs.length) :
    (treeArr rs).1[i + 1]! = rs[i].1 := by
  unfold treeArr
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

theorem treeArr_lab {i : Nat} (hi : i < rs.length) :
    (treeArr rs).2[i + 1]! = rs[i].2 := by
  unfold treeArr
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

theorem treeArr_size : (treeArr rs).1.size = rs.length + 1 := by simp [treeArr]

theorem walkAt_zero {act : Nat → Nat → Nat} {root : Nat} (h : (treePts act ng root rs).2 = true) :
    walkAt act ng root rs 0 = root := by
  rw [walkAt, (treePts_sound h).2.1]
  rfl

theorem walkAt_succ {act : Nat → Nat → Nat} {root : Nat} (h : (treePts act ng root rs).2 = true)
    {i : Nat} (hi : i < rs.length) :
    rs[i].1 ≤ i ∧ rs[i].2 < ng ∧
      walkAt act ng root rs (i + 1) = act rs[i].2 (walkAt act ng root rs rs[i].1) := by
  obtain ⟨hlen, -, hst⟩ := treePts_sound h
  obtain ⟨hp, hl, he⟩ := hst i hi
  refine ⟨hp, hl, ?_⟩
  rw [walkAt, walkAt, he, List.getElem?_eq_getElem (by omega)]
  rfl

theorem treeHs_eq (G : Array Rows) (c : CFSG.Sporadic.Co1.InvNative.ConjCert) :
    CFSG.Sporadic.Co1Patterson.Native.treeHs G c = foldPush c.pts.size (fun i acc =>
      if i == 0 then one else mul G[c.lab[i]!]! acc[c.par[i]!]!) := rfl

theorem treeHis_eq (Gi : Array Rows) (c : CFSG.Sporadic.Co1.InvNative.ConjCert) :
    CFSG.Sporadic.Co1Patterson.Native.treeHis Gi c = foldPush c.pts.size (fun i acc =>
      if i == 0 then one else mul acc[c.par[i]!]! Gi[c.lab[i]!]!) := rfl

theorem treeHs_get {G : Array Rows} {GK : List Nat} (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
    (h : (treePts (hsAct GK) ng oneK rs).2 = true) (pts : Array Rows)
    (hn : pts.size = rs.length + 1) :
    (CFSG.Sporadic.Co1Patterson.Native.treeHs G ⟨pts, (treeArr rs).1, (treeArr rs).2⟩).size =
        rs.length + 1 ∧
      ∀ j < rs.length + 1, (CFSG.Sporadic.Co1Patterson.Native.treeHs G
        ⟨pts, (treeArr rs).1, (treeArr rs).2⟩)[j]! = unpackR 24 (walkAt (hsAct GK) ng oneK rs j) := by
  rw [treeHs_eq]
  simp only [hn]
  refine foldPush_spec _ fun i hi acc hacc hprev => ?_
  rcases i with _ | i
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [walkAt_zero h, CFSG.KC.Co1B.one_eq]
  · have hi' : i < rs.length := by omega
    obtain ⟨hp, hl, he⟩ := walkAt_succ h hi'
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte]
    change mul G[(treeArr rs).2[i + 1]!]! acc[(treeArr rs).1[i + 1]!]! = _
    rw [treeArr_par hi', treeArr_lab hi', hprev _ (by omega), hG _ hl, he, CFSG.KC.F2W.mul_unpackW]
    rfl

theorem treeHis_get {Gi : Array Rows} {GiK : List Nat}
    (hG : ∀ l < ng, Gi[l]! = unpackR 24 (getL 0 GiK l))
    (h : (treePts (hisAct GiK) ng oneK rs).2 = true) (pts : Array Rows)
    (hn : pts.size = rs.length + 1) :
    (CFSG.Sporadic.Co1Patterson.Native.treeHis Gi ⟨pts, (treeArr rs).1, (treeArr rs).2⟩).size =
        rs.length + 1 ∧
      ∀ j < rs.length + 1, (CFSG.Sporadic.Co1Patterson.Native.treeHis Gi
        ⟨pts, (treeArr rs).1, (treeArr rs).2⟩)[j]! = unpackR 24 (walkAt (hisAct GiK) ng oneK rs j) := by
  rw [treeHis_eq]
  simp only [hn]
  refine foldPush_spec _ fun i hi acc hacc hprev => ?_
  rcases i with _ | i
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [walkAt_zero h, CFSG.KC.Co1B.one_eq]
  · have hi' : i < rs.length := by omega
    obtain ⟨hp, hl, he⟩ := walkAt_succ h hi'
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte]
    change mul acc[(treeArr rs).1[i + 1]!]! Gi[(treeArr rs).2[i + 1]!]! = _
    rw [treeArr_par hi', treeArr_lab hi', hprev _ (by omega), hG _ hl, he, CFSG.KC.F2W.mul_unpackW]
    rfl

theorem toList_eq_map {arr : Array Rows} {L : List Nat} (hs : arr.size = L.length)
    (h : ∀ j < L.length, arr[j]! = unpackR 24 (L[j]?.getD 0)) : arr.toList = L.map (unpackR 24) := by
  apply List.ext_getElem (by simp [hs])
  intro j h1 h2
  have hj : j < L.length := by simpa using h2
  rw [Array.getElem_toList, ← getElem!_pos arr j (by simpa using h1), h j hj, List.getElem_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem contains_map_unpack (L : List Nat) (X : Nat) :
    (L.map (unpackR 24)).contains (unpackR 24 X) = L.any fun y => eqK X y := by
  rw [List.contains_eq_any_beq, List.any_map]
  simp only [Function.comp_def, beq_unpack]

theorem walk_length {act : Nat → Nat → Nat} {root : Nat} (h : (treePts act ng root rs).2 = true) :
    (treePts act ng root rs).1.length = rs.length + 1 := (treePts_sound h).1

theorem gtOfMasks_get {G : Array Rows} {GK : List Nat}
    (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
    (h : (treePts (hisAct GK) ng oneK rs).2 = true) :
    (CFSG.Sporadic.Co1Block.gtOfMasks G (treeArr rs)).pts.size = rs.length + 1 ∧
      ∀ j < rs.length + 1, (CFSG.Sporadic.Co1Block.gtOfMasks G (treeArr rs)).pts[j]! =
        unpackR 24 (walkAt (hisAct GK) ng oneK rs j) := by
  have e : (CFSG.Sporadic.Co1Block.gtOfMasks G (treeArr rs)).pts = foldPush (treeArr rs).1.size
      (fun i acc => if i == 0 then CFSG.Sporadic.SmallF2.Native.idRows 24 else
        CFSG.Sporadic.SmallF2.Native.mulRows 24 acc[(treeArr rs).1[i]!]! G[(treeArr rs).2[i]!]!) := rfl
  rw [e, treeArr_size]
  refine foldPush_spec _ fun i hi acc hacc hprev => ?_
  rcases i with _ | i
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [walkAt_zero h]
    exact CFSG.KC.Co1B.one_eq
  · have hi' : i < rs.length := by omega
    obtain ⟨hp, hl, he⟩ := walkAt_succ h hi'
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte]
    rw [treeArr_par hi', treeArr_lab hi', hprev _ (by omega), hG _ hl, he]
    exact CFSG.KC.F2W.mul_unpackW _ _

section Orb

open CFSG.Sporadic.Co1Patterson.Native

variable {G Gi : Array Rows} {GK GiK : List Nat} {R : Nat}
  (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
  (hGi : ∀ l < ng, Gi[l]! = unpackR 24 (getL 0 GiK l))
  (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)

include hG hh in
theorem mkOrbT_hs {j : Nat} (hj : j < rs.length + 1) :
    (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).hs[j]! = unpackR 24 (walkAt (hsAct GK) ng oneK rs j) :=
  (treeHs_get hG hh _ (by simp [treeArr_size])).2 j hj

include hGi hhi in
theorem mkOrbT_his {j : Nat} (hj : j < rs.length + 1) :
    (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).his[j]! =
      unpackR 24 (walkAt (hisAct GiK) ng oneK rs j) :=
  (treeHis_get hGi hhi _ (by simp [treeArr_size])).2 j hj

theorem mkOrbT_size : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts.size = rs.length + 1 := by
  simp [mkOrbT, treeArr_size]

include hG hGi hh hhi in
theorem mkOrbT_pts {j : Nat} (hj : j < rs.length + 1) :
    (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts[j]! = unpackR 24
      (mulWK (mulWK (walkAt (hsAct GK) ng oneK rs j) R) (walkAt (hisAct GiK) ng oneK rs j)) := by
  have e : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts[j]! =
      mul (mul (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).hs[j]! (unpackR 24 R))
        (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).his[j]! := by
    simp only [mkOrbT]
    rw [getElem!_pos _ j (by simp [treeArr_size]; omega)]
    simp
  rw [e, mkOrbT_hs hG hh hj, mkOrbT_his hGi hhi hj, CFSG.KC.F2W.mul_unpackW,
    CFSG.KC.F2W.mul_unpackW]
  rfl

end Orb

theorem invsOK_sound : ∀ (G Gi : List Nat), invsOK G Gi = true →
    G.length = Gi.length ∧ ∀ l < G.length, Nat.beq (mulWK (getL 0 G l) (getL 0 Gi l)) oneK = true
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | g :: G, gi :: Gi, h => by
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
    obtain ⟨hl, hr⟩ := invsOK_sound G Gi h2
    refine ⟨by simp [hl], fun l hl' => ?_⟩
    rcases l with _ | l
    · exact h1
    · exact hr l (by simpa using hl')

theorem conjL_get (R : Nat) : ∀ (HS HIS : List Nat), HS.length = HIS.length →
    (conjL R HS HIS).length = HS.length ∧ ∀ j < HS.length,
      (conjL R HS HIS)[j]?.getD 0 = mulWK (mulWK (HS[j]?.getD 0) R) (HIS[j]?.getD 0)
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | h :: HS, hi :: HIS, hl => by
    obtain ⟨h1, h2⟩ := conjL_get R HS HIS (by simpa using hl)
    change (List.cons (mulWK (mulWK h R) hi) (conjL R HS HIS)).length = _ ∧
      ∀ j < (h :: HS).length, (List.cons (mulWK (mulWK h R) hi) (conjL R HS HIS))[j]?.getD 0 = _
    refine ⟨by simp [h1], fun j hj => ?_⟩
    rcases j with _ | j
    · rfl
    · simpa using h2 j (by simpa using hj)

theorem modL_eq : ∀ xs : List Nat, modL xs = xs.map fun x => Nat.mod x (Nat.shiftLeft 1 576)
  | [] => rfl
  | x :: xs => by
    change List.cons (Nat.mod x (Nat.shiftLeft 1 576)) (modL xs) = _
    rw [modL_eq xs]
    rfl

theorem strictInc_of_pairwise' : ∀ {l : List Nat}, l.Pairwise (· < ·) →
    CFSG.Sporadic.Co1.InvNative.strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 := List.rel_of_pairwise_cons h List.mem_cons_self
    simp only [CFSG.Sporadic.Co1.InvNative.strictInc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, strictInc_of_pairwise' (List.Pairwise.of_cons h)⟩

theorem distinctKeys_of_nodup {keys : List Nat} (h : keys.Nodup) :
    CFSG.Sporadic.Co1.InvNative.distinctKeys keys = true := by
  unfold CFSG.Sporadic.Co1.InvNative.distinctKeys
  apply strictInc_of_pairwise'
  have hs := List.pairwise_mergeSort (le := CFSG.Sporadic.Co1.InvNative.keyLe)
    (fun a b c h1 h2 => by
      simp only [CFSG.Sporadic.Co1.InvNative.keyLe, decide_eq_true_eq] at *
      omega)
    (fun a b => by simp only [CFSG.Sporadic.Co1.InvNative.keyLe, Bool.or_eq_true,
      decide_eq_true_eq]; omega) keys
  have hn : (keys.mergeSort CFSG.Sporadic.Co1.InvNative.keyLe).Nodup :=
    (List.mergeSort_perm keys _).nodup_iff.2 h
  exact (hs.and (List.nodup_iff_pairwise_ne.1 hn)).imp fun ⟨h1, h2⟩ => by
    simp only [CFSG.Sporadic.Co1.InvNative.keyLe, decide_eq_true_eq] at h1
    omega

theorem eqK_iff (X y : Nat) :
    eqK X y = true ↔ Nat.mod X (Nat.shiftLeft 1 576) = Nat.mod y (Nat.shiftLeft 1 576) :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by
    unfold eqK
    rw [Nat.beq_eq]
    exact h⟩

theorem nodup_keys {L : List Nat} (h : (modL L).Nodup) :
    ((L.map (unpackR 24)).map CFSG.Sporadic.Co1.InvNative.rowsKey).Nodup := by
  have key : ∀ a b : Nat, CFSG.Sporadic.Co1.InvNative.rowsKey (unpackR 24 a) =
      CFSG.Sporadic.Co1.InvNative.rowsKey (unpackR 24 b) →
      Nat.mod a (Nat.shiftLeft 1 576) = Nat.mod b (Nat.shiftLeft 1 576) := by
    intro a b e
    have e' := CFSG.Sporadic.Co1.Module.rowsKey_inj (validRows_unpackR a) (validRows_unpackR b) e
    refine (eqK_iff a b).1 ?_
    rw [← beq_unpack, e']
    exact beq_self_eq_true _
  have h2 : L.Pairwise fun a b => Nat.mod a (Nat.shiftLeft 1 576) ≠ Nat.mod b (Nat.shiftLeft 1 576) := by
    have h' := h
    rw [modL_eq] at h'
    exact List.pairwise_map.1 h'
  have h3 : L.Pairwise fun a b => CFSG.Sporadic.Co1.InvNative.rowsKey (unpackR 24 a) ≠
      CFSG.Sporadic.Co1.InvNative.rowsKey (unpackR 24 b) :=
    h2.imp fun hne e => hne (key _ _ e)
  exact List.pairwise_map.2 (List.pairwise_map.2 h3)

section Chk

open CFSG.Sporadic.Co1Patterson.Native

theorem orbOK_of_chk {G Gi : Array Rows} {GK GiK : List Nat} {R np : Nat} (hGs : G.size = ng)
    (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
    (hGi : ∀ l < ng, Gi[l]! = unpackR 24 (getL 0 GiK l)) (h : orbChk GK GiK ng R np rs = true) :
    orbOK G Gi (unpackR 24 R) (mkOrbT G Gi (unpackR 24 R) (treeArr rs)) = true := by
  have e : orbChk GK GiK ng R np rs = CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (treePts (hsAct GK) ng oneK rs).2
      (treePts (hisAct GiK) ng oneK rs).2) (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (lenL GK) ng) (invsOK GK GiK))
      (distinctK np (modL (conjL R (treePts (hsAct GK) ng oneK rs).1
        (treePts (hisAct GiK) ng oneK rs).1)))) := by
    unfold orbChk
    rcases treePts (hsAct GK) ng oneK rs with ⟨a, b⟩
    rcases treePts (hisAct GiK) ng oneK rs with ⟨c, d⟩
    rfl
  rw [e] at h
  obtain ⟨h12, h34⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨hh, hhi⟩ := CFSG.KC.TreeK.andB_true h12
  obtain ⟨h3, hd⟩ := CFSG.KC.TreeK.andB_true h34
  obtain ⟨hlen, hinv⟩ := CFSG.KC.TreeK.andB_true h3
  have hlenG : GK.length = ng := by rw [← CFSG.KC.Co1B.lenL_eq]; exact Nat.eq_of_beq_eq_true hlen
  obtain ⟨hGG, hgi⟩ := invsOK_sound GK GiK hinv
  have l1 := walk_length hh
  have l2 := walk_length hhi
  obtain ⟨cl, cg⟩ := conjL_get R _ _ (l1.trans l2.symm)
  have hn := mkOrbT_size (G := G) (Gi := Gi) (R := R) (rs := rs)
  have hhs := treeHs_get hG hh (Array.replicate (treeArr rs).1.size (unpackR 24 R))
    (by simp [treeArr_size])
  have hhis := treeHis_get hGi hhi (Array.replicate (treeArr rs).1.size (unpackR 24 R))
    (by simp [treeArr_size])
  have hpts : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts.toList =
      (conjL R (treePts (hsAct GK) ng oneK rs).1 (treePts (hisAct GiK) ng oneK rs).1).map
        (unpackR 24) := by
    refine toList_eq_map (by rw [hn, cl, l1]) fun j hj => ?_
    rw [cl, l1] at hj
    rw [mkOrbT_pts hG hGi hh hhi hj, cg j (by rw [l1]; exact hj)]
    rfl
  have epar : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.par = (treeArr rs).1 := rfl
  have elab' : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.lab = (treeArr rs).2 := rfl
  have ehs : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).hs = CFSG.Sporadic.Co1Patterson.Native.treeHs G
      ⟨Array.replicate (treeArr rs).1.size (unpackR 24 R), (treeArr rs).1, (treeArr rs).2⟩ := rfl
  have ehis : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).his =
      CFSG.Sporadic.Co1Patterson.Native.treeHis Gi
        ⟨Array.replicate (treeArr rs).1.size (unpackR 24 R), (treeArr rs).1, (treeArr rs).2⟩ := rfl
  unfold orbOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by rw [hn]; omega, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hn]; exact hhs.1
  · rw [hn]; exact hhis.1
  · simp [mkOrbT, treeArr_size]
  · simp [mkOrbT, treeArr]
  · intro l hl
    rw [hGs] at hl
    rw [hG l hl, hGi l hl, CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq]
    exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (hgi l (by rw [hlenG]; exact hl)))
  · rw [ehs, hhs.2 0 (by omega), walkAt_zero hh, ← CFSG.KC.Co1B.one_eq]
  · rw [ehis, hhis.2 0 (by omega), walkAt_zero hhi, ← CFSG.KC.Co1B.one_eq]
  · intro i hi
    rw [hn] at hi
    rcases i with _ | i
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hi' : i < rs.length := by omega
      obtain ⟨hp, hl, he⟩ := walkAt_succ hh hi'
      obtain ⟨-, -, he'⟩ := walkAt_succ hhi hi'
      rw [epar, elab', ehs, ehis, treeArr_par hi', treeArr_lab hi', hhs.2 _ (by omega),
        hhs.2 _ (by omega), hhis.2 _ (by omega), hhis.2 _ (by omega), he, he', hG _ hl, hGi _ hl,
        hGs, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
      exact ⟨⟨⟨by omega, hl⟩, rfl⟩, rfl⟩
  · intro i hi
    rw [hn] at hi
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [mkOrbT_pts hG hGi hh hhi hi]
      exact validRows_unpackR _
    · rw [ehs, hhs.2 i hi]
      exact validRows_unpackR _
    · rw [ehis, hhis.2 i hi]
      exact validRows_unpackR _
    · simp only [mkOrbT]
      rw [getElem!_pos _ i (by simp [treeArr_size]; omega)]
      simp
  · rw [hpts]
    apply distinctKeys_of_nodup
    apply nodup_keys
    exact distinctK_sound hd

end Chk

@[expose] def inorder : KT → List Nat
  | .leaf => []
  | .node l k r => inorder l ++ k :: inorder r

theorem buildKT_spec : ∀ (d : Nat) (xs : List Nat),
    inorder (buildKT d xs).1 ++ (buildKT d xs).2 = xs
  | 0, _ => rfl
  | d + 1, xs => by
    have hl := buildKT_spec d xs
    change inorder (Prod.rec (motive := fun _ => KT × List Nat)
      (fun L ys => List.rec (motive := fun _ => KT × List Nat) (Prod.mk L List.nil)
        (fun y zs _ => Prod.rec (motive := fun _ => KT × List Nat)
          (fun R rest => Prod.mk (KT.node L y R) rest) (buildKT d zs)) ys) (buildKT d xs)).1 ++
      (Prod.rec (motive := fun _ => KT × List Nat)
      (fun L ys => List.rec (motive := fun _ => KT × List Nat) (Prod.mk L List.nil)
        (fun y zs _ => Prod.rec (motive := fun _ => KT × List Nat)
          (fun R rest => Prod.mk (KT.node L y R) rest) (buildKT d zs)) ys) (buildKT d xs)).2 = xs
    rcases e : buildKT d xs with ⟨L, ys⟩
    rw [e] at hl
    rcases ys with _ | ⟨y, zs⟩
    · exact hl
    · have hr := buildKT_spec d zs
      dsimp only
      rcases e' : buildKT d zs with ⟨R, rest⟩
      rw [e'] at hr
      change inorder L ++ y :: inorder R ++ rest = xs
      rw [← hl, ← hr]
      simp

theorem memKT_sound : ∀ (t : KT) (x : Nat), (inorder t).Pairwise (· < ·) →
    memKT x t = decide (x ∈ inorder t)
  | .leaf, _, _ => rfl
  | .node l k r, x, h => by
    rw [inorder, List.pairwise_append] at h
    obtain ⟨hl, hr, hlr⟩ := h
    have hr' := List.pairwise_cons.1 hr
    change Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (memKT x r) true
      (Nat.beq x k)) (memKT x l) (Nat.blt x k) = _
    rw [memKT_sound l x hl, memKT_sound r x hr'.2]
    have hlk : ∀ a ∈ inorder l, a < k := fun a ha => hlr a ha k List.mem_cons_self
    have hkr : ∀ b ∈ inorder r, k < b := hr'.1
    rw [inorder]
    by_cases h1 : x < k
    · rw [show Nat.blt x k = true by simpa [Nat.blt_eq] using h1]
      simp only [List.mem_append, List.mem_cons]
      apply decide_eq_decide.2
      constructor
      · exact fun h => Or.inl h
      · rintro (h | h | h)
        · exact h
        · omega
        · exact absurd (hkr x h) (by omega)
    · rw [show Nat.blt x k = false from Bool.eq_false_iff.2 (by simpa [Nat.blt_eq] using h1)]
      by_cases h2 : x = k
      · subst h2
        rw [Nat.beq_refl]
        simp
      · rw [beq_false_of_ne h2]
        simp only [List.mem_append, List.mem_cons]
        apply decide_eq_decide.2
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact absurd (hlk x h) (by omega)
          · exact absurd h h2
          · exact h

theorem sincK_pairwise {l : List Nat} (h : sincK l = true) : l.Pairwise (· < ·) := by
  have key : ∀ (l : List Nat) (o : Option Nat), sincGo l o = true → l.Pairwise (· < ·) := by
    intro l
    induction l with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons x l ih =>
      intro o h
      have h2 : sincGo l (some x) = true := by
        revert h
        change CFSG.KLie.CT.andB _ (sincGo l (some x)) = true → _
        cases Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o <;>
          simp [CFSG.KLie.CT.andB]
      exact List.pairwise_cons.2 ⟨fun y hy => (sincGo_sound l (some x) h2).2 y hy x rfl, ih _ h2⟩
  exact key l none h

theorem memKT_treeOf {d : Nat} {xs : List Nat} (hs : sincK xs = true) (ha : treeAll d xs = true)
    (x : Nat) : memKT x (treeOf d xs) = decide (x ∈ xs) := by
  have hb := buildKT_spec d xs
  have hrest : (buildKT d xs).2 = [] := by
    unfold treeAll at ha
    rcases e : buildKT d xs with ⟨t, rest⟩
    rw [e] at ha
    cases rest with
    | nil => rfl
    | cons _ _ => exact absurd ha Bool.false_ne_true
  rw [hrest, List.append_nil] at hb
  have ht : treeOf d xs = (buildKT d xs).1 := by
    unfold treeOf
    rcases buildKT d xs with ⟨t, rest⟩
    rfl
  have hp : (inorder (buildKT d xs).1).Pairwise (· < ·) := by
    rw [hb]
    exact sincK_pairwise hs
  rw [ht, memKT_sound _ x hp, hb]

theorem any_eqK_memKT {L : List Nat} {d np : Nat} (hs : sincK (sortP np (modL L)) = true)
    (ha : treeAll d (sortP np (modL L)) = true) (X : Nat) :
    L.any (fun y => eqK X y) = memKT (Nat.mod X (Nat.shiftLeft 1 576)) (treeOf d (sortP np (modL L))) := by
  rw [memKT_treeOf hs ha]
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true, decide_eq_true_iff, (sortP_perm np (modL L)).mem_iff, modL_eq, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, ((eqK_iff X y).1 e).symm⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, (eqK_iff X y).2 e.symm⟩

theorem splitOn_semi' (cs : List Char) :
    (String.ofList cs).splitOn ";" = (cs.splitOn ';').map String.ofList :=
  CFSG.KC.G13.splitOn_one ";" ';' rfl rfl (by decide) rfl (by decide) cs

theorem parseWords_wordsC {W : List (List Int)} (hW : W ≠ []) :
    CFSG.Sporadic.Co1Patterson.Native.parseWords (String.ofList (wordsC W)) = W := by
  unfold CFSG.Sporadic.Co1Patterson.Native.parseWords wordsC
  rw [splitOn_semi', List.splitOn_intercalate ';' _ (by simpa using hW)]
  · rw [List.map_map, List.map_map]
    conv_rhs => rw [← List.map_id W]
    congr 1
    funext w
    exact CFSG.KC.LocalComp.ExcDeriv.parseWord w
  · intro l hl
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact (CFSG.KC.G13.intercalate_ok (S := ['-', ',']) (CFSG.KC.G13.sep_ok (by simp))
      (fun l hl => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hl
        exact CFSG.KC.G13.intC_ok (by simp) e)).not_mem rfl (by simp)

end CFSG.KC.Co1P

end
