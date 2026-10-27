module

public import Certificates.Data.Kernel.TabMatGrp
public import CFSG.Certificates.Kernel.TabMatSound
public import CFSG.Certificates.Kernel.SurjKSeedCore
public import CFSG.Certificates.WordPresentation

public section

namespace CFSG.KC.TabMatGrp

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.Certificates
  CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply rowsMatrix_mulRows rowsMatrix_idRows
  toVecD_apply)

@[expose] noncomputable def MatP (d M : Nat) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  rowsMatrix d (unpackR d M)

theorem MatP_mul (d X Y : Nat) : MatP d (mulF d X Y) = MatP d X * MatP d Y := by
  unfold MatP
  rw [← mulRows_unpackR, rowsMatrix_mulRows]

theorem MatP_id (d : Nat) : MatP d (idF d) = 1 := by
  unfold MatP
  rw [CFSG.KC.SurjSeed.unpackR_idF_gen, rowsMatrix_idRows]

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem notB_eq (a : Bool) : notB a = !a := by
  cases a <;> rfl

theorem seedsK_spec {d MA MB eA eB : Nat} {k : Nat → Nat → Bool}
    (h : seedsK d MA MB eA eB k = true) :
    MatP d MA * MatP d (powK d MA (Nat.pred eA)) = 1 ∧
      MatP d MB * MatP d (powK d MB (Nat.pred eB)) = 1 ∧
      k (powK d MA (Nat.pred eA)) (powK d MB (Nat.pred eB)) = true := by
  unfold seedsK at h
  simp only [strictB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · rw [← MatP_mul, Nat.eq_of_beq_eq_true h1, MatP_id]
  · rw [← MatP_mul, Nat.eq_of_beq_eq_true h2, MatP_id]

theorem seedsK_det {d MA MB eA eB : Nat} {k : Nat → Nat → Bool}
    (h : seedsK d MA MB eA eB k = true) : (MatP d MA).det ≠ 0 ∧ (MatP d MB).det ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := seedsK_spec h
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · have := congrArg Matrix.det h2
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this

theorem invW_acc : ∀ (w acc : List (Nat × Bool)),
    List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
      (fun l _ ih acc => ih (Prod.rec (motive := fun _ => Nat × Bool)
        (fun g b => (g, Bool.rec (motive := fun _ => Bool) true false b)) l :: acc)) w acc =
      (w.map fun l => (l.1, !l.2)).reverse ++ acc
  | [], _ => rfl
  | (g, b) :: w, acc => by
    rw [List.map_cons, List.reverse_cons, List.append_assoc, ← invW_acc w]
    cases b <;> rfl

theorem invW_natW {m : Nat} (s : List (Fin m × Bool)) : invW (natW s) = natW (FreeGroup.invRev s) := by
  unfold invW
  rw [invW_acc, List.append_nil]
  simp [natW, FreeGroup.invRev, List.map_reverse]

section Words

variable {d : Nat} {G : Type*} [Group G] {φ : G →* GL (Fin d) (ZMod 2)} {σ : Fin 2 → G}

variable (φ) in
noncomputable abbrev matOf (g : G) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  ((φ g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2))

theorem matOf_mul (g h : G) : matOf φ (g * h) = matOf φ g * matOf φ h := by
  simp [matOf]

theorem matOf_one : matOf φ (1 : G) = 1 := by
  simp [matOf]

theorem matOf_inv (g : G) : matOf φ g⁻¹ = (matOf φ g)⁻¹ := by
  simp [matOf, Matrix.coe_units_inv]

theorem MatP_inv_of {MA MAi : Nat} {g : G} (hA : MatP d MA = matOf φ g)
    (h : MatP d MA * MatP d MAi = 1) : MatP d MAi = matOf φ g⁻¹ := by
  rw [matOf_inv, ← hA]
  exact (Matrix.inv_eq_right_inv h).symm

theorem signedProd_invRev (s : List (Fin 2 × Bool)) :
    signedProd σ (FreeGroup.invRev s) = (signedProd σ s)⁻¹ := by
  rw [← lift_mk_eq_signedProd, ← lift_mk_eq_signedProd, ← FreeGroup.inv_mk, map_inv]

variable (σ) in
noncomputable abbrev segVal (segs : List (List (Fin 2 × Bool))) (i : Nat) : G :=
  signedProd σ (segs.getD i [])

variable {MA MAi MB MBi : Nat} (hA : MatP d MA = matOf φ (σ 0)) (hAi : MatP d MAi = matOf φ (σ 0)⁻¹)
  (hB : MatP d MB = matOf φ (σ 1)) (hBi : MatP d MBi = matOf φ (σ 1)⁻¹)
include hA hAi hB hBi

theorem MatP_letP (l : Fin 2 × Bool) :
    MatP d (letP MA MAi MB MBi (l.1.val, l.2)) = matOf φ (if l.2 then σ l.1 else (σ l.1)⁻¹) := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b
  · exact hAi
  · exact hA
  · exact hBi
  · exact hB

theorem MatP_wordFrom : ∀ (u : List (Fin 2 × Bool)) (acc : Nat),
    MatP d (wordFrom d MA MAi MB MBi (natW u) acc) = MatP d acc * matOf φ (signedProd σ u)
  | [], acc => by
    change MatP d acc = _
    rw [signedProd_nil, matOf_one, mul_one]
  | l :: u, acc => by
    change MatP d (strictN (mulW d acc (letP MA MAi MB MBi (l.1.val, l.2)))
      (wordFrom d MA MAi MB MBi (natW u))) = _
    rw [strictN_eq, MatP_wordFrom u, mulW_eq, MatP_mul, MatP_letP hA hAi hB hBi, signedProd_cons, matOf_mul,
      mul_assoc]

theorem MatP_wordP (u : List (Fin 2 × Bool)) :
    MatP d (wordP d MA MAi MB MBi (natW u)) = matOf φ (signedProd σ u) := by
  unfold wordP
  rw [MatP_wordFrom hA hAi hB hBi, MatP_id, one_mul]

theorem MatP_segFrom {segs : List (List (Fin 2 × Bool))} {k : Nat} (hk : k ≤ segs.length) :
    ∀ (w : List (Fin k × Bool)) (acc : Nat),
      MatP d (segFrom d ((segs.map natW).flatMap fun s =>
        [wordP d MA MAi MB MBi s, wordP d MA MAi MB MBi (invW s)]) (natW w) acc) =
        MatP d acc * matOf φ (signedProd (fun i : Fin k => segVal σ segs i.val) w)
  | [], acc => by
    change MatP d acc = _
    rw [signedProd_nil, matOf_one, mul_one]
  | (i, b) :: w, acc => by
    have hi : i.val < (segs.map natW).length := by simp; omega
    obtain ⟨e1, e2⟩ := CFSG.KC.TabMat.getL_pairs (wordP d MA MAi MB MBi)
      (fun s => wordP d MA MAi MB MBi (invW s)) (segs.map natW) i.val hi
    have hgd : segs.getD i.val [] = segs[i.val]'(by simpa using hi) := by
      rw [List.getD_eq_getElem]
    change MatP d (strictN (mulW d acc (gP _ (i.val, b))) (segFrom d _ (natW w))) = _
    rw [strictN_eq, MatP_segFrom hk w, mulW_eq, MatP_mul, signedProd_cons, matOf_mul, mul_assoc]
    congr 2
    unfold gP
    cases b
    · change MatP d (getL 0 _ (2 * i.val + 1)) = _
      rw [e2, List.getElem_map, invW_natW, MatP_wordP hA hAi hB hBi, signedProd_invRev (σ := σ),
        ← hgd]
      rfl
    · change MatP d (getL 0 _ (2 * i.val)) = _
      rw [e1, List.getElem_map, MatP_wordP hA hAi hB hBi, ← hgd]
      rfl

end Words

theorem MatP_inj {d M M' : Nat} (h : MatP d M = MatP d M') (hM : M < 2 ^ (d * d))
    (hM' : M' < 2 ^ (d * d)) : M = M' := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < d * d
  · have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hp
    have hi : p / d < d := (Nat.div_lt_iff_lt_mul hd).2 hp
    have hj : p % d < d := Nat.mod_lt _ hd
    have e := congrFun (congrFun h ⟨p / d, hi⟩) ⟨p % d, hj⟩
    have hr : ∀ N : Nat, (unpackR d N)[p / d]?.getD 0 = rowF d N (p / d) := fun N => by
      simp [unpackR, hi, rowF_eq]
    unfold MatP at e
    rw [rowsMatrix_apply, rowsMatrix_apply, hr, hr, toVecD_apply, toVecD_apply] at e
    rw [testBit_rowF d _ _ _ hj, testBit_rowF d _ _ _ hj, Nat.div_add_mod' p d] at e
    cases h1 : M.testBit p <;> cases h2 : M'.testBit p <;> simp_all
  · rw [Nat.not_lt] at hp
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hp)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM' (Nat.pow_le_pow_right (by norm_num) hp))]

theorem mulF_lt (d A B : Nat) : mulF d A B < 2 ^ (d * d) := by
  rw [mulF_eq_orN]
  exact orN_fields_lt fun i _ => vmF_lt d B _

theorem idF_lt (d : Nat) : idF d < 2 ^ (d * d) := by
  have hI : idF d = orN d fun i => pw2 i <<< (d * i) := rfl
  rw [hI]
  refine orN_fields_lt fun i hi => ?_
  change 1 <<< i < 2 ^ d
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by omega) hi

theorem segFrom_lt (d : Nat) (Gs : List Nat) :
    ∀ (w : List (Nat × Bool)) (acc : Nat), acc < 2 ^ (d * d) → segFrom d Gs w acc < 2 ^ (d * d)
  | [], _, h => h
  | l :: w, acc, _ => by
    change strictN (mulW d acc (gP Gs l)) (segFrom d Gs w) < _
    rw [strictN_eq]
    exact segFrom_lt d Gs w _ (mulW_eq d acc _ ▸ mulF_lt d _ _)

theorem notInL_spec {x : Nat} : ∀ {L : List Nat}, notInL x L = true → x ∉ L
  | [], _ => List.not_mem_nil
  | y :: L, h => by
    change andB (notB (Nat.beq x y)) (notInL x L) = true at h
    rw [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.mem_cons, not_or]
    refine ⟨fun e => ?_, notInL_spec h.2⟩
    rw [e, Nat.beq_refl] at h
    exact absurd h.1 (by simp)

theorem distinctL_spec : ∀ {L : List Nat}, distinctL L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: L, h => by
    change andB (notInL x L) (distinctL L) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    exact List.nodup_cons.2 ⟨notInL_spec h.1, distinctL_spec h.2⟩

theorem segsK_eq (d MA MAi MB MBi : Nat) : ∀ (segs : List (List (Nat × Bool))) (k : List Nat → Bool),
    segsK d MA MAi MB MBi segs k =
      k (segs.flatMap fun s => [wordP d MA MAi MB MBi s, wordP d MA MAi MB MBi (invW s)])
  | [], _ => rfl
  | s :: segs, k => by
    change strictB (wordP d MA MAi MB MBi s) (fun g => strictB (wordP d MA MAi MB MBi (invW s))
      fun gi => segsK d MA MAi MB MBi segs fun L => k (g :: gi :: L)) = _
    rw [strictB_eq, strictB_eq, segsK_eq d MA MAi MB MBi segs]
    rfl

theorem matsK_eq (d : Nat) (Gs : List Nat) (k : List Nat → Bool) :
    ∀ (ws : List (List (Nat × Bool))) (acc : List Nat),
      List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
        (fun w _ ih acc => strictB (segFrom d Gs w (idF d)) fun g => ih (g :: acc)) ws acc =
        k ((ws.map fun w => segFrom d Gs w (idF d)).reverse ++ acc)
  | [], _ => rfl
  | w :: ws, acc => by
    change strictB (segFrom d Gs w (idF d)) (fun g => List.rec (motive := fun _ => List Nat → Bool)
      (fun acc => k acc) (fun w _ ih acc => strictB (segFrom d Gs w (idF d)) fun g => ih (g :: acc))
      ws (g :: acc)) = _
    rw [strictB_eq, matsK_eq d Gs k ws]
    simp

theorem pairsP_spec {d MA MAi MB MBi : Nat} {Gs : List Nat} :
    ∀ ps : List (List (Nat × Bool) × List (Nat × Bool)), pairsP d MA MAi MB MBi Gs ps = true →
      ∀ q ∈ ps, wordFrom d MA MAi MB MBi q.2 (segFrom d Gs q.1 (idF d)) = idF d
  | [], _, _, hq => absurd hq List.not_mem_nil
  | (w, t) :: ps, h, q, hq => by
    change andB (Nat.beq (wordFrom d MA MAi MB MBi t (segFrom d Gs w (idF d))) (idF d))
      (pairsP d MA MAi MB MBi Gs ps) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with e | e
    · subst e
      exact Nat.eq_of_beq_eq_true h.1
    · exact pairsP_spec ps h.2 q e

variable {d MA MB eA eB : Nat} {G : Type*} [Group G] {φ : G →* GL (Fin d) (ZMod 2)}
  {σ : Fin 2 → G}

theorem grpK_sound (hφ : Function.Injective φ) (hA : MatP d MA = matOf φ (σ 0))
    (hB : MatP d MB = matOf φ (σ 1)) (segs : List (List (Fin 2 × Bool))) {k : Nat}
    (hk : k ≤ segs.length) (ps : List (List (Fin k × Bool) × List (Fin 2 × Bool)))
    (h : grpK d MA MB eA eB (segs.map natW) (ps.map fun q => (natW q.1, natW q.2)) = true) :
    ∀ q ∈ ps, signedProd (fun i : Fin k => segVal σ segs i.val) q.1 * signedProd σ q.2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := seedsK_spec h
  have hAi := MatP_inv_of hA h1
  have hBi := MatP_inv_of hB h2
  rw [segsK_eq] at h3
  intro q hq
  have hm := pairsP_spec _ h3 (natW q.1, natW q.2) (List.mem_map.2 ⟨q, hq, rfl⟩)
  have e := congrArg (MatP d) hm
  rw [MatP_wordFrom hA hAi hB hBi, MatP_segFrom hA hAi hB hBi hk, MatP_id, one_mul, ← matOf_mul]
    at e
  apply hφ
  rw [map_one]
  exact Units.ext e

theorem distK_sound (hA : MatP d MA = matOf φ (σ 0)) (hB : MatP d MB = matOf φ (σ 1))
    (segs : List (List (Fin 2 × Bool))) {k : Nat} (hk : k ≤ segs.length)
    (ws : List (List (Fin k × Bool)))
    (h : distK d MA MB eA eB (segs.map natW) (ws.map natW) = true) :
    ∀ i (hi : i < ws.length) j (hj : j < ws.length), i ≠ j →
      signedProd (fun l : Fin k => segVal σ segs l.val) ws[i] ≠
        signedProd (fun l : Fin k => segVal σ segs l.val) ws[j] := by
  obtain ⟨h1, h2, h3⟩ := seedsK_spec h
  have hAi := MatP_inv_of hA h1
  have hBi := MatP_inv_of hB h2
  rw [segsK_eq] at h3
  unfold matsK at h3
  rw [matsK_eq, List.append_nil] at h3
  have hnd := List.nodup_reverse.1 (distinctL_spec h3)
  intro i hi j hj hij e
  set Gs := (segs.map natW).flatMap fun s =>
    [wordP d MA (powK d MA (Nat.pred eA)) MB (powK d MB (Nat.pred eB)) s,
     wordP d MA (powK d MA (Nat.pred eA)) MB (powK d MB (Nat.pred eB)) (invW s)] with hGs
  have em : MatP d (segFrom d Gs (natW ws[i]) (idF d)) = MatP d (segFrom d Gs (natW ws[j]) (idF d)) := by
    rw [MatP_segFrom hA hAi hB hBi hk, MatP_segFrom hA hAi hB hBi hk, e]
  have en := MatP_inj em (segFrom_lt d Gs _ _ (idF_lt d)) (segFrom_lt d Gs _ _ (idF_lt d))
  have hi' : i < ((ws.map natW).map fun w => segFrom d Gs w (idF d)).length := by simpa using hi
  have hj' : j < ((ws.map natW).map fun w => segFrom d Gs w (idF d)).length := by simpa using hj
  refine hij ((List.Nodup.getElem_inj_iff hnd (hi := hi') (hj := hj')).1 ?_)
  simpa using en

theorem prod_pairLetter {G : Type*} [Group G] (x y : G) : ∀ u : List Int,
    (u.map fun z => if z = 1 then x else if z = -1 then x⁻¹ else if z = 2 then y else y⁻¹).prod =
      signedProd ![x, y] (u.map pairLetter)
  | [] => rfl
  | z :: u => by
    rw [List.map_cons, List.prod_cons, List.map_cons, signedProd_cons, prod_pairLetter x y u]
    congr 1
    by_cases h1 : z = 1
    · simp [pairLetter, h1]
    by_cases h2 : z = -1
    · simp [pairLetter, h2]
    by_cases h3 : z = 2
    · simp [pairLetter, h3]
    · simp [pairLetter, h1, h2, h3]

end CFSG.KC.TabMatGrp

end
