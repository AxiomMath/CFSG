module

public import Certificates.Data.Kernel.J4Gen589301.Run
public import CFSG.Certificates.Kernel.J4Row.Sound
public import CFSG.Quasithin.Vol2.KGFactJ4M4GenElts
import all CFSG.Certificates.Kernel.J4Q.Rep

public section

namespace CFSG.KC.J4Gen

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.KC.J4Q CFSG.KC.J4NPV
  CFSG.KC.Loop CFSG.Quasithin.KGC31.J4M4.Gen

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem parseSlp_ofList (L : List Char) : parseSlp (String.ofList L) = parseL L := by
  unfold parseSlp parseL
  rw [String.toList_ofList]

theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_eq d l i

theorem rdK_eq (one : Nat) (mem : List Nat) (n i : Nat) :
    rdK one mem n i = if i < n then mem.getD (n - 1 - i) one else one := by
  unfold rdK
  rw [getN_eq]
  by_cases h : i < n
  · have hb : Nat.blt i n = true := Nat.blt_eq.mpr h
    rw [hb, if_pos h]
    rfl
  · have hb : Nat.blt i n = false := by
      cases e : Nat.blt i n
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hb, if_neg h]

@[expose] def MemRel (one : Nat) (mem : List Nat) (n : Nat) (memG : List J) : Prop :=
  n = memG.length ∧ ∀ i, VjRep (rdK one mem n i) (memG.getD i 1)

theorem memRel_nil (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : MemRel one [] 0 [] :=
  ⟨rfl, fun i => by
    rw [rdK_eq, if_neg (Nat.not_lt_zero i), List.getD_nil]
    exact vjRep_one hK⟩

theorem memRel_push {mem : List Nat} {n : Nat} {memG : List J} (hm : MemRel one mem n memG)
    {v : Nat} {x : J} (hv : VjRep v x) : MemRel one (v :: mem) (Nat.succ n) (memG ++ [x]) := by
  obtain ⟨hn, hr⟩ := hm
  refine ⟨by simp [hn], fun i => ?_⟩
  rw [getD_append_singleton]
  rcases lt_trichotomy i n with h | h | h
  · have e : rdK one (v :: mem) (Nat.succ n) i = rdK one mem n i := by
      rw [rdK_eq, rdK_eq, if_pos (by omega), if_pos h]
      have e2 : Nat.succ n - 1 - i = (n - 1 - i) + 1 := by omega
      rw [e2, List.getD_cons_succ]
    rw [e, if_neg (by omega)]
    exact hr i
  · subst h
    rw [rdK_eq, if_pos (by omega), if_pos hn]
    have e2 : Nat.succ i - 1 - i = 0 := by omega
    rw [e2, List.getD_cons_zero]
    exact hv
  · have e : rdK one (v :: mem) (Nat.succ n) i = rdK one mem n i := by
      rw [rdK_eq, rdK_eq, if_neg (by omega), if_neg (by omega)]
    rw [e, if_neg (by omega)]
    exact hr i

theorem runK_gen (inp : List Nat) (fin : List Nat → Nat → Bool) (k : Nat) (ls : List Line)
    (mem : List Nat) (n : Nat) (invs : List Nat) :
    runK c rm one pad inp fin (.gen k :: ls) mem n invs =
      strictB (getN one inp k) fun v => runK c rm one pad inp fin ls (v :: mem) (Nat.succ n) invs :=
  rfl

theorem runK_mul (inp : List Nat) (fin : List Nat → Nat → Bool) (i j : Nat) (ls : List Line)
    (mem : List Nat) (n : Nat) (invs : List Nat) :
    runK c rm one pad inp fin (.mul i j :: ls) mem n invs =
      strictB (rdK one mem n i) fun x => strictB (rdK one mem n j) fun y =>
        strictB (mulJ c rm x y) fun v => runK c rm one pad inp fin ls (v :: mem) (Nat.succ n) invs :=
  rfl

theorem runK_inv (inp : List Nat) (fin : List Nat → Nat → Bool) (i : Nat) (ls : List Line)
    (mem : List Nat) (n : Nat) (invs : List Nat) :
    runK c rm one pad inp fin (.inv i :: ls) mem n invs =
      strictB (rdK one mem n i) fun x =>
        List.rec (motive := fun _ => Bool) false
          (fun h hs _ => CFSG.KC.J4Q.andB (canonJ pad h) (CFSG.KC.J4Q.andB (Nat.beq (mulJ c rm x h) one)
            (runK c rm one pad inp fin ls (h :: mem) (Nat.succ n) hs))) invs :=
  rfl

theorem runK_pow (inp : List Nat) (fin : List Nat → Nat → Bool) (i e : Nat) (ls : List Line)
    (mem : List Nat) (n : Nat) (invs : List Nat) :
    runK c rm one pad inp fin (.pow i e :: ls) mem n invs =
      strictB (rdK one mem n i) fun x =>
        strictB (powJ c rm one x e) fun v => runK c rm one pad inp fin ls (v :: mem) (Nat.succ n) invs :=
  rfl

theorem runK_sound (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {inp : List Nat} {inpG : ℕ → J}
    (hin : ∀ k, VjRep (getN one inp k) (inpG k)) {fin : List Nat → Nat → Bool} :
    ∀ (prog : List Line) (mem : List Nat) (n : Nat) (memG : List J) (invs : List Nat),
      MemRel one mem n memG → runK c rm one pad inp fin prog mem n invs = true →
        ∃ mem' n', MemRel one mem' n' (evalSlp inpG prog memG) ∧ fin mem' n' = true
  | [], mem, n, _, _, hm, h => ⟨mem, n, hm, h⟩
  | l :: ls, mem, n, memG, invs, hm, h => by
    have hr := hm.2
    cases l with
    | gen k =>
      rw [runK_gen, vj_strictB_eq] at h
      exact runK_sound hK hin ls _ _ _ invs (memRel_push hm (hin k)) h
    | mul i j =>
      rw [runK_mul, vj_strictB_eq, vj_strictB_eq, vj_strictB_eq] at h
      exact runK_sound hK hin ls _ _ _ invs (memRel_push hm (vjRep_mul hK (hr i) (hr j))) h
    | inv i =>
      rw [runK_inv, vj_strictB_eq] at h
      cases invs with
      | nil => exact absurd h Bool.false_ne_true
      | cons g gs =>
        obtain ⟨hc, h⟩ := vj_andB_iff.1 h
        obtain ⟨hb, h⟩ := vj_andB_iff.1 h
        exact runK_sound hK hin ls _ _ _ gs
          (memRel_push hm (vjRep_inv hK (hr i) hc (Nat.eq_of_beq_eq_true hb))) h
    | pow i e =>
      rw [runK_pow, vj_strictB_eq, vj_strictB_eq] at h
      exact runK_sound hK hin ls _ _ _ invs
        (memRel_push hm (CFSG.KC.J4Row.vjRep_powJ hK (hr i) e)) h

theorem runK_out (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {inp : List Nat} {inpG : ℕ → J}
    (hin : ∀ k, VjRep (getN one inp k) (inpG k)) {prog : List Line} {invs : List Nat} {o M : Nat}
    (h : runK c rm one pad inp (fun mem n => Nat.beq (rdK one mem n o) M) prog [] 0 invs = true) :
    VjRep M ((evalSlp inpG prog []).getD o 1) := by
  obtain ⟨mem, n, hm, hf⟩ := runK_sound hK hin prog [] 0 [] invs (memRel_nil hK) h
  rw [← Nat.eq_of_beq_eq_true hf]
  exact hm.2 o

theorem runK_out2 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {inp : List Nat} {inpG : ℕ → J}
    (hin : ∀ k, VjRep (getN one inp k) (inpG k)) {prog : List Line} {invs : List Nat}
    {o₁ o₂ M₁ M₂ : Nat}
    (h : runK c rm one pad inp
      (fun mem n => CFSG.KC.J4Q.andB (Nat.beq (rdK one mem n o₁) M₁) (Nat.beq (rdK one mem n o₂) M₂))
      prog [] 0 invs = true) :
    VjRep M₁ ((evalSlp inpG prog []).getD o₁ 1) ∧ VjRep M₂ ((evalSlp inpG prog []).getD o₂ 1) := by
  obtain ⟨mem, n, hm, hf⟩ := runK_sound hK hin prog [] 0 [] invs (memRel_nil hK) h
  obtain ⟨h1, h2⟩ := vj_andB_iff.1 hf
  rw [← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2]
  exact ⟨hm.2 o₁, hm.2 o₂⟩

theorem rowJ_lt112 (n k : Nat) : rowJ (2 ^ 112 - 1) n k < 2 ^ 112 :=
  Nat.and_lt_two_pow _ (by omega : 2 ^ 112 - 1 < 2 ^ 112)

theorem wfA_decN (n : Nat) : WfA (decN n) := by
  refine ⟨by simp [decN], Array.all_eq_true.mpr fun i hi => ?_⟩
  simp only [decN, Array.getElem_ofFn]
  exact wf_of_bits fun k hk => by
    rw [ofN_eq (rowJ_lt112 _ _)]
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (rowJ_lt112 _ _) (Nat.pow_le_pow_right (by omega) hk))

@[expose] noncomputable def matN (G : Nat) : Matrix (Fin 112) (Fin 112) (ZMod 2) := rowsMatrix (decN G)

theorem enc_decN (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {G : Nat} (hG : canonJ pad G = true) :
    encR (decN G) = G :=
  encR_decN (consts_pad hK) hG

theorem rows_mul_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y X' Y' : Array V2}
    (hX : WfA X) (hY : WfA Y) (hX' : WfA X') (hY' : WfA Y')
    (h : mulJ c rm (encR X) (encR Y) = mulJ c rm (encR X') (encR Y')) :
    rowsMatrix X * rowsMatrix Y = rowsMatrix X' * rowsMatrix Y' := by
  rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
  apply rowsMatrix_eq_of_eqRows
  rw [eqRows_eq (wf_mulRows hX hY) (wf_mulRows hX' hY'), enc_mulRows hK hX hY, enc_mulRows hK hX' hY', h]
  exact Nat.beq_refl _

theorem matN_mul_inv (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {G GI : Nat}
    (hG : canonJ pad G = true) (hGI : canonJ pad GI = true) (h : mulJ c rm G GI = one) :
    matN G * matN GI = 1 := by
  rw [matN, matN, ← rowsMatrix_mulRows, ← rowsMatrix_idRows]
  apply rowsMatrix_eq_of_eqRows
  rw [eqRows_eq (wf_mulRows (wfA_decN G) (wfA_decN GI)) wf_idRows,
    enc_mulRows hK (wfA_decN G) (wfA_decN GI), enc_decN hK hG, enc_decN hK hGI, h, enc_idRows hK]
  exact Nat.beq_refl _

theorem Mx_mul_matN (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {MX MY G : Nat} {x y : J}
    (hx : VjRep MX x) (hy : VjRep MY y) (hG : canonJ pad G = true)
    (h : mulJ c rm MX G = mulJ c rm G MY) : Mx x * matN G = matN G * Mx y := by
  obtain ⟨X, hX, eX, mX⟩ := hx
  obtain ⟨Y, hY, eY, mY⟩ := hy
  rw [← mX, ← mY]
  exact rows_mul_eq hK hX (wfA_decN G) (wfA_decN G) hY (by rw [eX, eY, enc_decN hK hG]; exact h)

theorem gl_conj {x y : J} {M Mi : Matrix (Fin 112) (Fin 112) (ZMod 2)} (h₁ : M * Mi = 1)
    (h₂ : Mi * M = 1) (h : Mx x * M = M * Mx y) :
    (x : GL (Fin 112) (ZMod 2)) * ⟨M, Mi, h₁, h₂⟩ = ⟨M, Mi, h₁, h₂⟩ * (y : GL (Fin 112) (ZMod 2)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact h

theorem factsK_sound (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {Z C U F AP BP MA MB G GI : Nat} {z γ u f a' b' x y : J}
    (hz : VjRep Z z) (hc : VjRep C γ) (hu : VjRep U u) (hf : VjRep F f) (hap : VjRep AP a')
    (hbp : VjRep BP b') (ha : VjRep MA x) (hb : VjRep MB y)
    (h : factsK c rm one pad Z C U F AP BP MA MB G GI = true) :
    z * z = 1 ∧ γ ^ 11 = 1 ∧ γ * z = z * γ ∧ u * z * u⁻¹ = f ∧
      ∃ gM : GL (Fin 112) (ZMod 2), (a' : GL (Fin 112) (ZMod 2)) * gM = gM * x ∧
        (b' : GL (Fin 112) (ZMod 2)) * gM = gM * y := by
  unfold factsK at h
  obtain ⟨h1, h⟩ := vj_andB_iff.1 h
  obtain ⟨h2, h⟩ := vj_andB_iff.1 h
  obtain ⟨h3, h⟩ := vj_andB_iff.1 h
  obtain ⟨h4, h⟩ := vj_andB_iff.1 h
  obtain ⟨h5, h⟩ := vj_andB_iff.1 h
  obtain ⟨h6, h⟩ := vj_andB_iff.1 h
  obtain ⟨hg, h⟩ := vj_andB_iff.1 h
  obtain ⟨hgi, h⟩ := vj_andB_iff.1 h
  obtain ⟨h7, h8⟩ := vj_andB_iff.1 h
  have hinv := matN_mul_inv hK hg hgi (Nat.eq_of_beq_eq_true h7)
  have hinv' := matN_mul_inv hK hgi hg (Nat.eq_of_beq_eq_true h8)
  refine ⟨vjRep_eq_of_eq (vjRep_mul hK hz hz) (vjRep_one hK) (Nat.eq_of_beq_eq_true h1),
    vjRep_eq_of_eq (CFSG.KC.J4Row.vjRep_powJ hK hc 11) (vjRep_one hK) (Nat.eq_of_beq_eq_true h2),
    vjRep_eq_of_eq (vjRep_mul hK hc hz) (vjRep_mul hK hz hc) (Nat.eq_of_beq_eq_true h3), ?_,
    ⟨⟨matN G, matN GI, hinv, hinv'⟩, gl_conj hinv hinv' (Mx_mul_matN hK hap ha hg (Nat.eq_of_beq_eq_true h5)),
      gl_conj hinv hinv' (Mx_mul_matN hK hbp hb hg (Nat.eq_of_beq_eq_true h6))⟩⟩
  have e := vjRep_eq_of_eq (vjRep_mul hK hu hz) (vjRep_mul hK hf hu) (Nat.eq_of_beq_eq_true h4)
  rw [e, mul_inv_cancel_right]

end CFSG.KC.J4Gen

end
