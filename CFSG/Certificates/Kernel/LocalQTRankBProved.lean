module

public import Certificates.Data.Kernel.LocalQT.RankB
public import CFSG.Certificates.Kernel.LocalQTEnumWProved
public import CFSG.Certificates.Kernel.LocalQTRankCheckProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.KC.LQT.RB.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem rowW_eq (w x k : Nat) : rowW w x k = (x >>> (64 * w * k)) &&& (2 ^ (64 * w) - 1) := by
  have e : Nat.shiftLeft 1 (64 * w) = 2 ^ (64 * w) := by
    change 1 <<< (64 * w) = 2 ^ (64 * w)
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [rowW]
  change (x >>> (64 * w * k)) &&& (Nat.shiftLeft 1 (64 * w) - 1) = _
  rw [e]

theorem imgW_rowW (W x r q : Nat) (hq : q < 64) : imgW W (rowW W x r) q = imgW W x (64 * r + q) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_imgW, testBit_imgW, rowW_eq, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < W
  · have hle : W * q ≤ W * 63 := Nat.mul_le_mul_left _ (by omega)
    have h1 : W * q + j < 64 * W := by omega
    have h2 : 64 * W * r + (W * q + j) = W * (64 * r + q) + j := by ring
    simp [hj, h1, h2]
  · simp [hj]

theorem fieldT_eq {W N R x : Nat} {T : Nat → Nat} (hR : N ≤ 64 * R)
    (hT : ∀ r < R, T r = rowW W x r) {i : Nat} (hi : i < N) : fieldT W T i = imgW W x i := by
  have e1 : Nat.shiftRight i 6 = i / 64 := by
    change i >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land i 63 = i % 64 := Nat.and_two_pow_sub_one_eq_mod i 6
  rw [fieldT, e1, e2, hT _ (by omega), imgW_rowW _ _ _ _ (Nat.mod_lt _ (by decide)),
    Nat.div_add_mod]

theorem rowsOK_spec {W N R x : Nat} {T : Nat → Nat} (h : rowsOK W N R x T = true) :
    N ≤ 64 * R ∧ ∀ r < R, T r = rowW W x r := by
  rw [rowsOK, andB_eq, Bool.and_eq_true] at h
  refine ⟨Nat.le_of_ble_eq_true h.1, fun r hr => ?_⟩
  have := allR_true h.2 r hr
  rw [Nat.zero_add] at this
  exact P.beq_iff.1 this

theorem allL_lt {W : Nat} {l : List Nat} (h : allL l (fun x => Nat.blt x (Nat.shiftLeft 1 W)) = true) :
    ∀ x ∈ l, x < 2 ^ W := by
  rw [allL_eq, List.all_eq_true] at h
  intro x hx
  have := h x hx
  rw [Nat.blt_eq] at this
  have e : Nat.shiftLeft 1 W = 2 ^ W := by
    change 1 <<< W = 2 ^ W
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rwa [e] at this

theorem field_code {W N R C : Nat} {T : Nat → Nat} {l : List Nat} (hrow : rowsOK W N R C T = true)
    (hC : C = codeK W l) (hl : ∀ x ∈ l, x < 2 ^ W) (hlen : N ≤ l.length) {i : Nat} (hi : i < N) :
    fieldT W T i = l.getD i 0 := by
  obtain ⟨h1, h2⟩ := rowsOK_spec hrow
  rw [fieldT_eq h1 h2 hi, hC, imgW_codeK l hl i (by omega)]

end CFSG.KC.LQT.RB.Pf

end

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem rankB_sound_proved {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (d k fuel dd zi K L PK CK RP RC : Nat) (PT CT : Nat → Nat)
    (h : rankBH n w W B ta tb prog qp k fuel dd zi K L PK CK RP RC PT CT = true)
    (hp : ∀ j < K, rankBP W qp.length (2 ^ k) PT CT d zi (j * L) L = true) :
    RankCert.RankCertS n B (slpTabsA ta.toArray tb.toArray prog) qp (d + 1)
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  rw [rankBH, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpW_rep hw hta htb hso
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpW n w (codeK w ta) (codeK w tb) prog = R at hlen hrep hR
  dsimp only at hR
  rw [andB_eq, Bool.and_eq_true] at hR
  obtain ⟨hqp, hBE⟩ := hR
  rw [rankBE] at hBE
  dsimp only at hBE
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hBE
  obtain ⟨hE, hpar, hcl, hPK, hCK, hRP, hRC, hzi, hz0, hzz, hcen, hcov⟩ := hBE
  generalize hEd : enumW w (lenA B) (lenA qp) (imgsW w) (fstN R qp) (ptsW w B (fstN R qp)) dd = E
    at hE hpar hcl hPK hCK hRP hRC hzi hz0 hzz hcen hcov
  obtain ⟨hq1, hinv, hbe, hsz, hcnt, hpl, hparE, hcll, hclE⟩ :=
    enumW_bfs hw hlen hrep hqp _ rfl E hEd hE
  generalize bfsEnumB n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) fuel = X
    at hbe hsz hcnt hpl hparE hcll hclE ⊢
  refine ⟨hq1, hinv, hbe, hsz, ?_⟩
  rw [lenA_eq] at hRC hzz hcen hcov
  rw [hcnt] at hRP hRC hzi hzz hcen hcov
  rw [← hsz] at hp
  have hPK' : PK = codeK W E.1.par.reverse := by
    rw [P.beq_iff, revOn_eq, List.append_nil] at hPK
    exact hPK
  have hCK' : CK = codeK W E.1.cl.reverse := by
    rw [P.beq_iff, revOn_eq, List.append_nil] at hCK
    exact hCK
  have hparlt : ∀ x ∈ E.1.par.reverse, x < 2 ^ W := fun x hx =>
    allL_lt hpar x (List.mem_reverse.1 hx)
  have hcllt : ∀ x ∈ E.1.cl.reverse, x < 2 ^ W := fun x hx =>
    allL_lt hcl x (List.mem_reverse.1 hx)
  have hfP : ∀ i < X.1.size, fieldT W PT i = X.2.1[i]! := by
    intro i hi
    rw [field_code hRP hPK' hparlt (by rw [List.length_reverse, hpl]) hi, hparE i hi]
  have hfC : ∀ i < X.1.size, ∀ j < qp.length,
      fieldT W CT (i * (qp.length + qp.length) + j) = X.2.2[i * (qp.length + qp.length) + j]! := by
    intro i hi j hj
    have hRC' : rowsOK W (X.1.size * (qp.length + qp.length)) RC CK CT = true := hRC
    rw [field_code hRC' hCK' hcllt (by rw [List.length_reverse, hcll]) (pos_lt hi (by omega)),
      hclE i hi j hj]
  obtain ⟨-, -, -, hparB, -, hstep, -⟩ := hbe
  have hGl : (qp.map fun p => T[p.1]!).length = qp.length := List.length_map _
  have hGil : (qp.map fun p => T[p.2]!).length = qp.length := List.length_map _
  rw [hGl, hGil] at hstep
  have hmul := mulG_spec (N := X.1.size) (g := qp.length) (gi := qp.length) hfP hfC
    (fun i hi hi0 => by
      obtain ⟨h1, s, hs, -⟩ := hparB i hi hi0
      refine ⟨h1, ?_⟩
      rcases qp with _ | ⟨q, qp⟩
      · simp at hs
      · simp)
    (fun i hi j hj => (hstep i hi j hj).1) X.1.size
  unfold invsB at hcov
  unfold rankBP invsB at hp
  dsimp only at hp
  have hmT : ∀ i k, mulT W qp.length X.1.size PT CT i k =
      mulG (fieldT W PT) (fieldT W CT) qp.length (qp.length + qp.length) X.1.size i k :=
    fun _ _ => rfl
  apply rankCheck_of_parts (zi := zi) (K := K) (L := L) (g := qp.length) (gi := qp.length)
    (par := X.2.1) (cl := X.2.2) (mul := mulT W qp.length X.1.size PT CT)
    (fun i hi k hk => by rw [hmT, (hmul i k hi hk).1]; exact ⟨rfl, (hmul i k hi hk).2⟩)
  · exact P.blt_iff.1 hzi
  · rw [notB_eq, Bool.not_eq_true', ← Bool.not_eq_true] at hz0
    exact fun e => hz0 (P.beq_iff.2 e)
  · exact P.beq_iff.1 hzz
  · intro i hi
    have := allR_true hcen i hi
    rw [Nat.zero_add] at this
    exact P.beq_iff.1 this
  · rw [lenA_eq] at hcov
    exact Nat.le_of_ble_eq_true hcov
  · exact hp

end CFSG.KC.LQT.RB

end
