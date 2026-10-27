module

public import Certificates.Data.Kernel.B45Perm.Defs
public import CFSG.Certificates.Kernel.LocalQTTcPSound
public import CFSG.Certificates.Kernel.LocalQTTcPProved
public import CFSG.Quasithin.Background.SmithB45ExcHSRuWit
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KC.B45P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.KC.LQT.TCK
  CFSG.KC.LQT.TCP CFSG.KC.PkPow CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab
open scoped commutatorElement

variable {n w : ℕ}

theorem eqA_false {a b : Array ℕ} {g h : Equiv.Perm (Fin n)} (ha : Rep n a g) (hb : Rep n b h)
    (hne : g ≠ h) : eqA n a b = false := by
  cases e : eqA n a b
  · rfl
  · exact absurd ((eqA_iff ha hb).1 e) hne

theorem orderCheck_of {p : ℕ} {x : PArr} {g : Equiv.Perm (Fin n)} (hx : PRep n x g)
    (h1 : g ^ p = 1) (h2 : g ≠ 1) : orderCheck n p x = true := by
  unfold orderCheck
  rw [(eqA_iff (pRep_pow hx p).1 rep_idA).2 h1, eqA_false hx.1 rep_idA h2]
  rfl

theorem cfgCheck_of {p : ℕ} {z x y : PArr} {c g h : Equiv.Perm (Fin n)} (hz : PRep n z c)
    (hx : PRep n x g) (hy : PRep n y h) (hc : c = ⁅g, h⁆) (hp : g ^ p = 1) (h3 : c * g = g * c)
    (h4 : c * h = h * c) (h5 : c ≠ 1) : cfgCheck n p z x y = true := by
  unfold cfgCheck
  rw [(eqA_iff hz.1 (pRep_comm hx hy).1).2 hc, (eqA_iff (pRep_pow hx p).1 rep_idA).2 hp,
    (eqA_iff (hz.mul hx).1 (hx.mul hz).1).2 h3, (eqA_iff (hz.mul hy).1 (hy.mul hz).1).2 h4,
    eqA_false hz.1 rep_idA h5]
  rfl

theorem eq_of_beq_rs {A B : ℕ} {g h : Equiv.Perm (Fin n)} (e : Nat.beq A B = true)
    (hA : RS n w A g) (hB : RS n w B h) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hA
  exact rp_unique hA.1 hB.1

theorem ne_of_bIf {A idn : ℕ} {g : Equiv.Perm (Fin n)}
    (e : bIf(Nat.beq A idn, false, true) = true) (hA : RS n w A g) (hid : RS n w idn 1) :
    g ≠ 1 := by
  intro h1
  rw [h1] at hA
  have := eq_of_rs hA hid
  rw [this, Nat.beq_refl] at e
  exact Bool.false_ne_true e

theorem rs_ppw (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) (hid : RS n w (pidn n w) 1) {X : ℕ}
    {g : Equiv.Perm (Fin n)} (hX : RS n w X g) : ∀ e, RS n w (ppw n w X e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact hid
  | e + 1 => by
    have r : ppw n w X (e + 1) = strictN (ppw n w X e) (fun q => pcomp n w (mask w) X q) := rfl
    rw [r, sN, pow_succ']
    exact rs_pcomp hn hnw hX (rs_ppw hn hnw hid hX e)

theorem ordK_sound (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) (hid : RS n w (pidn n w) 1) {p idn X : ℕ}
    {g : Equiv.Perm (Fin n)} (hidn : RS n w idn 1) (hX : RS n w X g)
    (h : ordK n w p idn X = true) : g ^ p = 1 ∧ g ≠ 1 := by
  unfold ordK at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  exact ⟨eq_of_beq_rs h1 (rs_ppw hn hnw hid hX p) hidn, ne_of_bIf h2 hX hidn⟩

theorem invProdP_sound (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hidn : RS n w idn 1)
    {G GI : List ℕ} (hl : G.length = GI.length)
    (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true) {t : PArr} {T TI : ℕ}
    (hT : PrP n w t T TI) (wd : List ℤ) (k : ℕ → ℕ → Bool)
    (h : invProdP n w idn G GI T TI wd k = true) :
    ∃ Z ZI, k Z ZI = true ∧ PrP n w (pMul n t (pConj n (pWord n (unpackP n w G GI) wd) t)) Z ZI := by
  unfold invProdP at h
  obtain ⟨g, gi, h1, hg⟩ := wordP_sound hn hnw hidn hl hz wd _ h
  rw [sB, sB, sB, sB] at h1
  exact ⟨_, _, h1, hT.mul hn hnw (prp_conj hn hnw hg hT)⟩

theorem b45OrdK_sound {p : ℕ} {G GI : List ℕ} {T TI : ℕ} {wd : List ℤ}
    (h : b45OrdK n w p G GI T TI wd = true) :
    orderCheck n p (pMul n (unpack n w T, unpack n w TI)
      (pConj n (pWord n (unpackP n w G GI) wd) (unpack n w T, unpack n w TI))) = true := by
  unfold b45OrdK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hT, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  rw [sB] at h
  obtain ⟨Z, ZI, hk, c, hc, hZ, -⟩ := invProdP_sound hn hnw hidn hl hz (prp_of_permOK hT) wd _ h
  obtain ⟨h1, h2⟩ := ordK_sound hn hnw hidn hidn hZ hk
  exact orderCheck_of hc h1 h2

theorem b45CfgK_sound {p : ℕ} {G GI : List ℕ} {T TI : ℕ} {wg wx wy : List ℤ}
    (h : b45CfgK n w p G GI T TI wg wx wy = true) :
    cfgCheck n p (pMul n (unpack n w T, unpack n w TI)
      (pConj n (pWord n (unpackP n w G GI) wg) (unpack n w T, unpack n w TI)))
      (pWord n (unpackP n w G GI) wx) (pWord n (unpackP n w G GI) wy) = true := by
  unfold b45CfgK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hT, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  rw [sB] at h
  obtain ⟨Z, ZI, h1, c, hc, hZ, -⟩ := invProdP_sound hn hnw hidn hl hz (prp_of_permOK hT) wg _ h
  obtain ⟨X, XI, h2, g, hgx, hX, hXI⟩ := wordP_sound hn hnw hidn hl hz wx _ h1
  obtain ⟨Y, YI, h3, k, hky, hY, hYI⟩ := wordP_sound hn hnw hidn hl hz wy _ h2
  unfold cfgK at h3
  obtain ⟨e1, h3⟩ := bAnd_true h3
  obtain ⟨e2, h3⟩ := bAnd_true h3
  obtain ⟨e3, h3⟩ := bAnd_true h3
  obtain ⟨e4, e5⟩ := bAnd_true h3
  have hcomm : RS n w (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) X Y) XI) YI)
      ⁅g, k⁆ := by
    rw [commutatorElement_def]
    exact rs_pcomp hn hnw (rs_pcomp hn hnw (rs_pcomp hn hnw hX hY) hXI) hYI
  exact cfgCheck_of hc hgx hky (eq_of_beq_rs e1 hZ hcomm)
    (eq_of_beq_rs e2 (rs_ppw hn hnw hidn hX p) hidn)
    (eq_of_beq_rs e3 (rs_pcomp hn hnw hZ hX) (rs_pcomp hn hnw hX hZ))
    (eq_of_beq_rs e4 (rs_pcomp hn hnw hZ hY) (rs_pcomp hn hnw hY hZ)) (ne_of_bIf e5 hZ hidn)

theorem foldr_fix (P : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < n) →
    l.foldr (fun x c => nIf(Nat.beq (pg w (mask w) P x) x, Nat.succ c, c)) 0 =
      l.countP fun i => (unpack n w P)[i]! == i
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.foldr_cons, List.countP_cons, foldr_fix P l fun i hi => hl i (List.mem_cons_of_mem _ hi),
      Orb.unpack_get (hl x List.mem_cons_self)]
    cases h : Nat.beq (pg w (mask w) P x) x
    · have h' := Nat.ne_of_beq_eq_false h
      simp [h']
    · have h' := Nat.eq_of_beq_eq_true h
      simp [h']

theorem nfix_eq (P : ℕ) : nfix n w P = fixCountA n (unpack n w P) := by
  unfold nfix fixCountA
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  exact foldr_fix P _ fun i hi => List.mem_range.1 hi

end CFSG.KC.B45P

end
