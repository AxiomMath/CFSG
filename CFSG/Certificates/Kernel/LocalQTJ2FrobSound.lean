module

public import Certificates.Data.Kernel.LocalQT.J2Frob
public import CFSG.Certificates.Kernel.LocalQTTcPSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.LocalQTTcPProved

public section

namespace CFSG.KC.LQT.TC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2.Native

@[expose] def frobOKG (n : ℕ) (gens : List PArr) (xw gw : List ℤ) : Bool :=
  let FX := pWord n gens xw
  let FG := pWord n gens gw
  let FY := pConj n FG FX
  eqA n (pMul n (pMul n FX FX) (pMul n (pMul n FX FX) FX)).1 (idA n) &&
    !eqA n FX.1 (idA n) &&
    eqA n (pMul n FX FY).1 (pMul n FY FX).1 &&
    eqA n (pConj n FG FY).1 (pInv (pMul n FX FY)).1

open CFSG.Monster.B.Co2

private theorem eqA_of_beq {n w : ℕ} {a b : Array ℕ} {P Q : ℕ} {g h : Equiv.Perm (Fin n)}
    (ha : Rep n a g) (hb : Rep n b h) (hP : CFSG.KC.LQT.TCK.RP n w P g)
    (hQ : CFSG.KC.LQT.TCK.RP n w Q h) (e : Nat.beq P Q = true) : eqA n a b = true := by
  rw [Nat.eq_of_beq_eq_true e] at hP
  exact (eqA_iff ha hb).2 (CFSG.KC.LQT.TCP.rp_unique hP hQ)

theorem frobK_sound {n w : ℕ} {G GI : List ℕ} {xw gw : List ℤ} (h : frobK n w G GI xw gw = true) :
    frobOKG n (unpackP n w G GI) xw gw = true := by
  unfold frobK at h
  obtain ⟨hid, h⟩ := CFSG.KC.LQT.TCK.bAnd_true h
  obtain ⟨hg, h⟩ := CFSG.KC.LQT.TCK.bAnd_true h
  obtain ⟨hn, hnw, -⟩ := CFSG.KC.LQT.TCP.idK_facts hid
  have hidn := CFSG.KC.LQT.TCP.rs_idn hid
  obtain ⟨hl, hz⟩ := CFSG.KC.LQT.TCK.gensTc_sound G GI hg
  obtain ⟨X, XI, h1, hX⟩ := CFSG.KC.LQT.TCP.wordP_sound hn hnw hidn hl hz xw _ h
  obtain ⟨Gx, GxI, h2, hGx⟩ := CFSG.KC.LQT.TCP.wordP_sound hn hnw hidn hl hz gw _ h1
  rw [CFSG.KC.LQT.TCK.sB, CFSG.KC.LQT.TCK.sB, CFSG.KC.LQT.TCK.sB] at h2
  obtain ⟨c1, h2⟩ := CFSG.KC.LQT.TCK.bAnd_true h2
  obtain ⟨c2, h2⟩ := CFSG.KC.LQT.TCK.bAnd_true h2
  obtain ⟨c3, c4⟩ := CFSG.KC.LQT.TCK.bAnd_true h2
  have hY := CFSG.KC.LQT.TCP.prp_conj hn hnw hGx hX
  have hXX := hX.mul hn hnw hX
  have hX5 := hXX.mul hn hnw (hXX.mul hn hnw hX)
  have hXY := hX.mul hn hnw hY
  have hYX := hY.mul hn hnw hX
  have hGY := (hGx.mul hn hnw hY).mul hn hnw hGx.inv
  simp only [frobOKG, unpackP, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨g, h1, h2, -⟩ := hX5
    exact eqA_of_beq h1.1 rep_idA h2.1 hidn.1 c1
  · by_contra hne
    have hne' := Bool.eq_true_of_not_eq_false hne
    obtain ⟨x, hxP, hxA, -⟩ := hX
    have hx1 : x = 1 := (eqA_iff hxP.1 rep_idA).1 hne'
    subst hx1
    have := CFSG.KC.LQT.TCP.eq_of_rs hxA hidn
    rw [this, Nat.beq_refl] at c2
    exact absurd c2 (by decide)
  · obtain ⟨g, h1, h2, -⟩ := hXY
    obtain ⟨g', h1', h2', -⟩ := hYX
    exact eqA_of_beq h1.1 h1'.1 h2.1 h2'.1 c3
  · obtain ⟨g, h1, h2, -⟩ := hGY
    obtain ⟨g', h1', -, h3'⟩ := hXY
    exact eqA_of_beq h1.1 h1'.inv.1 h2.1 h3'.1 c4

theorem count_eq {α : Type} (l : List α) :
    List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem pcK_spec {n w N : ℕ} {G GI : List ℕ} {E : ℕ → ℕ} {targets : List ℕ} :
    ∀ {data : List (ℕ × ℕ × List (List ℤ) × List (ℤ × ℤ))}, pcK n w N G GI E data targets = true →
    ∀ e ∈ data, e.2.2.1.length = 2 ∧ e.1 < N ∧ e.2.1 < N ∧
      mcP n w G GI [E e.1, E e.2.1] [E e.1, E e.2.1] e.2.2.1 e.2.2.2 targets = true
  | [], _, e, he => absurd he List.not_mem_nil
  | d :: data, h, e, he => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (pcK n w N G GI E data targets)
              (mcP n w G GI [E d.1, E d.2.1] [E d.1, E d.2.1] d.2.2.1 d.2.2.2 targets))
            (Nat.blt d.2.1 N)) (Nat.blt d.1 N))
        (Nat.beq (List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun _ _ ih2 => Nat.succ ih2) d.2.2.1)
          (nat_lit 2)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
    obtain ⟨h7, h8⟩ := (bAnd_iff _ _).1 h6
    rcases List.mem_cons.1 he with rfl | he
    · rw [count_eq] at h1
      rw [Nat.blt_eq] at h3 h5
      exact ⟨Nat.eq_of_beq_eq_true h1, h3, h5, h7⟩
    · exact pcK_spec h8 e he

end CFSG.KC.LQT.TC

end
