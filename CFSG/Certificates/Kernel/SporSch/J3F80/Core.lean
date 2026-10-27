module

public import CFSG.Certificates.Kernel.SporSch.J3F80.Tri
public import CFSG.Certificates.Kernel.SporSch.InvRowsF2Sound
public import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
import CFSG.Sporadic.Schreier.J4SCols

public section

namespace CFSG.KS.SporSch.J3F.CorePf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS CFSG.KS.SporSch CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.Schreier.PairJ3
open CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.J3F.Pad CFSG.KS.SporSch.J3F.Tri

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem strictB_c (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_c {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem img_sound (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X)
    {z w : Nat}
    (h : imgK c rm t0 t1 t2 t3 t4 t5 t6 usK dgK (enc80 X) (trJ t0 t1 t2 t3 t4 t5 t6 (enc80 X)) z =
      w) :
    canonRows 80 (mulRows 80 (transposeRows 80 X) (mulRows 80 (triRowsZ 80 z) X)) =
      triRowsZ 80 w := by
  have m1 := mul80 hK (wf_tri z) hX
  have t := tr80 hK hX
  have m2 := mul80 hK t.1 m1.1
  have cn := canonK_eq hK m2.1
  unfold imgK at h
  rw [triK_eq, m1.2, t.2, m2.2, cn.2, packTriK_eq hK cn.1] at h
  rw [← h, tri_pack cn.1 (fun i hi j hj => canon_upper _ hi hj)]

theorem pull_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {L : List Nat} {z : Nat}
    (hL : rows80K L = true) (_hz : z < 2 ^ 3240)
    (h : Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 usK dgK (packRowsK L)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L)) z) z = true) :
    pullOKZ 80 L.toArray z z = true := by
  obtain ⟨hW, hp⟩ := rows80K_sound hL
  rw [hp] at h
  unfold pullOKZ
  rw [img_sound hK hW (Nat.eq_of_beq_eq_true h)]
  exact beq_self_eq_true _

private theorem unpack_get {n w P r : Nat} (hr : r < n) : (unpack n w P)[r]! = pg w (mask w) P r := by
  unfold unpack
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

theorem forms_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {bytes : ByteArray}
    {S : Array (Array Nat)} {L1 L2 : List Nat} {F : Nat → Nat} {S0 S1 : Nat}
    (hF : ∀ r < 6156, hexAt bytes (810 * r) 810 = F r)
    (hS0 : S[0]! = unpack 6156 13 S0) (hS1 : S[1]! = unpack 6156 13 S1)
    (hL1 : rows80K L1 = true) (hL2 : rows80K L2 = true)
    (h : ∀ r < 6156, formsF c rm t0 t1 t2 t3 t4 t5 t6 usK dgK F S0 S1 (packRowsK L1)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L1)) (packRowsK L2)
      (trJ t0 t1 t2 t3 t4 t5 t6 (packRowsK L2)) r = true) :
    formsCheckWith bytes S L1.toArray L2.toArray = true := by
  obtain ⟨hW1, hp1⟩ := rows80K_sound hL1
  obtain ⟨hW2, hp2⟩ := rows80K_sound hL2
  have htri : ∀ s < 6156, (Array.ofFn (n := 6156) fun r : Fin 6156 =>
      triRowsZ 80 (hexAt bytes (810 * r.val) 810))[s]! = triRowsZ 80 (F s) := by
    intro s hs
    rw [getElem!_pos _ s (by simpa using hs), Array.getElem_ofFn, hF s hs]
  unfold formsCheckWith
  dsimp only
  apply PF2.parLt_of_forall
  intro r hr
  have hr' := h r hr
  unfold formsF at hr'
  rw [hp1, hp2, strictB_c] at hr'
  obtain ⟨hw, hr'⟩ := bAnd_c hr'
  rw [strictB_c] at hr'
  obtain ⟨hs0, hr'⟩ := bAnd_c hr'
  obtain ⟨hi0, hr'⟩ := bAnd_c hr'
  rw [strictB_c] at hr'
  obtain ⟨hs1, hi1⟩ := bAnd_c hr'
  have hs0' : pg 13 (mask 13) S0 r < 6156 := Nat.blt_eq.mp hs0
  have hs1' : pg 13 (mask 13) S1 r < 6156 := Nat.blt_eq.mp hs1
  have hw' : F r < 2 ^ 3240 := by
    have := Nat.blt_eq.mp hw
    rwa [Nat.shiftLeft_eq', Nat.one_shiftLeft] at this
  rw [hS0, hS1, unpack_get hr, unpack_get hr, htri r hr, htri _ hs0', htri _ hs1']
  unfold pullOKRows
  rw [img_sound hK hW1 (Nat.eq_of_beq_eq_true hi0), img_sound hK hW2 (Nat.eq_of_beq_eq_true hi1),
    pack_tri hw', hF r hr]
  simp

theorem leftInv_of_mulJ (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {RB : Nat} {P : Array Nat}
    (hP : Wf80 P) (h : mulJ c rm RB (enc80 P) = dgK) :
    mulRows 80 (Array.ofFn (n := 80) fun r => row80 RB r.val) P = idRows 80 := by
  rw [mulJ_enc80 hK RB hP, id80.2, enc80] at h
  have hlt : ∀ v, vecMulN 80 P v < 2 ^ 112 := fun v =>
    lt_of_lt_of_le (CFSG.Sporadic.J4Schreier.vecMulN_lt hP.2 v)
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hW1 : CFSG.KS.SporSch.J4B.WfN
      (Array.ofFn (n := 112) fun r => vecMulN 80 P (row80 RB r.val)) := by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    exact hlt _
  have e := CFSG.KS.SporSch.J4B.enc_inj hW1 (wf_pad id80.1) h
  apply Array.ext
  · simp [mulRows, idRows]
  · intro i h1 h2
    have hi : i < 80 := by simpa [mulRows] using h1
    have := congrArg (fun A : Array Nat => A[i]?.getD 0) e
    simp only [pad112, Array.getElem?_ofFn, (by omega : i < 112), ↓reduceDIte,
      Option.getD_some] at this
    rw [Array.getElem?_eq_getElem (by simpa using h2), Option.getD_some] at this
    simpa [mulRows, hi] using this

theorem binv_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {z RB : Nat}
    (_hz : z < 2 ^ 3240)
    (h : Nat.beq (mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) dgK = true) :
    mulRows 80 (invRowsF2 80 (polarRowsZ 80 z)) (polarRowsZ 80 z) = idRows 80 := by
  have pk := polarK_eq hK z
  rw [pk.2] at h
  exact InvF2.invRowsF2_mul_of_mul pk.1.1 pk.1.2 (leftInv_of_mulJ hK pk.1 (Nat.eq_of_beq_eq_true h))

end CFSG.KS.SporSch.J3F.CorePf

end
