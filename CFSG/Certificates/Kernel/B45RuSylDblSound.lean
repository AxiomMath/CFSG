module

public import Certificates.Data.Kernel.B45Perm.RuSylDbl
public import CFSG.Certificates.Kernel.LocalQTTcPSound
public import CFSG.Certificates.Kernel.LocalQTTcPProved
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.B45P.RuSylD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCK CFSG.KC.LQT.TCP
  CFSG.KC.PkPow CFSG.KC.B45P.RuSyl CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem prep_ppw {Y : Nat} {y : Equiv.Perm (Fin 4060)} (hY : CFSG.KS.Raw.Orb.PRep 4060 12 Y y) :
    ∀ e, CFSG.KS.Raw.Orb.PRep 4060 12 (ppw 4060 12 Y e) (y ^ e)
  | 0 => by
    rw [pow_zero]
    exact CFSG.KS.Raw.Orb.prep_pidn (by norm_num) (by norm_num)
  | e + 1 => by
    have r : ppw 4060 12 Y (e + 1) =
        strictN (ppw 4060 12 Y e) (fun q => pcomp 4060 12 (mask 12) Y q) := rfl
    rw [r, sN, pow_succ']
    exact CFSG.KS.Raw.Orb.prep_pcomp (by norm_num) hY (prep_ppw hY e)

theorem dblC_sound {TR CD : Nat → Nat} {o0 o1 : Nat} {G GI : List Nat} {e : Nat → Nat}
    {wd : List Int} {X : Nat → Equiv.Perm (Fin 4060)} (hid : idK 4060 12 (mask 12) = true)
    (hg : gensTc 4060 12 G GI = true)
    (hx : ∀ i < 495, CFSG.KS.Raw.Orb.PRep 4060 12 (xP TR o0 o1 (CD i)) (X i))
    (h : dblC TR CD o0 o1 (pidn 4060 12) G GI e wd = true) :
    (∀ t < 4, e t < 495) ∧ ∃ g : Equiv.Perm (Fin 4060),
      CFSG.QuasithinUnique.Setup.X1.PRep 4060 (pWord 4060 (unpackP 4060 12 G GI) wd) g ∧
      (X (e 0) * (g * X (e 1) * g⁻¹) * X (e 2) * (g * X (e 3) * g⁻¹)) ^ 29 = 1 ∧
      X (e 0) * (g * X (e 1) * g⁻¹) * X (e 2) * (g * X (e 3) * g⁻¹) ≠ 1 := by
  unfold dblC at h
  obtain ⟨hlt, hw⟩ := bAnd_true h
  have hlt' : ∀ t < 4, e t < 495 := fun t ht => by
    have := allN_spec hlt t ht
    rwa [Nat.blt_eq] at this
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨A, AI, hk, g, hgr, hA, hAI⟩ := wordP_sound hn hnw hidn hl hz wd _ hw
  rw [sB] at hk
  obtain ⟨h29, hmv⟩ := bAnd_true hk
  have hX : ∀ t < 4, CFSG.KS.Raw.Orb.PRep 4060 12 (xP TR o0 o1 (CD (e t))) (X (e t)) :=
    fun t ht => hx _ (hlt' t ht)
  have hc : ∀ t < 4, CFSG.KS.Raw.Orb.PRep 4060 12 (cjP A AI (xP TR o0 o1 (CD (e t))))
      (g * X (e t) * g⁻¹) := fun t ht =>
    CFSG.KS.Raw.Orb.prep_pcomp (by norm_num)
      (CFSG.KS.Raw.Orb.prep_pcomp (by norm_num) hA.1 (hX t ht)) hAI.1
  have hY : CFSG.KS.Raw.Orb.PRep 4060 12 (yP TR CD o0 o1 e A AI)
      (X (e 0) * (g * X (e 1) * g⁻¹) * X (e 2) * (g * X (e 3) * g⁻¹)) :=
    CFSG.KS.Raw.Orb.prep_pcomp (by norm_num)
      (CFSG.KS.Raw.Orb.prep_pcomp (by norm_num)
        (CFSG.KS.Raw.Orb.prep_pcomp (by norm_num) (hX 0 (by norm_num)) (hc 1 (by norm_num)))
        (hX 2 (by norm_num))) (hc 3 (by norm_num))
  refine ⟨hlt', g, hgr, ?_, ?_⟩
  · have hp := prep_ppw hY 29
    rw [Nat.eq_of_beq_eq_true h29] at hp
    have h1 : CFSG.KS.Raw.Orb.PRep 4060 12 (pidn 4060 12) 1 :=
      CFSG.KS.Raw.Orb.prep_pidn (by norm_num) (by norm_num)
    exact Equiv.ext fun x => Fin.ext ((hp x).symm.trans (h1 x))
  · intro h1
    rw [h1] at hY
    have hall : allN 4060 (fun p => Nat.beq (pg 12 (mask 12) (yP TR CD o0 o1 e A AI) p) p) =
        true := CFSG.KS.PackFld.allN_of_forall fun p hp => by
      have := hY ⟨p, hp⟩
      rw [Equiv.Perm.one_apply] at this
      rw [this]
      exact Nat.beq_refl p
    rw [hall] at hmv
    exact Bool.false_ne_true hmv

end CFSG.KC.B45P.RuSylD

end
