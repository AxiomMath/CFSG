module

public import Certificates.Data.Kernel.B45Perm.TGen
public import CFSG.Certificates.Kernel.B45PermSound

public section

namespace CFSG.KC.B45P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.KC.LQT.TCK
  CFSG.KC.LQT.TCP CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n w : ℕ}

theorem size_pWord (gens : List PArr) : ∀ wd : List ℤ, (pWord n gens wd).1.size = n
  | [] => by simp [pWord, pId, idA]
  | _ :: _ => by simp [pWord, pMul, compA]

theorem arr_eq_of_rep {a b : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g) (hb : Rep n b g)
    (sa : a.size = n) (sb : b.size = n) : a = b := by
  refine Array.ext (sa.trans sb.symm) fun i h1 h2 => ?_
  have e := (ha.apply (sa ▸ h1)).trans (hb.apply (sa ▸ h1)).symm
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at e

theorem tGenK_sound {G GI : List ℕ} {T TI S : ℕ} {wd : List ℤ}
    (h : tGenK n w G GI T TI S wd = true) :
    (pWord n (unpackP n w G GI) wd).1 = unpack n w S ∧
      eqA n (pMul n (pWord n (unpackP n w G GI) wd) (unpack n w T, unpack n w TI)).1
        (pMul n (unpack n w T, unpack n w TI) (pWord n (unpackP n w G GI) wd)).1 = true := by
  unfold tGenK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hT, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨A, AI, hk, g, hr, hA, -⟩ := wordP_sound hn hnw hidn hl hz wd _ h
  obtain ⟨e1, e2⟩ := bAnd_true hk
  obtain ⟨t, ht, htA, -⟩ := prp_of_permOK hT
  have hS : RS n w S g := Nat.eq_of_beq_eq_true e1 ▸ hA
  refine ⟨arr_eq_of_rep hr.1 (Orb.rep_unpack hS.1) (size_pWord _ wd) (by simp [unpack]), ?_⟩
  have hc : g * t = t * g := eq_of_beq_rs e2 (rs_pcomp hn hnw hA htA) (rs_pcomp hn hnw htA hA)
  exact (eqA_iff (hr.mul ht).1 (ht.mul hr).1).2 hc

end CFSG.KC.B45P

end
