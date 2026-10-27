module

public import Certificates.Data.Kernel.OpsLayKNorm
import CFSG.Certificates.Kernel.OpsLayKSnd

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

theorem secK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : SecData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : secK c A B D = true) : (ops3 d).secCheck D = true := by
  subst hd
  unfold secK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, houts, htReg, htests, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  have hT := hL.2 D.tReg (by rw [hlen]; exact htReg)
  have hxs := Snd.forall₂_map hL D.outs (fun r hr => by rw [hlen]; exact Snd.lt_of_all houts hr)
  have hsec := Snd.secOK_of hc hp hT hxs (fun k hk => Snd.lt_of_all htests hk) hrun
  unfold Ops.secCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨h2, hlt, houts, htReg, hsec⟩

theorem sqK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : SqData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : sqK c A B D = true) : (ops3 d).squareCheck D = true := by
  subst hd
  unfold sqK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, hrx, hry, hrh, hr0, hoh0, hexp, ht, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  simp only [Bool.and_eq_true, and_assoc] at hrun
  obtain ⟨hXr, hYr, hHo, hXY, hHX, hHY, hnorm⟩ := hrun
  have e : ∀ v ∈ [D.r, D.oh, D.a, D.b, D.c, D.d], v < 65536 :=
    fun v hv => Snd.lt_of_all hexp hv
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  have hX := hL.2 D.rx (by rw [hlen]; exact hrx)
  have hY := hL.2 D.ry (by rw [hlen]; exact hry)
  have hH := hL.2 D.rh (by rw [hlen]; exact hrh)
  unfold Ops.squareCheck Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨h2, hlt, hrx, hry, hrh, hr0, hoh0,
    Snd.eq_pow_one hc hp hX (e D.r (by simp)) hXr, Snd.eq_pow_one hc hp hY (e D.r (by simp)) hYr,
    Snd.eq_pow_one hc hp hH (e D.oh (by simp)) hHo,
    Snd.eq_of_rel (Snd.rel_mul hc hp hX hY) (Snd.rel_mul hc hp hY hX) hXY,
    Snd.conjOK_of hc hp hH hX (Snd.rel_mul hc hp (Snd.rel_pow hc hp hX (e D.a (by simp)))
      (Snd.rel_pow hc hp hY (e D.c (by simp)))) hHX,
    Snd.conjOK_of hc hp hH hY (Snd.rel_mul hc hp (Snd.rel_pow hc hp hX (e D.b (by simp)))
      (Snd.rel_pow hc hp hY (e D.d (by simp)))) hHY,
    Snd.normalFormOK_of hc hp D.r (.cons hX (.cons hY .nil)) ht hnorm⟩

theorem cubK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : CubData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : cubK c A B D = true) : (ops3 d).cubicCheck D = true := by
  subst hd
  unfold cubK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, hrx, hry, hrh, hr0, hoh0, hexp, ht, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  simp only [SecS.strictB_eq, Bool.and_eq_true, and_assoc] at hrun
  obtain ⟨hXr, hYr, hHo, hZt, hZX, hZY, hHX, hHY, hHZ, hnorm⟩ := hrun
  have e : ∀ v ∈ [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ], v < 65536 :=
    fun v hv => Snd.lt_of_all hexp hv
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  have hX := hL.2 D.rx (by rw [hlen]; exact hrx)
  have hY := hL.2 D.ry (by rw [hlen]; exact hry)
  have hH := hL.2 D.rh (by rw [hlen]; exact hrh)
  have hZ := Snd.rel_commM hc hp hX hY (e D.r (by simp))
  have hu := Snd.vrel_unit hc hp ht
  unfold Ops.cubicCheck Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨h2, hlt, hrx, hry, hrh, hr0, hoh0,
    Snd.eq_pow_one hc hp hX (e D.r (by simp)) hXr, Snd.eq_pow_one hc hp hY (e D.r (by simp)) hYr,
    Snd.eq_pow_one hc hp hH (e D.oh (by simp)) hHo,
    Snd.vne_of_vrel hc hp (Snd.vrel_vmul hc hp hu hZ) hu (Snd.ne_of_not_beq hZt),
    Snd.eq_of_rel (Snd.rel_mul hc hp hZ hX) (Snd.rel_mul hc hp hX hZ) hZX,
    Snd.eq_of_rel (Snd.rel_mul hc hp hZ hY) (Snd.rel_mul hc hp hY hZ) hZY,
    Snd.conjOK_of hc hp hH hX (Snd.rel_mul hc hp (Snd.rel_mul hc hp
      (Snd.rel_pow hc hp hX (e D.a (by simp))) (Snd.rel_pow hc hp hY (e D.b (by simp))))
      (Snd.rel_pow hc hp hZ (e D.k (by simp)))) hHX,
    Snd.conjOK_of hc hp hH hY (Snd.rel_mul hc hp (Snd.rel_mul hc hp
      (Snd.rel_pow hc hp hX (e D.c (by simp))) (Snd.rel_pow hc hp hY (e D.d (by simp))))
      (Snd.rel_pow hc hp hZ (e D.l (by simp)))) hHY,
    Snd.conjOK_of hc hp hH hZ (Snd.rel_pow hc hp hZ (e D.μ (by simp))) hHZ,
    Snd.normalFormOK_of hc hp D.r (.cons hX (.cons hY (.cons hZ .nil))) ht hnorm⟩

theorem cub2K_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : Cub2Data}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : cub2K c A B D = true) : (ops3 d).cub2Check D = true := by
  subst hd
  unfold cub2K at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, hrx, hry, hr0, hr16, ht, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  simp only [SecS.strictB_eq, Bool.and_eq_true, and_assoc] at hrun
  obtain ⟨hXr, hYr, hZt, hZX, hZY, hN1, hN2⟩ := hrun
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  have hX := hL.2 D.rx (by rw [hlen]; exact hrx)
  have hY := hL.2 D.ry (by rw [hlen]; exact hry)
  have hZ := Snd.rel_commM hc hp hX hY hr16
  have hu := Snd.vrel_unit hc hp ht
  unfold Ops.cub2Check Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨h2, hlt, hrx, hry, hr0, Snd.eq_pow_one hc hp hX hr16 hXr,
    Snd.eq_pow_one hc hp hY hr16 hYr,
    Snd.vne_of_vrel hc hp (Snd.vrel_vmul hc hp hu hZ) hu (Snd.ne_of_not_beq hZt),
    Snd.eq_of_rel (Snd.rel_mul hc hp hZ hX) (Snd.rel_mul hc hp hX hZ) hZX,
    Snd.eq_of_rel (Snd.rel_mul hc hp hZ hY) (Snd.rel_mul hc hp hY hZ) hZY,
    Snd.normOK_of hc hp hL hlen hX hY hZ hN1, Snd.normOK_of hc hp hL hlen hX hY hZ hN2⟩

theorem normCK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : NormData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : normCK c A B D = true) : (ops3 d).normCheck D = true := by
  subst hd
  unfold normCK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, houts, htests, hog0, hog, hgens, hexpo, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨helem, hgen⟩ := hrun
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  have houts' : ∀ r ∈ D.base.outs, r < D.base.nregs := fun r hr => Snd.lt_of_all houts hr
  have hxs := Snd.forall₂_map hL D.base.outs (fun r hr => by rw [hlen]; exact houts' r hr)
  have helemOK := Snd.elemOK_of hc hp hxs (fun k hk => Snd.lt_of_all htests hk) helem
  have hexpo' : ∀ j < D.gens.length, ∀ i < D.base.outs.length, ∀ k < D.base.outs.length,
      D.expo j k i < 65536 := by
    intro j hj i hi k hk
    have h1 := List.all_eq_true.1 hexpo j (List.mem_range.2 hj)
    have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
    exact of_decide_eq_true (List.all_eq_true.1 h2 k (List.mem_range.2 hk))
  have hgensOK := Snd.normGens_of hc hp hL hlen houts' (fun g hg => Snd.lt_of_all hgens hg) hog
    hexpo' hgen
  unfold Ops.normCheck Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, hog0, hgensOK⟩
  unfold Ops.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨h2, hlt, houts, helemOK⟩

end CFSG.KC.OpsLayK

end
