module

public import Certificates.Data.Kernel.OpsW4N
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsLayKSnd
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsW4N

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census CFSG.KC.OpsK CFSG.KC.OpsMN
  CFSG.KC.OpsHom CFSG.KC.LQT CFSG.KC.OpsLayK

section Hom

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V} (H : Hom O₀ O)

omit [Inhabited M] in
theorem appDigits_U : ∀ (xs : List Nat), (∀ x ∈ xs, H.P x) → ∀ (n : Nat) {v : V}, H.Q v →
    O₀.appDigits (xs.map H.U) n (H.W v) = H.W (O.appDigits xs n v) ∧
      H.Q (O.appDigits xs n v)
  | [], _, _, _, hv => ⟨rfl, hv⟩
  | x :: xs, hx, n, v, hv => by
    obtain ⟨e1, q1⟩ := H.app_U (hx x List.mem_cons_self) (n % 3) hv
    change O₀.appDigits (xs.map H.U) (n / 3) (O₀.app (H.U x) (n % 3) (H.W v)) =
      H.W (O.appDigits xs (n / 3) (O.app x (n % 3) v)) ∧ _
    rw [e1]
    exact appDigits_U xs (fun y hy => hx y (List.mem_cons_of_mem x hy)) _ q1

omit [Inhabited M] in
theorem kerOK_U {xs : List Nat} (hx : ∀ x ∈ xs, H.P x) (tests : List Nat) :
    O₀.kerOK (xs.map H.U) tests = O.kerOK xs tests := by
  unfold Ops.kerOK
  rw [List.length_map]
  apply List.all_congr rfl
  intro n
  apply List.any_congr rfl
  intro t
  unfold Ops.moved
  obtain ⟨u1, uq⟩ := H.unit t
  obtain ⟨a1, aq⟩ := appDigits_U H xs hx (n + 1) uq
  rw [u1, a1, H.vne aq uq]

omit [Inhabited M] in
theorem cubeOK_U {a : Nat} (ha : H.P a) : O₀.cubeOK (H.U a) = O.cubeOK a := by
  unfold Ops.cubeOK
  obtain ⟨m1, p1⟩ := H.mul ha ha
  obtain ⟨m2, p2⟩ := H.mul p1 ha
  rw [m1, m2, H.one.1, H.eq p2 H.one.2]

omit [Inhabited M] in
theorem elemOK_U {xs : List Nat} (hx : ∀ x ∈ xs, H.P x) (tests : List Nat) :
    O₀.elemOK (xs.map H.U) tests = O.elemOK xs tests := by
  unfold Ops.elemOK
  rw [H.commsOK_U xs hx, kerOK_U H hx,
    all_map_congr xs H.U _ _ fun x hx' => cubeOK_U H (hx x hx')]

theorem w4Check_of_N {A B : Nat} {D : W4Data} (eA : O₀.decode D.base.seedA = H.U A)
    (eB : O₀.decode D.base.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : w4N O A B D.base D.inv = true) : W4Data.check O₀ D = true := by
  unfold w4N at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hp⟩, hout⟩, hinv⟩, hr⟩ := h
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N H eA eB hA hB hp hr
  rw [forceL_eq, forceB_eq] at hk
  unfold w4OK at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨hel, hTT⟩, hmove⟩, hcomm⟩ := hk
  have hreg : ∀ r < D.base.nregs,
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[r]! = H.U (getN Rl r) ∧
        H.P (getN Rl r) :=
    fun r hr => hR.2 r (by rw [hlen]; exact hr)
  have hoR : ∀ r ∈ D.base.outs, r < D.base.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hout r hr)
  obtain ⟨eT, pT⟩ := hreg D.inv hinv
  have hxs : D.base.outs.map (fun r =>
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[r]!) =
        (D.base.outs.map (getN Rl)).map H.U := by
    rw [List.map_map]
    exact List.map_congr_left fun r hr => (hreg r (hoR r hr)).1
  have hP : ∀ x ∈ D.base.outs.map (getN Rl), H.P x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact (hreg r (hoR r hr)).2
  have gel : O₀.elemOK (D.base.outs.map fun r =>
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[r]!) D.base.tests = true := by
    rw [hxs, elemOK_U H hP]
    exact hel
  have gTT : O₀.eq (O₀.mul (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[D.inv]!
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[D.inv]!) O₀.one = true := by
    obtain ⟨m1, p1⟩ := H.mul pT pT
    rw [eT, m1, H.one.1, H.eq p1 H.one.2]
    exact hTT
  have gmove : D.base.tests.any (fun k => O₀.vne (O₀.vmul (O₀.unit k)
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[D.inv]!) (O₀.unit k)) =
        true := by
    obtain ⟨k, hk, hv⟩ := List.any_eq_true.1 hmove
    refine List.any_eq_true.2 ⟨k, hk, ?_⟩
    obtain ⟨eu, qu⟩ := H.unit k
    obtain ⟨ev, qv⟩ := H.vmul qu pT
    rw [eT, eu, ev, H.vne qv qu]
    exact hv
  have gcomm : D.base.outs.all (fun r => O₀.commOK
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[r]!
      (O₀.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog)[D.inv]!) = true := by
    refine List.all_eq_true.2 fun r hr => ?_
    obtain ⟨er, pr⟩ := hreg r (hoR r hr)
    rw [er, eT, H.commOK_U pr pT]
    exact List.all_eq_true.1 hcomm (getN Rl r) (List.mem_map_of_mem hr)
  unfold W4Data.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨hn, hp, hout, hinv, gel, gTT, gmove, gcomm⟩

end Hom

section Lay

theorem w4Check_of_L {c : Lay} {d A B : Nat} {LA LB : List Char} {D : W4Data}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : w4L c A B D.base D.inv = true) : W4Data.check (ops3 d) D = true := by
  subst hd
  unfold w4L at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hprog, houts, hinv, htests, hrun⟩ := h
  rw [Snd.runC_eq] at hrun
  obtain ⟨h2, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  have hT := hL.2 D.inv (by rw [hlen]; exact hinv)
  have hxs := Snd.forall₂_map hL D.base.outs
    (fun r hr => by rw [hlen]; exact Snd.lt_of_all houts hr)
  have htk : ∀ k ∈ D.base.tests, k < c.d := fun k hk => Snd.lt_of_all htests hk
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨⟨⟨hel, hTT⟩, hmove⟩, hcomm⟩ := hrun
  unfold W4Data.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨h2, hlt, houts, hinv, Snd.elemOK_of hc hp hxs htk hel,
    Snd.eq_of_rel (Snd.rel_mul hc hp hT hT) (Snd.rel_one hc hp) hTT, ?_, ?_⟩
  · refine Snd.any_mono (fun k hk hb => ?_) hmove
    exact Snd.vne_of_vrel hc hp (Snd.vrel_vmul hc hp (Snd.vrel_unit hc hp (htk k hk)) hT)
      (Snd.vrel_unit hc hp (htk k hk)) (Snd.ne_of_not_beq hb)
  · refine List.all_eq_true.2 fun r hr => ?_
    have hX := hL.2 r (by rw [hlen]; exact Snd.lt_of_all houts hr)
    exact Snd.eq_of_rel (Snd.rel_mul hc hp hX hT) (Snd.rel_mul hc hp hT hX)
      (List.all_eq_true.1 hcomm _ (List.mem_map_of_mem hr))

end Lay

end CFSG.KC.OpsW4N

end
