module

public import Certificates.Data.Kernel.OpsLayGKF
public import CFSG.Certificates.Kernel.OpsV4Sound

public section

namespace CFSG.KC.OpsLayGKF

open CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion CFSG.GH74.KGroups.J3 CFSG.KC.LQT
  CFSG.KC.OpsLayK CFSG.KC.OpsV4

variable {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V}

theorem appBase_of (S : Sim O₀ O) (b : Nat) : ∀ {Xs : List M} {xs : List Nat},
    List.Forall₂ S.R Xs xs → ∀ (n : Nat) {u : V₀} {v : V}, S.RV u v →
      S.RV (O₀.appBase b Xs n u) (O.appBase b xs n v)
  | _, _, .nil, _, _, _, h => h
  | _, _, .cons hX hs, n, _, _, h => by
    simp only [Ops.appBase]
    exact appBase_of S b hs (n / b) (S.app hX (n % b) h)

theorem kerModOK_of (S : Sim O₀ O) {T : M} {t : Nat} (hT : S.R T t) {Xs : List M}
    {xs : List Nat} (h : List.Forall₂ S.R Xs xs) {tests : List Nat} (hTs : ∀ k ∈ tests, S.T k)
    (hk : O.kerModOK t xs tests = true) : O₀.kerModOK T Xs tests = true := by
  unfold Ops.kerModOK at hk ⊢
  rw [h.length_eq]
  refine List.all_eq_true.2 fun n hn => ?_
  have hn' := List.all_eq_true.1 hk n hn
  unfold Ops.outsideN at hn' ⊢
  rw [Bool.and_eq_true] at hn' ⊢
  constructor
  · obtain ⟨k, hk', hv⟩ := List.any_eq_true.1 hn'.1
    exact List.any_eq_true.2 ⟨k, hk', S.vne (appBase_of S 2 h (n + 1) (S.unit (hTs k hk')))
      (S.unit (hTs k hk')) hv⟩
  · obtain ⟨k, hk', hv⟩ := List.any_eq_true.1 hn'.2
    exact List.any_eq_true.2 ⟨k, hk', S.vne (appBase_of S 2 h (n + 1) (S.unit (hTs k hk')))
      (S.vmul (S.unit (hTs k hk')) hT) hv⟩

theorem prodBase2_of (S : Sim O₀ O) : ∀ {Xs : List M} {xs : List Nat},
    List.Forall₂ S.R Xs xs → ∀ n, S.R (prodBase2 O₀ Xs n) (prodBase2 O xs n)
  | _, _, .nil, _ => by
    simp only [prodBase2]
    exact S.one
  | _, _, .cons hX hs, n => by
    simp only [prodBase2]
    by_cases hc : n % 2 = 1
    · rw [if_pos hc, if_pos hc]
      exact S.mul hX (prodBase2_of S hs (n / 2))
    · rw [if_neg hc, if_neg hc]
      exact prodBase2_of S hs (n / 2)

theorem fusCheck_of_G [Inhabited M] (S : Sim O₀ O) {D : FusData} (hn : 2 ≤ D.nregs)
    (hp : D.prog.all (Op.lt D.nregs) = true)
    (ho : [D.o0, D.o1, D.o2, D.o3].all (decide <| · < D.nregs) = true) {g : Nat → Nat}
    (hg : ∀ r < D.nregs, S.R (O₀.run D.prog
      (O₀.initRegs (O₀.decode D.seedA) (O₀.decode D.seedB) D.nregs))[r]! (g r))
    (hT : ∀ k ∈ D.tests, S.T k)
    (hE : ∀ k < 15, S.E (D.n1s.getD k 0) ∧ S.E (D.n2s.getD k 0))
    (h : gkfG O S.pw D g = true) : fusCheck O₀ D = true := by
  unfold gkfG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsq, hc⟩, hker⟩, hall⟩ := h
  have hlt : ∀ r ∈ [D.o0, D.o1, D.o2, D.o3], r < D.nregs :=
    fun r hr => of_decide_eq_true (List.all_eq_true.1 ho r hr)
  have r0 := hg _ (hlt D.o0 (by simp))
  have r1 := hg _ (hlt D.o1 (by simp))
  have r2 := hg _ (hlt D.o2 (by simp))
  have r3 := hg _ (hlt D.o3 (by simp))
  have hxs := List.Forall₂.cons r0 (.cons r1 (.cons r2 (.cons r3 .nil)))
  unfold fusCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hp, hlt D.o0 (by simp), hlt D.o1 (by simp), hlt D.o2 (by simp),
    hlt D.o3 (by simp), all_of_forall₂ (p := fun X => O₀.eq (O₀.mul X X) O₀.one)
      (q := fun x => O.eq (O.mul x x) O.one) (fun _ _ hX hx => S.eq (S.mul hX hX) S.one hx) hxs hsq,
    S.commsOK hxs hc, kerModOK_of S S.one hxs hT hker, ?_⟩
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' := List.all_eq_true.1 hall k hk
  rw [Bool.and_eq_true] at hk' ⊢
  refine ⟨hk'.1, ?_⟩
  have rs := hg _ (of_decide_eq_true hk'.1)
  have rp := prodBase2_of S hxs (k + 1)
  obtain ⟨e1, e2⟩ := hE k (List.mem_range.1 hk)
  have ht := hk'.2
  unfold fusTestG at ht
  unfold fusTest
  simp only [Bool.and_eq_true] at ht ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
  exact ⟨⟨⟨⟨S.eq (S.mul rs rs) S.one h1, h2⟩, h3⟩, S.eq (S.pow (S.mul rs r0) e1) S.one h4⟩,
    S.eq (S.pow (S.mul rs rp) e2) S.one h5⟩

theorem gkfFusK_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {D : FusData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (h : gkfFusK c A B D = true) : fusCheck (ops3 d) D = true := by
  subst hd
  unfold gkfFusK at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hprog, ho⟩, htests⟩, hexp⟩, hrun⟩ := h
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.prog A B D.nregs
  refine fusCheck_of_G (Sim.ofL3 c hc hp) hn hlt ho (fun r hr => hL.2 r (by rw [hlen]; exact hr))
    (fun k hk => Snd.lt_of_all htests hk) (fun k hk => ?_) hrun
  have h2 := List.all_eq_true.1 hexp k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h2
  exact ⟨(of_decide_eq_true h2.1 : D.n1s.getD k 0 < 65536),
    (of_decide_eq_true h2.2 : D.n2s.getD k 0 < 65536)⟩

end CFSG.KC.OpsLayGKF

end
