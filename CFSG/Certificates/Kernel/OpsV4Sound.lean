module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.RankThree.PartTwo.Census.Sporadic.FourGroupCert
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsLayKSndP
public import CFSG.Certificates.Kernel.OpsRenLSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsV4

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census CFSG.KC.OpsK CFSG.KC.OpsMN
  CFSG.KC.OpsHom CFSG.KC.LQT CFSG.KC.OpsLayK

structure Sim {M V₀ V : Type} (O₀ : Ops M V₀) (O : Ops Nat V) where
  R : M → Nat → Prop
  RV : V₀ → V → Prop
  T : Nat → Prop
  E : Nat → Prop
  pw : Nat → Nat → Nat
  mul {X Y : M} {x y : Nat} : R X x → R Y y → R (O₀.mul X Y) (O.mul x y)
  one : R O₀.one O.one
  eq {X Y : M} {x y : Nat} : R X x → R Y y → O.eq x y = true → O₀.eq X Y = true
  vmul {u : V₀} {v : V} {X : M} {x : Nat} : RV u v → R X x → RV (O₀.vmul u X) (O.vmul v x)
  unit {k : Nat} : T k → RV (O₀.unit k) (O.unit k)
  vne {u u' : V₀} {v v' : V} : RV u v → RV u' v' → O.vne v v' = true → O₀.vne u u' = true
  pow {X : M} {x e : Nat} : R X x → E e → R (O₀.pow X e) (pw x e)

theorem all_of_forall₂ {α β : Type} {P : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ X x, P X x → q x = true → p X = true) :
    ∀ {Xs : List α} {xs : List β}, List.Forall₂ P Xs xs → xs.all q = true → Xs.all p = true
  | _, _, .nil, _ => rfl
  | _, _, .cons hX hs, h => by
    rw [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨hpq _ _ hX h.1, all_of_forall₂ hpq hs h.2⟩

namespace Sim

variable {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V} (S : Sim O₀ O)

theorem app {X : M} {x : Nat} (hX : S.R X x) : ∀ (n : Nat) {u : V₀} {v : V}, S.RV u v →
    S.RV (O₀.app X n u) (O.app x n v)
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    simp only [Ops.app]
    exact app hX n (S.vmul h hX)

theorem appDigits : ∀ {Xs : List M} {xs : List Nat}, List.Forall₂ S.R Xs xs →
    ∀ (n : Nat) {u : V₀} {v : V}, S.RV u v → S.RV (O₀.appDigits Xs n u) (O.appDigits xs n v)
  | _, _, .nil, _, _, _, h => h
  | _, _, .cons hX hs, n, _, _, h => by
    simp only [Ops.appDigits]
    exact appDigits hs (n / 3) (S.app hX (n % 3) h)

theorem kerOK {Xs : List M} {xs : List Nat} (h : List.Forall₂ S.R Xs xs) {tests : List Nat}
    (hT : ∀ k ∈ tests, S.T k) (hk : O.kerOK xs tests = true) : O₀.kerOK Xs tests = true := by
  unfold Ops.kerOK at hk ⊢
  rw [h.length_eq]
  refine List.all_eq_true.2 fun n hn => ?_
  obtain ⟨k, hk', hm⟩ := List.any_eq_true.1 (List.all_eq_true.1 hk n hn)
  refine List.any_eq_true.2 ⟨k, hk', ?_⟩
  unfold Ops.moved at hm ⊢
  exact S.vne (S.appDigits h (n + 1) (S.unit (hT k hk'))) (S.unit (hT k hk')) hm

theorem commOK {X Y : M} {x y : Nat} (hX : S.R X x) (hY : S.R Y y)
    (h : O.commOK x y = true) : O₀.commOK X Y = true :=
  S.eq (S.mul hX hY) (S.mul hY hX) h

theorem commsOK : ∀ {Xs : List M} {xs : List Nat}, List.Forall₂ S.R Xs xs →
    O.commsOK xs = true → O₀.commsOK Xs = true
  | _, _, .nil, _ => rfl
  | _, _, .cons hX hs, h => by
    simp only [Ops.commsOK, Bool.and_eq_true] at h ⊢
    exact ⟨all_of_forall₂ (fun _ _ hY => S.commOK hX hY) hs h.1, commsOK hs h.2⟩

theorem elemOK {Xs : List M} {xs : List Nat} (h : List.Forall₂ S.R Xs xs) {tests : List Nat}
    (hT : ∀ k ∈ tests, S.T k) (he : O.elemOK xs tests = true) : O₀.elemOK Xs tests = true := by
  unfold Ops.elemOK at he ⊢
  simp only [Bool.and_eq_true] at he ⊢
  exact ⟨⟨all_of_forall₂ (p := O₀.cubeOK) (q := O.cubeOK)
    (fun _ _ hX hc => S.eq (S.mul (S.mul hX hX) hX) S.one hc) h he.1.1,
    S.commsOK h he.1.2⟩, S.kerOK h hT he.2⟩

theorem conjOK {X T T₁ T₂ : M} {x t t₁ t₂ : Nat} (hX : S.R X x) (hT : S.R T t)
    (h₁ : S.R T₁ t₁) (h₂ : S.R T₂ t₂) (h : conjG O x t t₁ t₂ (O.mul t₁ t₂) = true) :
    LiftData.conjOK O₀ X T T₁ T₂ = true := by
  unfold conjG at h
  rw [forceB_eq] at h
  unfold LiftData.conjOK
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (S.eq (S.mul hX hT) (S.mul h₁ hX) h))
  · exact Or.inl (Or.inr (S.eq (S.mul hX hT) (S.mul h₂ hX) h))
  · exact Or.inr (S.eq (S.mul hX hT) (S.mul (S.mul h₁ h₂) hX) h)

theorem outs_getD {D : LiftData} {i : Nat} (hi : i < D.base.outs.length) :
    D.base.outs[i]! = D.base.outs.getD i 0 ∧ D.base.outs.getD i 0 ∈ D.base.outs := by
  rw [getElem!_pos D.base.outs i hi, Snd.getD_eq_of_lt 0 hi]
  exact ⟨rfl, List.getElem_mem hi⟩

theorem mem_regsL_out {D : LiftData} {r : Nat} (h : r ∈ D.base.outs) : r ∈ regsL D :=
  List.mem_append_left _ h

theorem mem_regsL_unit {D : LiftData} {n : Nat} (h : D.units.any (fun u => u.1 == n) = true) :
    n ∈ regsL D := by
  obtain ⟨u, hu, he⟩ := List.any_eq_true.1 h
  rw [beq_iff_eq] at he
  subst he
  exact List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hu)))

theorem relOK [Inhabited M] {D : LiftData} {Ra : Array M} {g : Nat → Nat}
    (hg : ∀ r ∈ regsL D, r < D.base.nregs → S.R Ra[r]! (g r))
    (hout : ∀ r ∈ D.base.outs, r < D.base.nregs) (rel : LiftRel) (h : relG O D g rel = true) :
    LiftData.relOK O₀ D Ra rel = true := by
  have hy : ∀ {i : Nat}, i < D.base.outs.length → D.base.outs[i]! = D.base.outs.getD i 0 ∧
      S.R Ra[D.base.outs.getD i 0]! (g (D.base.outs.getD i 0)) := fun hi =>
    ⟨(outs_getD hi).1, hg _ (mem_regsL_out (outs_getD hi).2) (hout _ (outs_getD hi).2)⟩
  cases rel with
  | inv n i =>
    simp only [relG, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hi⟩, ha⟩, he⟩ := h
    have hN := hg n (mem_regsL_unit ha) hn
    obtain ⟨ei, hY⟩ := hy hi
    simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq]
    rw [ei]
    exact ⟨⟨⟨hn, hi⟩, ha⟩, S.eq (S.mul hN hY) (S.mul (S.mul hY hY) hN) he⟩
  | fix n i =>
    simp only [relG, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hi⟩, ha⟩, he⟩ := h
    have hN := hg n (mem_regsL_unit ha) hn
    obtain ⟨ei, hY⟩ := hy hi
    simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq]
    rw [ei]
    exact ⟨⟨⟨hn, hi⟩, ha⟩, S.eq (S.mul hN hY) (S.mul hY hN) he⟩
  | swap n i j =>
    simp only [relG, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hn, hi⟩, hj⟩, ha⟩, he₁⟩, he₂⟩ := h
    have hN := hg n (mem_regsL_unit ha) hn
    obtain ⟨ei, hY⟩ := hy hi
    obtain ⟨ej, hZ⟩ := hy hj
    simp only [LiftData.relOK, Bool.and_eq_true, decide_eq_true_eq]
    rw [ei, ej]
    exact ⟨⟨⟨⟨⟨hn, hi⟩, hj⟩, ha⟩, S.eq (S.mul hN hY) (S.mul hZ hN) he₁⟩,
      S.eq (S.mul hN hZ) (S.mul hY hN) he₂⟩

theorem liftCheck [Inhabited M] {D : LiftData} (hn : 2 ≤ D.base.nregs)
    (hp : D.base.prog.all (Op.lt D.base.nregs) = true) {g : Nat → Nat}
    (hg : ∀ r ∈ regsL D, r < D.base.nregs → S.R (O₀.run D.base.prog
      (O₀.initRegs (O₀.decode D.base.seedA) (O₀.decode D.base.seedB) D.base.nregs))[r]! (g r))
    (hT : ∀ k ∈ D.base.tests, S.T k) (hE : ∀ u ∈ D.units, S.E u.2)
    (h : liftG O S.pw D g = true) : LiftData.check O₀ D = true := by
  unfold liftG at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hout, h₁, h₂, hel, hT₁, hT₂, hc, hmov, hconj, hunits, hrels⟩ := h
  rw [forceB_eq] at hconj
  have hoR : ∀ r ∈ D.base.outs, r < D.base.nregs := fun r hr =>
    of_decide_eq_true (List.all_eq_true.1 hout r hr)
  have r₁ := hg D.inv₁ (List.mem_append_right _ List.mem_cons_self) h₁
  have r₂ := hg D.inv₂ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) h₂
  have hX : ∀ r ∈ D.base.outs, S.R (O₀.run D.base.prog
      (O₀.initRegs (O₀.decode D.base.seedA) (O₀.decode D.base.seedB) D.base.nregs))[r]! (g r) :=
    fun r hr => hg r (mem_regsL_out hr) (hoR r hr)
  have hxs : ∀ L : List Nat, (∀ r ∈ L, r ∈ D.base.outs) →
      List.Forall₂ S.R (L.map fun r => (O₀.run D.base.prog
        (O₀.initRegs (O₀.decode D.base.seedA) (O₀.decode D.base.seedB) D.base.nregs))[r]!)
        (L.map g) := by
    intro L
    induction L with
    | nil => intro _; exact List.Forall₂.nil
    | cons r L ih =>
      intro hL
      exact List.Forall₂.cons (hX r (hL r List.mem_cons_self))
        (ih fun r' hr' => hL r' (List.mem_cons_of_mem _ hr'))
  unfold LiftData.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hp, hout, h₁, h₂, S.elemOK (hxs _ fun _ h => h) hT hel,
    S.eq (S.mul r₁ r₁) S.one hT₁, S.eq (S.mul r₂ r₂) S.one hT₂, S.commOK r₁ r₂ hc, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hv⟩ := List.any_eq_true.1 hmov
    exact List.any_eq_true.2 ⟨k, hk, S.vne (S.vmul (S.unit (hT k hk)) r₁) (S.unit (hT k hk)) hv⟩
  · refine List.all_eq_true.2 fun r hr => ?_
    have hb := List.all_eq_true.1 hconj r hr
    rw [Bool.and_eq_true] at hb ⊢
    exact ⟨S.conjOK (hX r hr) r₁ r₁ r₂ hb.1, S.conjOK (hX r hr) r₂ r₁ r₂ hb.2⟩
  · refine List.all_eq_true.2 fun u hu => ?_
    have hb := List.all_eq_true.1 hunits u hu
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    have mu : u.1 ∈ regsL D := List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hu)))
    exact ⟨hb.1, S.eq (S.pow (hg u.1 mu hb.1.1) (hE u hu)) S.one hb.2⟩
  · exact List.all_eq_true.2 fun rel hrel => S.relOK hg hoR rel (List.all_eq_true.1 hrels rel hrel)

@[expose] noncomputable def ofHom (H : Hom O₀ O) : Sim O₀ O where
  R X x := X = H.U x ∧ H.P x
  RV u v := u = H.W v ∧ H.Q v
  T _ := True
  E _ := True
  pw X e := powN O (e + 1) X e
  mul := by
    rintro _ _ x y ⟨rfl, hx⟩ ⟨rfl, hy⟩
    exact H.mul hx hy
  one := H.one
  eq := by
    rintro _ _ x y ⟨rfl, hx⟩ ⟨rfl, hy⟩ h
    rw [H.eq hx hy]
    exact h
  vmul := by
    rintro _ v _ x ⟨rfl, hv⟩ ⟨rfl, hx⟩
    exact H.vmul hv hx
  unit _ := H.unit _
  vne := by
    rintro _ _ v v' ⟨rfl, hv⟩ ⟨rfl, hv'⟩ h
    rw [H.vne hv hv']
    exact h
  pow := by
    rintro _ x e ⟨rfl, hx⟩ -
    rw [powN_eq O _ _ _ (Nat.lt_succ_self e)]
    exact H.pow_U e hx

end Sim

@[expose] noncomputable def Sim.ofL3 (c : Lay) (hc : c.ok = true) (hp : c.p = 3) :
    Sim (ops3 c.d) (opsL c) where
  R := Snd.LRel c
  RV := Snd.LVRel c
  T k := k < c.d
  E e := e < 65536
  pw := powK c
  mul hX hY := Snd.rel_mul hc hp hX hY
  one := Snd.rel_one hc hp
  eq hX hY h := Snd.eq_of_rel hX hY h
  vmul hu hX := Snd.vrel_vmul hc hp hu hX
  unit hk := Snd.vrel_unit hc hp hk
  vne hu hu' h := Snd.vne_of_vrel hc hp hu hu' (Snd.ne_of_not_beq h)
  pow hX he := Snd.rel_pow hc hp hX he

@[expose] noncomputable def Sim.ofLP (c : Lay) (hc : c.ok = true) :
    Sim (opsP c.p c.d) (opsL c) where
  R := SndP.LRel c
  RV := SndP.LVRel c
  T k := k < c.d
  E e := e < 65536
  pw := powK c
  mul hX hY := SndP.rel_mul hc hX hY
  one := SndP.rel_one hc
  eq hX hY h := SndP.eq_of_rel hX hY h
  vmul hu hX := SndP.vrel_vmul hc hu hX
  unit hk := SndP.vrel_unit hc hk
  vne hu hu' h := SndP.vne_of_vrel hc hu hu' (Snd.ne_of_not_beq h)
  pow hX he := SndP.rel_pow hc hX he

theorem v4Check_eq {M V : Type} [Inhabited M] (O : Ops M V) (D : V4Data) :
    V4Data.check O D = LiftData.check O (v4Lift D.base D.inv₁ D.inv₂) := by
  unfold V4Data.check LiftData.check v4Lift
  simp only [List.all_nil, Bool.and_true]
  rfl

section Hom

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V} (H : Hom O₀ O)

theorem liftCheck_of_N {A B : Nat} {D : LiftData} (eA : O₀.decode D.base.seedA = H.U A)
    (eB : O₀.decode D.base.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : liftN O A B D = true) : LiftData.check O₀ D = true := by
  unfold liftN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hp⟩, hr⟩ := h
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N H eA eB hA hB hp hr
  exact (Sim.ofHom H).liftCheck hn hp (g := getN Rl)
    (fun r _ hr => hR.2 r (by rw [hlen]; exact hr)) (fun _ _ => trivial) (fun _ _ => trivial) hk

theorem v4Check_of_N {A B : Nat} {D : V4Data} (eA : O₀.decode D.base.seedA = H.U A)
    (eB : O₀.decode D.base.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : v4N O A B D.base D.inv₁ D.inv₂ = true) : V4Data.check O₀ D = true := by
  rw [v4Check_eq]
  exact liftCheck_of_N H eA eB hA hB h

end Hom

theorem getR_idxOf (c : Lay) (R : List Nat) : ∀ (L : List Nat) {r : Nat}, r ∈ L →
    getR c (L.map (getR c R)) (L.idxOf r) = getR c R r
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, r, h => by
    by_cases har : a = r
    · subst har
      simp [List.idxOf_cons_self, getR]
    · have hr : r ∈ L := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm har
        · exact h
      have e : (a :: L).idxOf r = L.idxOf r + 1 := by
        simp [List.idxOf_cons, beq_iff_eq, har]
      rw [e, List.map_cons]
      simpa [getR] using getR_idxOf c R L hr

theorem liftCheck_of_L {c : Lay} {d A B : Nat} {LA LB : List Char} {D : LiftData}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : liftL c A B D = true) : LiftData.check (ops3 d) D = true := by
  subst hd
  unfold liftL liftPreL at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hprog, htests⟩, hexp⟩, hrun⟩ := h
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  exact (Sim.ofL3 c hc hp).liftCheck hn hlt (fun r _ hr => hL.2 r (by rw [hlen]; exact hr))
    (fun k hk => Snd.lt_of_all htests hk)
    (fun u hu => (of_decide_eq_true (List.all_eq_true.1 hexp u hu) : u.2 < 65536)) hrun

theorem v4Check_of_L {c : Lay} {d A B : Nat} {LA LB : List Char} {D : V4Data}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : v4L c A B D.base D.inv₁ D.inv₂ = true) : V4Data.check (ops3 d) D = true := by
  rw [v4Check_eq]
  exact liftCheck_of_L hc hp hd hA hB hsA hsB h

theorem liftCheck_of_LP {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : LiftData}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : liftL c A B D = true) : LiftData.check (opsP p d) D = true := by
  subst hp hd
  unfold liftL liftPreL at h
  rw [Snd.runC_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hprog, htests⟩, hexp⟩, hrun⟩ := h
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have hL := SndP.lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  exact (Sim.ofLP c hc).liftCheck hn hlt (fun r _ hr => hL.2 r (by rw [hlen]; exact hr))
    (fun k hk => Snd.lt_of_all htests hk)
    (fun u hu => (of_decide_eq_true (List.all_eq_true.1 hexp u hu) : u.2 < 65536)) hrun

theorem v4Check_of_LP {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : V4Data}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (h : v4L c A B D.base D.inv₁ D.inv₂ = true) : V4Data.check (opsP p d) D = true := by
  rw [v4Check_eq]
  exact liftCheck_of_LP hc hp hd hA hB hsA hsB h

theorem liftCheck_of_chunks {c : Lay} {d A B : Nat} {LA LB : List Char} {D : LiftData}
    {cs : List RChunk} {S : Nat → List Nat}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (hpre : liftPreL c D = true) (hren : renOK (regsL D) D.base.prog cs = true)
    (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hfin : liftFinL c (S cs.length) D = true) : LiftData.check (ops3 d) D = true := by
  subst hd
  unfold liftPreL at hpre
  simp only [Bool.and_eq_true] at hpre
  obtain ⟨⟨hprog, htests⟩, hexp⟩ := hpre
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have e := renOK_sound hn hlt hren h0 hch
  have hL := Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  refine (Sim.ofL3 c hc hp).liftCheck hn hlt
    (g := fun r => getR c (S cs.length) ((regsL D).idxOf r)) (fun r hr hrn => ?_)
    (fun k hk => Snd.lt_of_all htests hk)
    (fun u hu => (of_decide_eq_true (List.all_eq_true.1 hexp u hu) : u.2 < 65536)) hfin
  rw [← e, getR_idxOf c _ _ hr]
  exact hL.2 r (by rw [hlen]; exact hrn)

theorem v4Check_of_chunks {c : Lay} {d A B : Nat} {LA LB : List Char} {D : V4Data}
    {cs : List RChunk} {S : Nat → List Nat}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (hpre : liftPreL c (v4Lift D.base D.inv₁ D.inv₂) = true)
    (hren : renOK (regsL (v4Lift D.base D.inv₁ D.inv₂)) D.base.prog cs = true)
    (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hfin : v4FinL c (S cs.length) D.base D.inv₁ D.inv₂ = true) :
    V4Data.check (ops3 d) D = true := by
  rw [v4Check_eq]
  exact liftCheck_of_chunks hc hp hd hA hB hsA hsB hpre hren h0 hch hfin

theorem liftCheck_of_chunksP {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : LiftData}
    {cs : List RChunk} {S : Nat → List Nat}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (hpre : liftPreL c D = true) (hren : renOK (regsL D) D.base.prog cs = true)
    (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hfin : liftFinL c (S cs.length) D = true) : LiftData.check (opsP p d) D = true := by
  subst hp hd
  unfold liftPreL at hpre
  simp only [Bool.and_eq_true] at hpre
  obtain ⟨⟨hprog, htests⟩, hexp⟩ := hpre
  obtain ⟨hn, hlt⟩ := Snd.progOK_spec hprog
  have e := renOK_sound hn hlt hren h0 hch
  have hL := SndP.lcorr_regs hc hA hB hsA hsB hprog
  have hlen := Snd.runL_initR_length c D.base.prog A B D.base.nregs
  refine (Sim.ofLP c hc).liftCheck hn hlt
    (g := fun r => getR c (S cs.length) ((regsL D).idxOf r)) (fun r hr hrn => ?_)
    (fun k hk => Snd.lt_of_all htests hk)
    (fun u hu => (of_decide_eq_true (List.all_eq_true.1 hexp u hu) : u.2 < 65536)) hfin
  rw [← e, getR_idxOf c _ _ hr]
  exact hL.2 r (by rw [hlen]; exact hrn)

theorem v4Check_of_chunksP {c : Lay} {p d A B : Nat} {LA LB : List Char} {D : V4Data}
    {cs : List RChunk} {S : Nat → List Nat}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : D.base.seedA = String.ofList LA) (hsB : D.base.seedB = String.ofList LB)
    (hpre : liftPreL c (v4Lift D.base D.inv₁ D.inv₂) = true)
    (hren : renOK (regsL (v4Lift D.base D.inv₁ D.inv₂)) D.base.prog cs = true)
    (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hfin : v4FinL c (S cs.length) D.base D.inv₁ D.inv₂ = true) :
    V4Data.check (opsP p d) D = true := by
  rw [v4Check_eq]
  exact liftCheck_of_chunksP hc hp hd hA hB hsA hsB hpre hren h0 hch hfin

end CFSG.KC.OpsV4

end
