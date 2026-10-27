module

public import Certificates.Data.Kernel.Cert690.CensusSBase
public import Certificates.Data.Kernel.Cert690.CensusSBind
public import CFSG.Certificates.Kernel.Cert690.CensusSSound

public section

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum

@[expose] def InOS (G : GK) (c : Nat) : Prop := G.ix c < G.n ∧ G.getO (G.ix c) = c

structure BaseFacts (G : GK) (Llist : Array (Array Nat)) (cs : List Nat) (B : SBase) : Prop where
  stab : ∀ k < B.nS, actS (fS B.spk k) B.b = B.b ∧ InOS G (fS B.spk k) ∧
    (k + 1 < B.nS → fS B.spk k < fS B.spk (k + 1))
  tp : ∀ p ∈ B.sing, InOS G (B.tpT.getD p 0) ∧ actS (B.tpT.getD p 0) B.b = p ∧
    mulF (B.tpT.getD p 0) (B.tpI.getD p 0) = oneF
  fg : ∀ gs ∈ B.fg, ∀ x ∈ gs, InOS G x
  pglc : ∀ c ∈ B.pglc, InOS G c
  lenFc : B.fc.length = B.nF
  lenFg : B.fg.length = B.nF
  fcLt : ∀ g < B.nF, B.fc.getD g 0 < B.LC.length
  first : ∀ c < B.LC.length, ∃ g < B.nF, B.fc.getD g 0 = c ∧
    ∀ x ∈ B.fg.getD g [], x ∈ B.LC.getD c []
  lenLG : B.LG.length = B.LC.length
  lenCs : cs.length = B.LC.length
  cand : List.Forall₂ (fun c p => (∀ x ∈ p.1, x ∈ p.2) ∧ (∀ x ∈ p.2, x ∈ subProds p.1) ∧
      List.Forall₂ (fun x i => x = G.getO i) p.2 (Llist[c]!).toList) cs (B.LG.zip B.LC)

theorem inOS_iff (G : GK) (c : Nat) : inOS G c = true ↔ InOS G c := by
  unfold inOS InOS
  simp only [bAnd_eq, Bool.and_eq_true, blt_eqS, beq_eqS, decide_eq_true_eq]

theorem fcS_gen (LC : List (List Nat)) (fc : List Nat) : ∀ (fg : List (List Nat)) (n : Nat),
    fcS LC fc fg n = true →
    fc.length = fg.length ∧ n ≤ LC.length ∧
    (∀ g < fc.length, n ≤ fc.getD g 0 + 1 ∧ fc.getD g 0 < LC.length) ∧
    ∀ c, n ≤ c → c < LC.length →
      ∃ g < fc.length, fc.getD g 0 = c ∧ ∀ x ∈ fg.getD g [], x ∈ LC.getD c [] := by
  induction fc with
  | nil =>
    intro fg n h
    cases fg with
    | nil =>
      change Nat.beq n (lenS LC) = true at h
      rw [beq_eqS, decide_eq_true_eq, lenS_eq] at h
      subst h
      exact ⟨rfl, le_rfl, fun g hg => absurd hg (Nat.not_lt_zero _),
        fun c hc hc' => absurd hc' (by omega)⟩
    | cons gs fg => exact absurd h Bool.false_ne_true
  | cons c fc ih =>
    intro fg n h
    cases fg with
    | nil => exact absurd h Bool.false_ne_true
    | cons gs fg =>
      change Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (fcS LC fc fg (Nat.succ n))
            (allS (fun x => memS x (nthS [] LC c)) gs)) (Nat.beq c n))
        (fcS LC fc fg n) (Nat.beq (Nat.succ c) n) = true at h
      by_cases e : c + 1 = n
      · have e' : Nat.beq (Nat.succ c) n = true := by rw [beq_eqS, decide_eq_true_eq]; exact e
        rw [e'] at h
        obtain ⟨hl, hn, hent, hcov⟩ := ih fg n h
        refine ⟨by simp [hl], hn, fun g hg => ?_, fun c' hc' hc'' => ?_⟩
        · cases g with
          | zero => simp only [List.getD_cons_zero]; omega
          | succ g =>
            simp only [List.getD_cons_succ]
            exact hent g (by simpa using hg)
        · obtain ⟨g, hg, h1, h2⟩ := hcov c' hc' hc''
          exact ⟨g + 1, by simpa using hg, by simpa using h1, by simpa using h2⟩
      · have e' : Nat.beq (Nat.succ c) n = false := by
          rw [beq_eqS, decide_eq_false_iff_not]
          exact e
        rw [e', bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, beq_eqS,
          decide_eq_true_eq, allS_eq_true] at h
        obtain ⟨hcn, hgs, ht⟩ := h
        subst hcn
        obtain ⟨hl, hn, hent, hcov⟩ := ih fg (c + 1) ht
        refine ⟨by simp [hl], by omega, fun g hg => ?_, fun c' hc' hc'' => ?_⟩
        · cases g with
          | zero => simp only [List.getD_cons_zero]; omega
          | succ g =>
            simp only [List.getD_cons_succ]
            have := hent g (by simpa using hg)
            omega
        · by_cases hcc : c' = c
          · subst hcc
            refine ⟨0, by simp, by simp, fun x hx => ?_⟩
            simp only [List.getD_cons_zero] at hx
            have := hgs x hx
            rwa [memS_eq_true, nthS_eq] at this
          · obtain ⟨g, hg, h1, h2⟩ := hcov c' (by omega) hc''
            exact ⟨g + 1, by simpa using hg, by simpa using h1, by simpa using h2⟩

theorem fcS_sound (LC : List (List Nat)) (fc : List Nat) (fg : List (List Nat))
    (h : fcS LC fc fg 0 = true) :
    fc.length = fg.length ∧ (∀ g < fc.length, fc.getD g 0 < LC.length) ∧
    ∀ c < LC.length, ∃ g < fc.length, fc.getD g 0 = c ∧ ∀ x ∈ fg.getD g [], x ∈ LC.getD c [] := by
  obtain ⟨hl, -, hent, hcov⟩ := fcS_gen LC fc fg 0 h
  exact ⟨hl, fun g hg => (hent g hg).2, fun c hc => hcov c (Nat.zero_le c) hc⟩

theorem c690b_bAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem stabD_sound {G : GK} {B : SBase} {k c a : Nat} (h : stabD G B k c a = true) :
    a = B.b ∧ InOS G c ∧ (k + 1 < B.nS → c < fS B.spk (k + 1)) := by
  unfold stabD at h
  obtain ⟨h1, h3⟩ := c690b_bAnd h
  obtain ⟨h1, h2⟩ := c690b_bAnd h1
  refine ⟨Nat.eq_of_beq_eq_true h1, (inOS_iff G c).mp h2, fun hk => ?_⟩
  have e : Nat.blt (Nat.succ k) B.nS = true := by rw [blt_eqS, decide_eq_true_eq]; exact hk
  rw [e] at h3
  change strictB (fS B.spk (Nat.succ k)) (Nat.blt c) = true at h3
  rw [strictB_eq, blt_eqS, decide_eq_true_eq] at h3
  exact h3

theorem stabS_sound {G : GK} {B : SBase} (h : stabS G B = true) :
    ∀ k < B.nS, actS (fS B.spk k) B.b = B.b ∧ InOS G (fS B.spk k) ∧
      (k + 1 < B.nS → fS B.spk k < fS B.spk (k + 1)) := by
  intro k hk
  have h1 : strictB (fS B.spk k) (stabC G B k) = true :=
    (allS_eq_true _ _).mp h k (List.mem_range.mpr hk)
  rw [strictB_eq] at h1
  have h2 : strictB (actS (fS B.spk k) B.b) (stabD G B k (fS B.spk k)) = true := h1
  rw [strictB_eq] at h2
  exact stabD_sound h2

theorem tpS_sound {G : GK} {B : SBase}
    (h : allS (fun p => (fun t => bAnd(inOS G t, bAnd(Nat.beq (actS t B.b) p,
      Nat.beq (mulF t (nthS (nat_lit 0) B.tpI p)) oneF))) (nthS (nat_lit 0) B.tpT p)) B.sing =
      true) :
    ∀ p ∈ B.sing, InOS G (B.tpT.getD p 0) ∧ actS (B.tpT.getD p 0) B.b = p ∧
      mulF (B.tpT.getD p 0) (B.tpI.getD p 0) = oneF := by
  intro p hp
  obtain ⟨h1, h2⟩ := c690b_bAnd ((allS_eq_true _ _).mp h p hp)
  obtain ⟨h2, h3⟩ := c690b_bAnd h2
  have h2' := Nat.eq_of_beq_eq_true h2
  have h3' := Nat.eq_of_beq_eq_true h3
  rw [nthS_eq] at h1 h2' h3'
  rw [nthS_eq] at h3'
  exact ⟨(inOS_iff G _).mp h1, h2', h3'⟩

theorem fgS_sound {G : GK} {fg : List (List Nat)} (h : allS (allS (inOS G)) fg = true) :
    ∀ gs ∈ fg, ∀ x ∈ gs, InOS G x := fun gs hgs x hx =>
  (inOS_iff G x).mp ((allS_eq_true _ _).mp ((allS_eq_true _ _).mp h gs hgs) x hx)

theorem pglcS_sound {G : GK} {l : List Nat} (h : allS (inOS G) l = true) :
    ∀ c ∈ l, InOS G c := fun c hc => (inOS_iff G c).mp ((allS_eq_true _ _).mp h c hc)

theorem candZ_sound {G : GK} {Llist : Array (Array Nat)} {cs : List Nat}
    {LG LC : List (List Nat)}
    (h : zipS (fun c p => bAnd(allS (fun x => memS x p.2) p.1,
        bAnd(allS (fun x => memS x (subProds p.1)) p.2,
          zipS (fun x i => Nat.beq x (G.getO i)) p.2 (Llist[c]!).toList)))
      cs (List.zip LG LC) = true) :
    List.Forall₂ (fun c p => (∀ x ∈ p.1, x ∈ p.2) ∧ (∀ x ∈ p.2, x ∈ subProds p.1) ∧
      List.Forall₂ (fun x i => x = G.getO i) p.2 (Llist[c]!).toList) cs (LG.zip LC) := by
  rw [zipS_eq_true] at h
  refine h.imp fun c p hcp => ?_
  obtain ⟨h1, h2⟩ := c690b_bAnd hcp
  obtain ⟨h2, h3⟩ := c690b_bAnd h2
  refine ⟨fun x hx => (memS_eq_true _ _).mp ((allS_eq_true _ _).mp h1 x hx),
    fun x hx => (memS_eq_true _ _).mp ((allS_eq_true _ _).mp h2 x hx), ?_⟩
  rw [zipS_eq_true] at h3
  exact h3.imp fun x i hxi => Nat.eq_of_beq_eq_true hxi

theorem baseS_sound {G : GK} {Llist : Array (Array Nat)} {cs : List Nat} {B : SBase}
    (h : baseS G Llist cs B = true) : BaseFacts G Llist cs B := by
  obtain ⟨hst, h⟩ := c690b_bAnd h
  obtain ⟨htp, h⟩ := c690b_bAnd h
  obtain ⟨hfg, h⟩ := c690b_bAnd h
  obtain ⟨hpg, h⟩ := c690b_bAnd h
  obtain ⟨hfc, h⟩ := c690b_bAnd h
  obtain ⟨hLG, h⟩ := c690b_bAnd h
  obtain ⟨hcs, h⟩ := c690b_bAnd h
  obtain ⟨hord, hcand⟩ := c690b_bAnd h
  have hfc' := Nat.eq_of_beq_eq_true hfc
  have hLG' := Nat.eq_of_beq_eq_true hLG
  have hcs' := Nat.eq_of_beq_eq_true hcs
  rw [lenS_eq] at hfc' hLG' hcs'
  rw [lenS_eq] at hLG' hcs'
  obtain ⟨hl, hlt, hfirst⟩ := fcS_sound _ _ _ hord
  exact ⟨stabS_sound hst, tpS_sound htp, fgS_sound hfg, pglcS_sound hpg, hfc',
    hl.symm.trans hfc', fun g hg => hlt g (by omega), fun c hc => by
      obtain ⟨g, hg, h1, h2⟩ := hfirst c (by omega)
      exact ⟨g, by omega, h1, h2⟩,
    hLG', hcs', candZ_sound hcand⟩

theorem bindS_sound {minus : Bool} {B : SBase} (h : bindS minus B = true) :
    B.og = CFSG.GF2Type.Smith1979W3.Cert690.oGensC minus ∧
      B.omg = CFSG.GF2Type.Smith1979W3.Cert690.omegaGensC minus ∧
      B.kpg = CFSG.GF2Type.Smith1979W3.Cert690.kPGLGens ∧ B.pglOK = !minus ∧
      B.nS * B.sing.length = if minus then 51840 else 40320 := by
  unfold bindS at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

end CFSG.KC.C690S

end
