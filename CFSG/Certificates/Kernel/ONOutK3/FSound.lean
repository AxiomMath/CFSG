module

public import CFSG.Certificates.Kernel.ONOutK3.NodeSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.ONOutK3.F

public section

namespace CFSG.KS.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ComponentClassification.SolMax.ONOut

@[expose] noncomputable def TF (FL j : Nat) : Pt3 := (tA (fRec FL j), tB (fRec FL j), tC (fRec FL j))

@[expose] noncomputable def fStepK (G : Nat → Nat → Nat) (l : Nat) (t : Pt3) : Pt3 := map3 (fG G l) t

theorem key3_eq (a b c : Nat) : key3 a b c = a + 2 ^ 18 * b + 2 ^ 36 * c := by
  unfold key3
  change a + (b * 262144 + c * 68719476736) = _
  omega

theorem key3_inj {a b c r : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) (hc : c < 2 ^ 18)
    (h : key3 a b c = tK r) : a = tA r ∧ b = tB r ∧ c = tC r := by
  rw [key3_eq, tK_eq] at h
  rw [tA_eq, tB_eq, tC_eq]
  omega

theorem key3_tK (r : Nat) : key3 (tA r) (tB r) (tC r) = tK r := by
  rw [key3_eq, tK_split]

theorem mapK_eq {g : Nat → Nat} {t r : Nat} (hA : g (tA t) < 2 ^ 18) (hB : g (tB t) < 2 ^ 18)
    (hC : g (tC t) < 2 ^ 18) (h : mapK g t = tK r) :
    g (tA t) = tA r ∧ g (tB t) = tB r ∧ g (tC t) = tC r :=
  key3_inj hA hB hC h

theorem NP_lt : NP < 2 ^ 18 := by decide

structure FAt (G : Nat → Nat → Nat) (FL FK j : Nat) : Prop where
  ltA : tA (fRec FL j) < NP
  ltB : tB (fRec FL j) < NP
  ltC : tC (fRec FL j) < NP
  close : ∀ l < 2, fClose G FL j (fRec FL j) l = true
  root : j = 0 → tK (fRec FL j) = BK ∧ fPar (fRec FL j) = 0 ∧ fLab (fRec FL j) = 0
  tree : j ≠ 0 → fPar (fRec FL j) < j ∧ fLab (fRec FL j) < 2 ∧
    fPos (fRec FL (fPar (fRec FL j))) (fLab (fRec FL j)) = j
  order : j ≠ 0 → j + 1 < 60 →
    lexB (fPar (fRec FL j)) (fLab (fRec FL j)) (fPar (fRec FL (j + 1))) (fLab (fRec FL (j + 1))) = true
  dist : ∀ i < j, tK (fRec FL i) ≠ tK (fRec FL j)
  fk : fld(FK, Nat.mul 54 j, M54) = tK (fRec FL j)
  fkz : fld(FK, Nat.mul 54 (Nat.add 60 j), M54) = mapK (G 0) (fRec FL j)
  noz : tK (fRec FL j) ≠ mapK (G 0) BK

theorem fAt_of {G : Nat → Nat → Nat} {FL FK j : Nat} (h : fNode G FL FK j = true) : FAt G FL FK j := by
  unfold fNode at h
  rw [sB] at h
  obtain ⟨hA, h⟩ := band_t h
  obtain ⟨hB, h⟩ := band_t h
  obtain ⟨hC, h⟩ := band_t h
  obtain ⟨c0, h⟩ := band_t h
  obtain ⟨c1, h⟩ := band_t h
  obtain ⟨ht, h⟩ := band_t h
  obtain ⟨ho, h⟩ := band_t h
  obtain ⟨hd, h⟩ := band_t h
  obtain ⟨k1, h⟩ := band_t h
  obtain ⟨k2, hz⟩ := band_t h
  refine ⟨bltT hA, bltT hB, bltT hC, fun l hl => ?_, fun e => ?_, fun e => ?_, fun e he => ?_,
    fun i hi e => ?_, beqT k1, beqT k2, fun e => ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> assumption
  · have h0 := (bif_t ht).1 (beqTr e)
    obtain ⟨a1, h0⟩ := band_t h0
    obtain ⟨a2, a3⟩ := band_t h0
    exact ⟨beqT a1, beqT a2, beqT a3⟩
  · have h1 := (bif_t ht).2 (beqF e)
    rw [sB, sB] at h1
    obtain ⟨a1, h1⟩ := band_t h1
    obtain ⟨a2, a3⟩ := band_t h1
    exact ⟨bltT a1, bltT a2, beqT a3⟩
  · have h1 := (bif_t ho).2 (beqF e)
    have h2 := (bif_t h1).1 (bltTr he)
    rw [sB] at h2
    exact h2
  · have := (bif_t (allN_spec hd i hi)).1 (beqTr e)
    exact Bool.false_ne_true this
  · have := (bif_t hz).1 (beqTr e)
    exact Bool.false_ne_true this

theorem fClose_spec {G : Nat → Nat → Nat} {FL j r l : Nat} (h : fClose G FL j r l = true)
    (hA : fG G l (tA r) < 2 ^ 18) (hB : fG G l (tB r) < 2 ^ 18) (hC : fG G l (tC r) < 2 ^ 18) :
    fPos r l < 60 ∧ fStepK G l (tA r, tB r, tC r) = TF FL (fPos r l) ∧
      (fPos r l = 0 ∨ fPar (fRec FL (fPos r l)) < j ∨
        (fPar (fRec FL (fPos r l)) = j ∧ fLab (fRec FL (fPos r l)) ≤ l)) := by
  unfold fClose at h
  rw [sB, sB] at h
  obtain ⟨h1, h⟩ := band_t h
  obtain ⟨h2, h3⟩ := band_t h
  obtain ⟨e1, e2, e3⟩ := mapK_eq hA hB hC (beqT h2)
  refine ⟨bltT h1, ?_, ?_⟩
  · unfold fStepK map3 TF
    rw [e1, e2, e3]
  · by_cases e0 : fPos r l = 0
    · exact Or.inl e0
    · have := (bif_t h3).2 (beqF e0)
      by_cases e4 : fPar (fRec FL (fPos r l)) < j
      · exact Or.inr (Or.inl e4)
      · obtain ⟨a, b⟩ := band_t ((bif_t this).2 (bltF e4))
        exact Or.inr (Or.inr ⟨beqT a, bleT b⟩)

theorem f_replay {G : Nat → Nat → Nat} {FL FK : Nat} (h : fAll G FL FK = true)
    (hG : ∀ j < 60, ∀ l < 2, fG G l (tA (fRec FL j)) < 2 ^ 18 ∧ fG G l (tB (fRec FL j)) < 2 ^ 18 ∧
      fG G l (tC (fRec FL j)) < 2 ^ 18) :
    R3 (fStepK G) 2 base3 60 (TF FL) (fun j => fPar (fRec FL j)) (fun j => fLab (fRec FL j))
      (fun j l => fPos (fRec FL j) l) := by
  have hF : ∀ j < 60, FAt G FL FK j := fun j hj => fAt_of (allN_spec h j hj)
  have h0 := (hF 0 (by decide)).root rfl
  have hcl : ∀ j < 60, ∀ l < 2, _ := fun j hj l hl =>
    fClose_spec ((hF j hj).close l hl) (hG j hj l hl).1 (hG j hj l hl).2.1 (hG j hj l hl).2.2
  refine ⟨by decide, BK_triple h0.1, h0.2.1, h0.2.2, fun a ha b hb e => ?_, fun i hi0 hi => ?_,
    fun i hi0 hi => ?_, fun j hj l hl => ?_⟩
  · have ek : tK (fRec FL a) = tK (fRec FL b) := by
      unfold TF at e
      simp only [Prod.mk.injEq] at e
      rw [tK_split, tK_split, e.1, e.2.1, e.2.2]
    rcases Nat.lt_trichotomy a b with h1 | h1 | h1
    · exact absurd ek ((hF b hb).dist a h1)
    · exact h1
    · exact absurd ek.symm ((hF a ha).dist b h1)
  · obtain ⟨t1, t2, t3⟩ := (hF i hi).tree (by omega)
    refine ⟨t1, t2, ?_⟩
    have := (hcl (fPar (fRec FL i)) (by omega) _ t2).2.1
    rw [t3] at this
    exact this.symm
  · have := (hF i (by omega)).order (by omega) hi
    unfold lexB at this
    unfold LexLt
    by_cases e : fPar (fRec FL i) < fPar (fRec FL (i + 1))
    · exact Or.inl e
    · obtain ⟨a, b⟩ := band_t ((bif_t this).2 (bltF e))
      exact Or.inr ⟨beqT a, bltT b⟩
  · obtain ⟨p1, p2, p3⟩ := hcl j hj l hl
    refine ⟨p1, p2, ?_⟩
    rcases p3 with e | e | ⟨e1, e2⟩
    · exact Or.inl e
    · right
      unfold LexLt
      omega
    · right
      unfold LexLt
      omega

theorem f_facts {G : Nat → Nat → Nat} {FL FK : Nat} (h : fAll G FL FK = true) {j : Nat} (hj : j < 60) :
    FAt G FL FK j := fAt_of (allN_spec h j hj)

end CFSG.KS.ONK3

end
