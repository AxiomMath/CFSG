module

public import Certificates.Data.Kernel.TwistDce3.RelsNet
public import CFSG.Certificates.Kernel.TwistDce3.CoverNetSound

public section

namespace CFSG.Certificates.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange
open CFSG.KC.TwDce3 CFSG.KC.YModel
open CFSG.Certificates.TwDce.Words (sB_eq sN_eq)
open CFSG.Certificates.TwDce3.Words (evP_eq lst_eq digs_succ land15 shr4)
open CFSG.Certificates.TwDce2.Words (kandB_iff)

section
variable {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {NS : ℕ → ℕ} {K NL NP : ℕ}

noncomputable def psiL (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (l : List ℕ) (r : ℕ) : ℕ :=
  l.foldr (fun c y => fieldAt PB (F (ivL INVM c)) y) r

theorem psiL_lt (hN : NetFacts PB F INVM NS K NL NP) :
    ∀ (l : List ℕ), (∀ c ∈ l, c < NL) → ∀ r < NP, psiL PB F INVM l r < NP
  | [], _, r, hr => hr
  | c :: l, hl, r, hr => by
    have hc := hl c List.mem_cons_self
    have ih := psiL_lt hN l (fun d hd => hl d (List.mem_cons_of_mem _ hd)) r hr
    exact ((hN.tab _ (hN.tab c hc).1).2 _ ih).1

theorem foldl_psiL (hN : NetFacts PB F INVM NS K NL NP) :
    ∀ (l : List ℕ), (∀ c ∈ l, c < NL) → ∀ r < NP,
      l.foldl (fun p c => fieldAt PB (F c) p) (psiL PB F INVM l r) = r
  | [], _, r, _ => rfl
  | c :: l, hl, r, hr => by
    have hc := hl c List.mem_cons_self
    have hl' : ∀ d ∈ l, d < NL := fun d hd => hl d (List.mem_cons_of_mem _ hd)
    have hy := psiL_lt hN l hl' r hr
    have e := ((hN.tab _ (hN.tab c hc).1).2 _ hy).2
    rw [hN.inv c hc] at e
    change l.foldl _ (fieldAt PB (F c) (fieldAt PB (F (ivL INVM c)) (psiL PB F INVM l r))) = r
    rw [e]
    exact foldl_psiL hN l hl' r hr

theorem wPlN_sound (hN : NetFacts PB F INVM NS K NL NP) {P : ℕ} : ∀ n s X,
    (∀ i < n, s / 16 ^ i % 16 < NL) → ∀ u < P, ∀ r < NP,
      (wPlN INVM NS K P n s X).testBit (2 ^ K * u + r) =
        X.testBit (2 ^ K * u + psiL PB F INVM ((List.range n).map (fun i => s / 16 ^ i % 16)) r)
  | 0, s, X, _, u, _, r, _ => rfl
  | n + 1, s, X, hs, u, hu, r, hr => by
    have hc : s % 16 < NL := by simpa using hs 0 (by omega)
    have hc' := (hN.tab _ hc).1
    have hs' : ∀ i < n, s / 16 / 16 ^ i % 16 < NL := by
      intro i hi
      have := hs (i + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
    have hl' : ∀ c ∈ (List.range n).map (fun i => s / 16 / 16 ^ i % 16), c < NL := by
      intro c hcm
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcm
      exact hs' i (List.mem_range.1 hi)
    obtain ⟨hv, hp⟩ := hN.net _ hc'
    have hnp := hN.np
    have e0 : wPlN INVM NS K P (n + 1) s X = wPlN INVM NS K P n (s / 16)
        (CFSG.KC.MonsterConv.Perm.netApply K (2 ^ K) (CFSG.KC.MonsterConv.Perm.repU (2 ^ K) P)
          (NS (ivL INVM (s % 16))) X) := by
      simp only [wPlN, Nat.rec_add_one, sN_eq]
      rw [land15, shr4, shlK]
    have hy := psiL_lt hN _ hl' r hr
    rw [e0, wPlN_sound hN n (s / 16)
      (CFSG.KC.MonsterConv.Perm.netApply K (2 ^ K) (CFSG.KC.MonsterConv.Perm.repU (2 ^ K) P)
          (NS (ivL INVM (s % 16))) X) hs' u hu r hr,
      (CFSG.KC.Benes.testBit_netApply rfl hv X).1 u hu _ (by omega), hp _ hy, digs_succ]
    rfl

theorem relsN_sound (hN : NetFacts PB F INVM NS K NL NP) (hNL : 12 ≤ NL) :
    ∀ {ws : List (List ℕ)}, relsN INVM NS K ws = true → (∀ w ∈ ws, w.length < 2 ^ 32) →
    ∀ w ∈ ws, (∀ c ∈ w, c < 12) ∧ ∀ p < NP, w.foldl (fun q c => fieldAt PB (F c) q) p = p
  | [], _, _ => fun _ hw => absurd hw List.not_mem_nil
  | w :: ws, h, hl => by
    change andB (andB (codesOK w) (sB (codesW w) (fun v => wIdN INVM NS K v)))
      (relsN INVM NS K ws) = true at h
    rw [kandB_iff, kandB_iff, sB_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · have hc := CFSG.Certificates.TwDce2.Rels.codesOK_sound h1
      obtain ⟨hlen, -, hlst⟩ := CFSG.Certificates.TwDce2.Rels.codesW_spec v
        (fun c hc' => by have := hc c hc'; omega) (hl v List.mem_cons_self)
      refine ⟨hc, fun p hp => ?_⟩
      have hd : ((List.range (wLen (codesW v))).map (fun i => wStr (codesW v) / 16 ^ i % 16)) = v := by
        rw [← lst_eq, hlst]
      have hs : ∀ i < wLen (codesW v), wStr (codesW v) / 16 ^ i % 16 < NL := by
        intro i hi
        have hm : wStr (codesW v) / 16 ^ i % 16 ∈
            (List.range (wLen (codesW v))).map (fun i => wStr (codesW v) / 16 ^ i % 16) :=
          List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
        rw [hd] at hm
        have := hc _ hm
        omega
      have hvl : ∀ c ∈ v, c < NL := fun c hcv => by have := hc c hcv; omega
      have hnp := hN.np
      have hpsi : psiL PB F INVM v p = p := by
        have hy := psiL_lt hN v hvl p hp
        apply CFSG.KC.YModel.Sem.eq_of_bits (k := K) (by omega) (by omega)
        intro u hu
        have e : (wPlN INVM NS K K (wLen (codesW v)) (wStr (codesW v))
            (CFSG.KC.MonsterConv.Perm.idP K)).testBit (2 ^ K * u + p) =
            (CFSG.KC.MonsterConv.Perm.idP K).testBit (2 ^ K * u + p) := by
          rw [Nat.eq_of_beq_eq_true h2]
        rw [wPlN_sound hN _ _ (CFSG.KC.MonsterConv.Perm.idP K) hs u hu p hp, hd,
          CFSG.KC.YModel.Sem.testBit_idP (r := psiL PB F INVM v p) hu (by omega),
          CFSG.KC.YModel.Sem.testBit_idP (r := p) hu (by omega)] at e
        exact e
      have := foldl_psiL hN v hvl p hp
      rwa [hpsi] at this
    · exact relsN_sound hN hNL h3 (fun u hu => hl u (List.mem_cons_of_mem _ hu)) v hv

end

theorem brec_true {a b : Bool} (ha : a = true) (hb : b = true) : (Bool.rec false b a : Bool) = true := by
  subst ha
  exact hb

theorem codesOK_of : ∀ w : List ℕ, (∀ c ∈ w, c < 12) → codesOK w = true
  | [], _ => rfl
  | c :: w, h => brec_true (by rw [Nat.blt_eq]; exact h c List.mem_cons_self)
      (codesOK_of w fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem fixLoop_of {PB : ℕ} {F : ℕ → ℕ} (v : ℕ) : ∀ n, (∀ x < n, evP PB F v x = x) →
    (Nat.rec (motive := fun _ => Bool) true
      (fun x acc => andB acc (Nat.beq (evP PB F v x) x)) n) = true
  | 0, _ => rfl
  | n + 1, h => brec_true (fixLoop_of v n fun x hx => h x (by omega))
      (by rw [h n (by omega), Nat.beq_eq])

theorem relsOK_of {PB : ℕ} {F : ℕ → ℕ} {NP : ℕ} : ∀ ws : List (List ℕ),
    (∀ w ∈ ws, w.length < 2 ^ 32) →
    (∀ w ∈ ws, (∀ c ∈ w, c < 12) ∧ ∀ p < NP, w.foldl (fun q c => fieldAt PB (F c) q) p = p) →
    relsOK PB F NP ws = true
  | [], _, _ => rfl
  | w :: ws, hl, h => by
    obtain ⟨hc, hf⟩ := h w List.mem_cons_self
    obtain ⟨-, -, hlst⟩ := CFSG.Certificates.TwDce2.Rels.codesW_spec w
      (fun c hc' => by have := hc c hc'; omega) (hl w List.mem_cons_self)
    refine brec_true (brec_true (codesOK_of w hc) ?_)
      (relsOK_of ws (fun u hu => hl u (List.mem_cons_of_mem _ hu))
        (fun u hu => h u (List.mem_cons_of_mem _ hu)))
    rw [sB_eq]
    exact fixLoop_of (codesW w) NP fun x hx => by
      rw [evP_eq, hlst]
      exact hf x hx

end CFSG.Certificates.TwDce3

end
