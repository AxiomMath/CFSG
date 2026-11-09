module

public import CFSG.Certificates.Kernel.BfsPinSeedSound
public import CFSG.Certificates.Kernel.PGrpMul
public import CFSG.Sporadic.Schreier.PairWords
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (permOfArr rep_compA rep_idA Rep.apply)
open CFSG.Sporadic.Schreier (BaseFaithful)
open CFSG.KLie.CT (fget)

theorem genStepB_edge {n w m : Nat} {ps : List Nat} {T : Nat → Nat} {t row g k c : Nat}
    (h0 : genStepB n w m ps T t row g k c ≠ 0) :
    c ≤ genStepB n w m ps T t row g k c ∧ ∃ j < genStepB n w m ps T t row g k c,
      keyK n w ps (T j) = keyM n w m ps g t ∨ T j = pcomp n w m g t := by
  have hv := genStepB_eq n w m ps T t row g k c
  generalize genStepB n w m ps T t row g k c = r at h0 hv ⊢
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hv
    exact absurd hv h0
  simp only [h1, ↓reduceIte] at hv
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hv
    by_cases h3 : keyK n w ps (T (fget row k 16)) = keyM n w m ps g t
    · simp only [h3, ↓reduceIte] at hv
      subst hv
      exact ⟨le_refl _, _, h2, Or.inl h3⟩
    · simp only [h3, ↓reduceIte] at hv
      exact absurd hv h0
  · simp only [h2, ↓reduceIte] at hv
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w m g t
      · simp only [h4, h5, ↓reduceIte] at hv
        subst hv
        exact ⟨by omega, c, by omega, Or.inr h5⟩
      · simp only [h4, h5, ↓reduceIte] at hv
        exact absurd hv h0
    · simp only [h4, ↓reduceIte] at hv
      exact absurd hv h0

section Edges

variable {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat}

theorem fold_edges (i : Nat) : ∀ (L : List Nat) (c : Nat),
    L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c ≠ 0 →
    c ≤ L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c ∧
    ∀ k ∈ L, ∃ j < L.foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c,
      keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i)
  | [], _, _ => ⟨le_refl _, fun _ hk => absurd hk List.not_mem_nil⟩
  | k :: L, c, h0 => by
    rw [List.foldl_cons] at h0 ⊢
    have h1 : genStepB n w m ps T (T i) (E i) (G k) k c ≠ 0 := fun e => h0 (by
      rw [e]
      exact foldl_genStepB_zero i L)
    obtain ⟨hle1, j, hj, e⟩ := genStepB_edge h1
    obtain ⟨hle2, hL⟩ := fold_edges i L _ h0
    refine ⟨le_trans hle1 hle2, fun k' hk' => ?_⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact ⟨j, lt_of_lt_of_le hj hle2, e⟩
    · exact hL k' hk'

theorem point_edges {i c : Nat} (h0 : pointStepB n w m ng ps G T E i c ≠ 0) :
    c ≤ pointStepB n w m ng ps G T E i c ∧ ∀ k < ng, ∃ j < pointStepB n w m ng ps G T E i c,
      keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i) := by
  rw [pointStepB_foldlS] at h0 ⊢
  obtain ⟨hle, h⟩ := fold_edges i (List.range ng) c h0
  exact ⟨hle, fun k hk => h k (List.mem_range.2 hk)⟩

theorem run_edges : ∀ len lo c, (∀ i < lo, ∀ k < ng, ∃ j < c,
      keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i)) →
    runFB n w m ng ps G T E len lo c ≠ 0 →
    c ≤ runFB n w m ng ps G T E len lo c ∧ ∀ i < lo + len, ∀ k < ng,
      ∃ j < runFB n w m ng ps G T E len lo c,
        keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i)
  | 0, _, c, hc, _ => ⟨Nat.le_refl c, fun i hi k hk => hc i (by omega) k hk⟩
  | len + 1, lo, c, hc, h => by
    rw [runFB_succ] at h ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h
      exact absurd (runFB_zero len _) h
    · rw [hb] at h
      have hp : pointStepB n w m ng ps G T E lo c ≠ 0 := fun e => by
        change runFB n w m ng ps G T E len (Nat.succ lo) (pointStepB n w m ng ps G T E lo c) ≠ 0
          at h
        rw [e, runFB_zero] at h
        exact h rfl
      obtain ⟨hle1, hpt⟩ := point_edges hp
      have hc' : ∀ i < Nat.succ lo, ∀ k < ng, ∃ j < pointStepB n w m ng ps G T E lo c,
          keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i) := by
        intro i hi k hk
        rcases Nat.lt_or_ge i lo with h' | h'
        · obtain ⟨j, hj, e⟩ := hc i h' k hk
          exact ⟨j, lt_of_lt_of_le hj hle1, e⟩
        · have e : i = lo := by omega
          subst e
          exact hpt k hk
      have hr := run_edges len (Nat.succ lo) _ hc' h
      exact ⟨le_trans hle1 hr.1, fun i hi k hk => hr.2 i (by omega) k hk⟩

theorem runFB_edges {N : Nat} (hR : runFB n w m ng ps G T E N 0 1 = N) (hN : N ≠ 0) :
    ∀ i < N, ∀ k < ng, ∃ j < N,
      keyK n w ps (T j) = keyM n w m ps (G k) (T i) ∨ T j = pcomp n w m (G k) (T i) := by
  have h := run_edges N 0 1 (fun i hi => absurd hi (Nat.not_lt_zero i)) (by rw [hR]; exact hN)
  rw [hR] at h
  intro i hi k hk
  exact h.2 i (by omega) k hk

end Edges

theorem ofDigits_map_eq {n : Nat} {f g : Nat → Nat} : ∀ (ps : List Nat),
    (∀ p ∈ ps, f p < n) → (∀ p ∈ ps, g p < n) →
    Nat.ofDigits n (ps.map f) = Nat.ofDigits n (ps.map g) → ∀ p ∈ ps, f p = g p
  | [], _, _, _ => fun _ hp => absurd hp List.not_mem_nil
  | q :: ps, hf, hg, h => by
    simp only [List.map_cons, Nat.ofDigits_cons] at h
    have hfq := hf q List.mem_cons_self
    have hgq := hg q List.mem_cons_self
    have e1 : f q = g q := by
      have := congrArg (· % n) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfq, Nat.mod_eq_of_lt hgq] at this
      exact this
    have e2 : Nat.ofDigits n (ps.map f) = Nat.ofDigits n (ps.map g) := by
      rw [e1] at h
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact e1
    · exact ofDigits_map_eq ps (fun p hp => hf p (List.mem_cons_of_mem q hp))
        (fun p hp => hg p (List.mem_cons_of_mem q hp)) e2 p hp

theorem runFB_of_runSlB {n w ng : Nat} {ps : List Nat} {N L K : Nat} {G T E C : Nat → Nat}
    (hN : N = L * K) (hC0 : C 0 = 1) (hCK : C K = N)
    (hr : ∀ s < K, runSlB n w ng ps G T E L C s = true) :
    runFB n w (mask w) ng ps G T E N 0 1 = N := by
  have h := runFB_blocks L C K hr
  rw [hC0, hCK, ← hN] at h
  exact h

theorem eq_of_keyK {n w : Nat} {ps : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
    (hF : BaseFaithful H ps) (hps : ∀ p ∈ ps, p < n) (hsz : szOK n w = true) {a b : Nat} (ha : permB n w a = true)
    (hb : permB n w b = true) (haH : permOfArr n (unpack n w a) ∈ H)
    (hbH : permOfArr n (unpack n w b) ∈ H) (e : keyK n w ps a = keyK n w ps b) : a = b := by
  have hra := rep_of_validA (validA_unpack ha)
  have hrb := rep_of_validA (validA_unpack hb)
  have hk : keyA n ps (unpack n w a) = keyA n ps (unpack n w b) := by
    rw [keyA_unpack hps, keyA_unpack hps]
    exact e
  have hpt := ofDigits_map_eq ps (fun p hp => by rw [hra.apply (hps p hp)]; exact Fin.isLt _)
    (fun p hp => by rw [hrb.apply (hps p hp)]; exact Fin.isLt _) hk
  have hfix : permOfArr n (unpack n w b) = permOfArr n (unpack n w a) := by
    have h1 := hF _ (H.mul_mem (H.inv_mem hbH) haH) fun x hx => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [← hrb.apply x.isLt, ← hra.apply x.isLt]
      exact hpt x hx
    exact inv_mul_eq_one.1 h1
  obtain ⟨-, hw, ha0, -⟩ := PF.canon_facts (pp_of_permB hsz ha).1
  obtain ⟨-, -, hb0, -⟩ := PF.canon_facts (pp_of_permB hsz hb).1
  refine PF.eq_of_fields (PF.w_pos hw) ha0 hb0 fun i hi => ?_
  rw [← unpack_get' hi, ← unpack_get' hi, hra.apply hi, hrb.apply hi, hfix]

theorem enum_of_runFB {n w ng N fuel : Nat} {G T E : Nat → Nat} {SK ps : List Nat}
    {gs : Array (Array Nat)} {H : Subgroup (Equiv.Perm (Fin n))} (hsz : szOK n w = true)
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permB n w (G k) = true) (hH : ∀ k < ng, permOfArr n (unpack n w (G k)) ∈ H)
    (hF : BaseFaithful H ps) (hps : ∀ p ∈ ps, p < n) (hT0 : T 0 = pidn n w)
    (hK : keysSK n w ps N T SK = true) (hR : runFB n w (mask w) ng ps G T E N 0 1 = N)
    (hf : N ≤ fuel) :
    (enumOK n gs ps (enumBfs n gs ps fuel) = true ∧ (enumBfs n gs ps fuel).pts.size = N ∧
      ∀ i < N, (enumBfs n gs ps fuel).pts[i]! = unpack n w (T i)) ∧
      ∀ i < N, permB n w (T i) = true := by
  have hN : N ≠ 0 := by
    intro e
    subst e
    have e1 : runFB n w (mask w) ng ps G T E 0 0 1 = 1 := rfl
    omega
  have hP : ∀ j < N, permB n w (T j) = true ∧ permOfArr n (unpack n w (T j)) ∈ H :=
    runFB_points (P := fun j => permB n w (T j) = true ∧ permOfArr n (unpack n w (T j)) ∈ H)
      (by
        rw [hT0]
        refine ⟨permB_of_pp (PP.id hsz), ?_⟩
        rw [← idA_eq hsz, permOfArr_eq_of_rep rep_idA]
        exact H.one_mem)
      (fun i c k _ hk hi e => by
        rw [e]
        refine ⟨CFSG.KC.PGrp.permB_pcomp hsz (hp k hk) hi.1, ?_⟩
        rw [CFSG.KC.PGrp.permOfArr_pcomp hsz (hp k hk) hi.1]
        exact H.mul_mem (hH k hk) hi.2) hR hN
  have hcG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := fun k hk =>
    (pp_of_permB hsz (hp k hk)).1
  have hcT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := fun i hi =>
    (pp_of_permB hsz (hP i hi).1).1
  have hn32 : n < 2 ^ 32 := by
    have := (szOK_facts' hsz).1
    omega
  have hcl : ∀ k < ng, ∀ i < N, ∃ j < N, pcomp n w (mask w) (G k) (T i) = T j := by
    intro k hk i hi
    obtain ⟨j, hj, e⟩ := runFB_edges hR hN i hi k hk
    refine ⟨j, hj, ?_⟩
    rcases e with e | e
    · rw [keyM_eq hn32 hps] at e
      refine eq_of_keyK hF hps hsz (CFSG.KC.PGrp.permB_pcomp hsz (hp k hk) (hP i hi).1) (hP j hj).1
        ?_ (hP j hj).2 e.symm
      rw [CFSG.KC.PGrp.permOfArr_pcomp hsz (hp k hk) (hP i hi).1]
      exact H.mul_mem (hH k hk) (hP i hi).2
    · exact e.symm
  have hpts := enumBfs_pts_key hs hg hsz hcG hcT hT0 hps hK hR hf
  refine ⟨⟨enumOK_of_cl hs hg hsz hp hcG hcT hT0 hps hK hR hf hcl, by rw [hpts]; simp,
    fun i hi => ?_⟩, fun i hi => (hP i hi).1⟩
  rw [hpts, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

end CFSG.KC.BfsPin

end
