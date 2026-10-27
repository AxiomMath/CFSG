module

public import Certificates.Data.FzL410Norm
public import Certificates.Data.Kernel.FzL410.Codes
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace CFSG.FzL410K

open Certificates.FzL410 Certificates.FzL410.K

def e1 : A := (1, 0, 0, 0)
def e2 : A := (0, 1, 0, 0)
def r1 : A := (0, 0, 1, 0)
def r2 : A := (0, 0, 0, 1)

def enc (p : A) : ℕ := p.1.val + 256 * p.2.1.val + 65536 * p.2.2.1.val + 16777216 * p.2.2.2.val

def dec (k : ℕ) : A := ((k : ZMod 4), ((k / 4 : ℕ) : ZMod 4), ((k / 16 : ℕ) : ZMod 2), ((k / 32 : ℕ) : ZMod 2))

def cmp (p : A) : ℕ := p.1.val + 4 * p.2.1.val + 16 * p.2.2.1.val + 32 * p.2.2.2.val

theorem cmp_lt : ∀ p : A, cmp p < 64 := by decide

theorem dec_cmp : ∀ p : A, dec (cmp p) = p := by decide

theorem cmp_dec : ∀ k, k < 64 → cmp (dec k) = k := by decide

theorem nA (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nM (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nD (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nMod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem spr_eq (k : ℕ) : spr k = enc (dec k) := by
  simp only [spr, enc, dec, ZMod.val_natCast, nA, nM, nD, nMod]
  omega

theorem spr_cmp (p : A) : spr (cmp p) = enc p := by rw [spr_eq, dec_cmp]

theorem enc_lt (p : A) : enc p < 33554432 := by
  have := ZMod.val_lt p.1
  have := ZMod.val_lt p.2.1
  have := ZMod.val_lt p.2.2.1
  have := ZMod.val_lt p.2.2.2
  simp only [enc]
  omega

theorem enc_inj {p q : A} (h : enc p = enc q) : p = q := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c', d'⟩ := q
  simp only [enc] at h
  have := ZMod.val_lt a
  have := ZMod.val_lt b
  have := ZMod.val_lt c
  have := ZMod.val_lt d
  have := ZMod.val_lt a'
  have := ZMod.val_lt b'
  have := ZMod.val_lt c'
  have := ZMod.val_lt d'
  have h1 : a.val = a'.val := by omega
  have h2 : b.val = b'.val := by omega
  have h3 : c.val = c'.val := by omega
  have h4 : d.val = d'.val := by omega
  rw [ZMod.val_injective _ h1, ZMod.val_injective _ h2, ZMod.val_injective _ h3,
    ZMod.val_injective _ h4]

theorem enc_eq_iff {p q : A} : enc p = enc q ↔ p = q := ⟨enc_inj, congrArg enc⟩

theorem beq_enc {p q : A} : Nat.beq (enc p) (enc q) = true ↔ p = q := by
  rw [Nat.beq_eq]
  exact enc_eq_iff

theorem val_lin {n : ℕ} [NeZero n] (a b c d : ℕ) (x y z w : ZMod n) :
    (a • x + b • y + c • z + d • w).val = (a * x.val + b * y.val + c * z.val + d * w.val) % n := by
  rw [← ZMod.val_natCast n]
  congr 1
  push_cast
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem mul_le' {x y m n : ℕ} (hx : x < m + 1) (hy : y < n + 1) : x * y ≤ m * n :=
  Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)

theorem nrm_eq {s S1 S2 S3 S4 : ℕ} (hs : s = S1 + 256 * S2 + 65536 * S3 + 16777216 * S4)
    (h1 : S1 < 256) (h2 : S2 < 255) (h3 : S3 < 255) :
    nrm s = S1 % 4 + 256 * (S2 % 4) + 65536 * (S3 % 2) + 16777216 * (S4 % 2) := by
  simp only [nrm, nA, nM, nD, nMod]
  omega

theorem evS_nat {A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 K1 K2 K3 K4 : ℕ}
    (hA1 : A1 < 4) (hB1 : B1 < 4) (hC1 : C1 < 2) (hD1 : D1 < 2)
    (hA2 : A2 < 4) (hB2 : B2 < 4) (hC2 : C2 < 2) (hD2 : D2 < 2)
    (hA3 : A3 < 4) (hB3 : B3 < 4) (hC3 : C3 < 2) (hD3 : D3 < 2)
    (hA4 : A4 < 4) (hB4 : B4 < 4) (hC4 : C4 < 2) (hD4 : D4 < 2)
    (hK1 : K1 < 4) (hK2 : K2 < 4) (hK3 : K3 < 2) (hK4 : K4 < 2) :
    evS (A1 + 256 * B1 + 65536 * C1 + 16777216 * D1) (A2 + 256 * B2 + 65536 * C2 + 16777216 * D2)
      (A3 + 256 * B3 + 65536 * C3 + 16777216 * D3) (A4 + 256 * B4 + 65536 * C4 + 16777216 * D4)
      (K1 + 256 * K2 + 65536 * K3 + 16777216 * K4) =
    (K1 * A1 + K2 * A2 + K3 * A3 + K4 * A4) % 4 + 256 * ((K1 * B1 + K2 * B2 + K3 * B3 + K4 * B4) % 4) +
      65536 * ((K1 * C1 + K2 * C2 + K3 * C3 + K4 * C4) % 2) +
      16777216 * ((K1 * D1 + K2 * D2 + K3 * D3 + K4 * D4) % 2) := by
  have d1 : (K1 + 256 * K2 + 65536 * K3 + 16777216 * K4) % 256 = K1 := by omega
  have d2 : (K1 + 256 * K2 + 65536 * K3 + 16777216 * K4) / 256 % 256 = K2 := by omega
  have d3 : (K1 + 256 * K2 + 65536 * K3 + 16777216 * K4) / 65536 % 256 = K3 := by omega
  have d4 : (K1 + 256 * K2 + 65536 * K3 + 16777216 * K4) / 16777216 = K4 := by omega
  simp only [evS, nA, nM, nD, nMod]
  rw [d1, d2, d3, d4]
  have := mul_le' (m := 3) (n := 3) hK1 hA1
  have := mul_le' (m := 3) (n := 3) hK2 hA2
  have := mul_le' (m := 1) (n := 3) hK3 hA3
  have := mul_le' (m := 1) (n := 3) hK4 hA4
  have := mul_le' (m := 3) (n := 3) hK1 hB1
  have := mul_le' (m := 3) (n := 3) hK2 hB2
  have := mul_le' (m := 1) (n := 3) hK3 hB3
  have := mul_le' (m := 1) (n := 3) hK4 hB4
  have := mul_le' (m := 3) (n := 1) hK1 hC1
  have := mul_le' (m := 3) (n := 1) hK2 hC2
  have := mul_le' (m := 1) (n := 1) hK3 hC3
  have := mul_le' (m := 1) (n := 1) hK4 hC4
  exact nrm_eq (by ring) (by omega) (by omega) (by omega)

theorem enc_ev (g1 g2 g3 g4 p : A) :
    enc (ev g1 g2 g3 g4 p) = evS (enc g1) (enc g2) (enc g3) (enc g4) (enc p) := by
  obtain ⟨a1, b1, c1, d1⟩ := g1
  obtain ⟨a2, b2, c2, d2⟩ := g2
  obtain ⟨a3, b3, c3, d3⟩ := g3
  obtain ⟨a4, b4, c4, d4⟩ := g4
  obtain ⟨k1, k2, k3, k4⟩ := p
  simp only [ev, enc, Prod.smul_mk, Prod.mk_add_mk, val_lin]
  exact (evS_nat (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)).symm

theorem four_smul : ∀ x : A, (4 : ℕ) • x = 0 := by decide

theorem nsmul_mod {x : A} {m : ℕ} (hm : m • x = 0) (n : ℕ) : (n % m) • x = n • x := by
  have h : ∀ q : ℕ, (m * q) • x = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, add_nsmul, ih, hm, add_zero]
  conv_rhs => rw [← Nat.mod_add_div n m, add_nsmul, h, add_zero]

theorem ev_add {g1 g2 g3 g4 : A} (h3 : (2 : ℕ) • g3 = 0) (h4 : (2 : ℕ) • g4 = 0) (x y : A) :
    ev g1 g2 g3 g4 (x + y) = ev g1 g2 g3 g4 x + ev g1 g2 g3 g4 y := by
  simp only [ev, Prod.fst_add, Prod.snd_add, ZMod.val_add, nsmul_mod (four_smul _), nsmul_mod h3,
    nsmul_mod h4, add_nsmul]
  abel

def evH (g1 g2 g3 g4 : A) (h3 : (2 : ℕ) • g3 = 0) (h4 : (2 : ℕ) • g4 = 0) : A →+ A where
  toFun := ev g1 g2 g3 g4
  map_zero' := by simp [ev]
  map_add' := ev_add h3 h4

theorem ev_neg {g1 g2 g3 g4 : A} (h3 : (2 : ℕ) • g3 = 0) (h4 : (2 : ℕ) • g4 = 0) (x : A) :
    ev g1 g2 g3 g4 (-x) = -ev g1 g2 g3 g4 x :=
  map_neg (evH g1 g2 g3 g4 h3 h4) x

def homOf (f : A → A) {g1 g2 g3 g4 : A} (h3 : (2 : ℕ) • g3 = 0) (h4 : (2 : ℕ) • g4 = 0)
    (hf : ∀ p, f p = ev g1 g2 g3 g4 p) : A →+ A where
  toFun := f
  map_zero' := by rw [hf]; exact (evH g1 g2 g3 g4 h3 h4).map_zero
  map_add' x y := by rw [hf, hf, hf]; exact (evH g1 g2 g3 g4 h3 h4).map_add x y

theorem ev_gens : ∀ p : A, ev e1 e2 r1 r2 p = p := by decide

theorem hom_ev (F : A →+ A) (p : A) : F p = ev (F e1) (F e2) (F r1) (F r2) p := by
  conv_lhs => rw [← ev_gens p]
  simp only [ev, map_add, map_nsmul]

theorem ext4 (F G : A →+ A) (h1 : F e1 = G e1) (h2 : F e2 = G e2) (h3 : F r1 = G r1)
    (h4 : F r2 = G r2) : ∀ p, F p = G p := fun p => by
  rw [hom_ev F, hom_ev G, h1, h2, h3, h4]

theorem rho_ev : ∀ p : A, rho p = ev (0, 1, 0, 0) (3, 3, 0, 0) (0, 0, 0, 1) (0, 0, 1, 1) p := by
  decide
theorem tt_ev : ∀ p : A, tt p = ev (1, 0, 0, 0) (0, 1, 0, 0) (2, 0, 1, 0) (0, 2, 0, 1) p := by
  decide
theorem ss_ev : ∀ p : A, ss p = ev (3, 0, 0, 0) (0, 3, 0, 0) (0, 0, 1, 0) (0, 0, 0, 1) p := by
  decide
theorem ll_ev : ∀ p : A, ll p = ev (0, 1, 0, 0) (1, 0, 0, 0) (0, 0, 0, 1) (0, 0, 1, 0) p := by
  decide
theorem neg_ev : ∀ p : A, -p = ev (3, 0, 0, 0) (0, 3, 0, 0) (0, 0, 1, 0) (0, 0, 0, 1) p := by
  decide
theorem dbl_ev : ∀ p : A, (2 : ℕ) • p = ev (2, 0, 0, 0) (0, 2, 0, 0) 0 0 p := by decide

def rhoH : A →+ A := homOf rho (by decide) (by decide) rho_ev
def ttH : A →+ A := homOf tt (by decide) (by decide) tt_ev
def ssH : A →+ A := homOf ss (by decide) (by decide) ss_ev
def llH : A →+ A := homOf ll (by decide) (by decide) ll_ev

theorem rho_two {d : A} (h : (2 : ℕ) • d = 0) : (2 : ℕ) • rho d = 0 := by
  have := map_nsmul rhoH 2 d
  rw [h, map_zero] at this
  exact this.symm

def eqH (c d : A) (h : (2 : ℕ) • d = 0) : A →+ A := evH c (rho c) d (rho d) h (rho_two h)

def anH (c d : A) (h : (2 : ℕ) • d = 0) : A →+ A :=
  evH c (rho (rho c)) d (rho (rho d)) h (rho_two (rho_two h))

def pr (p : A) : A := ev 0 0 r1 r2 p

def prH : A →+ A := evH 0 0 r1 r2 (by decide) (by decide)

theorem evS_enc (a b c d p : A) : evS (enc a) (enc b) (enc c) (enc d) (enc p) = enc (ev a b c d p) :=
  (enc_ev a b c d p).symm

theorem rhoS_enc (p : A) : rhoS (enc p) = enc (rho p) := by rw [rho_ev, enc_ev]; rfl
theorem ttS_enc (p : A) : ttS (enc p) = enc (tt p) := by rw [tt_ev, enc_ev]; rfl
theorem ssS_enc (p : A) : ssS (enc p) = enc (ss p) := by rw [ss_ev, enc_ev]; rfl
theorem llS_enc (p : A) : llS (enc p) = enc (ll p) := by rw [ll_ev, enc_ev]; rfl
theorem negS_enc (p : A) : negS (enc p) = enc (-p) := by rw [neg_ev, enc_ev]; rfl
theorem dblS_enc (p : A) : dblS (enc p) = enc ((2 : ℕ) • p) := by rw [dbl_ev, enc_ev]; rfl
theorem piS_enc (p : A) : piS (enc p) = enc (pr p) := by rw [pr, enc_ev]; rfl

theorem eqS_enc (c d p : A) : eqS (enc c) (enc d) (enc p) = enc (evEq c d p) := by
  simp only [eqS, rhoS_enc, evS_enc, evEq]

theorem anS_enc (c d p : A) : anS (enc c) (enc d) (enc p) = enc (evAn c d p) := by
  simp only [anS, rhoS_enc, evS_enc, evAn]

theorem cE1_eq : cE1 = enc e1 := rfl
theorem cE2_eq : cE2 = enc e2 := rfl
theorem cR1_eq : cR1 = enc r1 := rfl
theorem cR2_eq : cR2 = enc r2 := rfl
theorem cZ_eq : cZ = enc 0 := rfl

theorem bA_iff {a b : Bool} : bA a b = true ↔ a = true ∧ b = true := by cases a <;> simp [bA]
theorem bO_iff {a b : Bool} : bO a b = true ↔ a = true ∨ b = true := by cases a <;> simp [bO]
theorem bI_iff {a b : Bool} : bI a b = true ↔ (a = true → b = true) := by cases a <;> simp [bI]
theorem bN_iff {a : Bool} : bN a = true ↔ ¬a = true := by cases a <;> simp [bN]

theorem allR_iff {f : ℕ → Bool} : ∀ {n : ℕ}, allR n f = true ↔ ∀ k < n, f k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    have e : allR (n + 1) f = bA (f n) (allR n f) := rfl
    rw [e, bA_iff, allR_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact h2 k h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem anyR_iff {f : ℕ → Bool} : ∀ {n : ℕ}, anyR n f = true ↔ ∃ k < n, f k = true
  | 0 => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1 => by
    have e : anyR (n + 1) f = bO (f n) (anyR n f) := rfl
    rw [e, bO_iff, anyR_iff]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact Or.inr ⟨k, hk', h⟩
      · exact Or.inl h

theorem cntR_eq (f : ℕ → Bool) :
    ∀ n, cntR n f = ((Finset.range n).filter (fun k => f k = true)).card
  | 0 => rfl
  | n + 1 => by
    have e : cntR (n + 1) f = Bool.rec 0 1 (f n) + cntR n f := rfl
    rw [e, cntR_eq f n, Finset.range_add_one, Finset.filter_insert]
    cases h : f n
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp only
      omega

theorem anyL_map {α : Type} (φ : α → ℕ) (f : ℕ → Bool) :
    ∀ L : List α, anyL (L.map φ) f = true → ∃ x ∈ L, f (φ x) = true
  | [] => fun h => absurd h Bool.false_ne_true
  | x :: L => fun h => by
    have e : anyL ((x :: L).map φ) f = bO (f (φ x)) (anyL (L.map φ) f) := rfl
    rw [e, bO_iff] at h
    rcases h with h | h
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, h⟩ := anyL_map φ f L h
      exact ⟨y, List.mem_cons_of_mem x hy, h⟩

theorem card_cnt (P : A → Prop) [DecidablePred P] (f : ℕ → Bool)
    (hf : ∀ k, f k = true ↔ P (dec k)) : (Finset.univ.filter P).card = cntR 64 f := by
  rw [cntR_eq]
  symm
  refine Finset.card_bij' (fun k _ => dec k) (fun p _ => cmp p) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hk ⊢
    exact (hf k).1 hk.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨cmp_lt p, (hf _).2 ?_⟩
    rw [dec_cmp]
    exact hp
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact cmp_dec k hk.1
  · intro p _
    exact dec_cmp p

theorem v1_4 : (1 : ZMod 4).val = 1 := rfl
theorem v1_2 : (1 : ZMod 2).val = 1 := rfl

theorem ev_e1 (a b c d : A) : ev a b c d e1 = a := by
  simp only [ev, e1, v1_4, ZMod.val_zero, one_smul, zero_smul, add_zero]
theorem ev_e2 (a b c d : A) : ev a b c d e2 = b := by
  simp only [ev, e2, v1_4, ZMod.val_zero, one_smul, zero_smul, add_zero, zero_add]
theorem ev_r1 (a b c d : A) : ev a b c d r1 = c := by
  simp only [ev, r1, v1_2, ZMod.val_zero, one_smul, zero_smul, add_zero, zero_add]
theorem ev_r2 (a b c d : A) : ev a b c d r2 = d := by
  simp only [ev, r2, v1_2, ZMod.val_zero, one_smul, zero_smul, zero_add]

theorem rho_e1 : rho e1 = e2 := by decide
theorem rho_e2 : rho e2 = -(e1 + e2) := by decide
theorem rho_r1 : rho r1 = r2 := by decide
theorem rho_r2 : rho r2 = r1 + r2 := by decide

theorem r1_two : (2 : ℕ) • r1 = 0 := by decide
theorem e1_two_ne : (2 : ℕ) • e1 ≠ 0 := by decide
theorem pr_two : ∀ z : A, pr ((2 : ℕ) • z) = 0 := by decide
theorem pr_r1 : pr r1 ≠ 0 := by decide
theorem pr_r1_add : pr r1 + pr r1 = 0 := by decide

def hlf (x : A) : A := (((x.1.val / 2 : ℕ) : ZMod 4), ((x.2.1.val / 2 : ℕ) : ZMod 4), 0, 0)

theorem half : ∀ x : A, (2 : ℕ) • x = 0 → pr x = 0 → x = (2 : ℕ) • hlf x := by decide

theorem neg_two_tors {x : A} (h : (2 : ℕ) • x = 0) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_nsmul, h]

theorem inj_crit (hI : normInjB = true) {u v : A} (h1 : (2 : ℕ) • v = 0) (h2 : (2 : ℕ) • u ≠ 0)
    (h3 : (2 : ℕ) • u ≠ (2 : ℕ) • e1) (h4 : pr v ≠ 0) (h5 : pr v ≠ pr r1) (p : A)
    (hp : ev e1 u r1 v p = 0) : p = 0 := by
  simp only [normInjB, allR_iff] at hI
  have h := hI (cmp u) (cmp_lt u) (cmp v) (cmp_lt v)
  rw [spr_cmp, spr_cmp, bI_iff] at h
  have hc : condN (enc u) (enc v) = true := by
    simp only [condN, bA_iff, bN_iff, dblS_enc, piS_enc, cZ_eq, cE1_eq, cR1_eq, beq_enc]
    exact ⟨h1, h2, h3, h4, h5⟩
  have h' := h hc
  simp only [injB, allR_iff, bI_iff, spr_eq, cE1_eq, cR1_eq, cZ_eq, evS_enc, beq_enc] at h'
  have := h' (cmp p) (cmp_lt p)
  rw [dec_cmp] at this
  exact this hp

theorem normSpec (hI : normInjB = true) : NormSpec := by
  unfold NormSpec NormRow IsRho3 ConjRho
  intro g1 g2 g3 h3 g4 h4 hR
  obtain ⟨hc, hfp⟩ := hR
  let σ := evH g1 g2 g3 g4 h3 h4
  have hc' : ∀ x, σ (σ (σ x)) = x := hc
  have hfp' : ∀ x, σ x = x → x = 0 := hfp
  have key : ∀ x, σ (σ x) + σ x + x = 0 := by
    intro x
    apply hfp'
    rw [map_add, map_add, hc']
    abel
  have hinj : ∀ x, σ x = 0 → x = 0 := by
    intro x hx
    rw [← hc' x, hx, map_zero, map_zero]
  have hv2 : (2 : ℕ) • σ r1 = 0 := by rw [← map_nsmul, r1_two, map_zero]
  have hu0 : (2 : ℕ) • σ e1 ≠ 0 := by
    intro h
    rw [← map_nsmul] at h
    exact e1_two_ne (hinj _ h)
  have hu1 : (2 : ℕ) • σ e1 ≠ (2 : ℕ) • e1 := by
    intro h
    rw [← map_nsmul] at h
    exact e1_two_ne (hfp' _ h)
  have hp0 : pr (σ r1) ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ : ∃ y, σ r1 = (2 : ℕ) • y := ⟨_, half _ hv2 h⟩
    apply pr_r1
    have e : r1 = (2 : ℕ) • σ (σ y) := by
      calc r1 = σ (σ (σ r1)) := (hc' r1).symm
        _ = (2 : ℕ) • σ (σ y) := by rw [hy, map_nsmul, map_nsmul]
    rw [e, pr_two]
  have hp1 : pr (σ r1) ≠ pr r1 := by
    intro h
    have hw2 : (2 : ℕ) • (σ r1 + r1) = 0 := by rw [nsmul_add, hv2, r1_two, add_zero]
    have hpw : pr (σ r1 + r1) = 0 := by
      have e : pr (σ r1 + r1) = pr (σ r1) + pr r1 := map_add prH (σ r1) r1
      rw [e, h, pr_r1_add]
    obtain ⟨y, hy⟩ : ∃ y, σ r1 + r1 = (2 : ℕ) • y := ⟨_, half _ hw2 hpw⟩
    have hs : σ r1 = (2 : ℕ) • y - r1 := eq_sub_of_add_eq hy
    have e1' : σ (σ r1) = (2 : ℕ) • σ y - σ r1 := by
      conv_lhs => rw [hs]
      rw [map_sub, map_nsmul]
    have hk : (2 : ℕ) • σ y + r1 = 0 := by
      have := key r1
      rw [e1'] at this
      rw [← this]
      abel
    have e : r1 = -((2 : ℕ) • σ y) := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact hk
    apply pr_r1
    have hn : pr (-((2 : ℕ) • σ y)) = -pr ((2 : ℕ) • σ y) := map_neg prH _
    rw [e, hn, pr_two, neg_zero]
  have hb2 : (2 : ℕ) • (r1 + σ r1) = 0 := by rw [nsmul_add, r1_two, hv2, add_zero]
  refine ⟨e1, r1, r1_two, ?_, fun p hp => inj_crit hI hv2 hu0 hu1 hp0 hp1 p hp⟩
  refine ext4 (σ.comp (evH e1 (σ e1) r1 (σ r1) r1_two hv2))
    ((evH e1 (σ e1) r1 (σ r1) r1_two hv2).comp rhoH) ?_ ?_ ?_ ?_
  · change σ (ev e1 (σ e1) r1 (σ r1) e1) = ev e1 (σ e1) r1 (σ r1) (rho e1)
    rw [ev_e1, rho_e1, ev_e2]
  · change σ (ev e1 (σ e1) r1 (σ r1) e2) = ev e1 (σ e1) r1 (σ r1) (rho e2)
    rw [ev_e2, rho_e2, ev_neg r1_two hv2, ev_add r1_two hv2, ev_e1, ev_e2, eq_neg_iff_add_eq_zero,
      ← key e1]
    abel
  · change σ (ev e1 (σ e1) r1 (σ r1) r1) = ev e1 (σ e1) r1 (σ r1) (rho r1)
    rw [ev_r1, rho_r1, ev_r2]
  · change σ (ev e1 (σ e1) r1 (σ r1) r2) = ev e1 (σ e1) r1 (σ r1) (rho r2)
    rw [ev_r2, rho_r2, ev_add r1_two hv2, ev_r1, ev_r2]
    calc σ (σ r1) = -(r1 + σ r1) := by
          rw [eq_neg_iff_add_eq_zero, ← key r1]
          abel
      _ = r1 + σ r1 := neg_two_tors hb2

theorem fixCnt (c d : A) : cntR 64 (fun k => Nat.beq (eqS (enc c) (enc d) (spr k)) (spr k)) =
    (Finset.univ.filter fun p : A => evEq c d p = p).card := by
  refine (card_cnt _ _ fun k => ?_).symm
  rw [spr_eq, eqS_enc, beq_enc]

theorem fix2Cnt (c d : A) : cntR 64 (fun k => bA (Nat.beq (eqS (enc c) (enc d) (spr k)) (spr k))
    (Nat.beq (dblS (spr k)) cZ)) =
    (Finset.univ.filter fun p : A => evEq c d p = p ∧ (2 : ℕ) • p = 0).card := by
  refine (card_cnt _ _ fun k => ?_).symm
  rw [bA_iff, spr_eq, eqS_enc, beq_enc, dblS_enc, cZ_eq, beq_enc]

theorem isT_twin {c d : A} (h : IsT c d) : isTN (enc c) (enc d) = true := by
  unfold IsT at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [isTN, fixCnt, fix2Cnt]
  simp only [gen4, bA_iff, cE1_eq, cE2_eq, cR1_eq, cR2_eq, cZ_eq, eqS_enc, dblS_enc, beq_enc,
    Nat.beq_eq, enc_eq_iff]
  exact ⟨h0, ⟨h1 _, h1 _, h1 _, h1 _⟩, h2, h3⟩

theorem psiA_of {c d c0 d0 : A} (hd : (2 : ℕ) • d = 0)
    (h : psiAN ttS (enc c) (enc d) (enc c0) (enc d0) = true) : PsiA c d c0 d0 := by
  simp only [psiAN, injS, gen4, bA_iff, bI_iff, allR_iff, spr_eq, cE1_eq, cE2_eq, cR1_eq, cR2_eq,
    cZ_eq, eqS_enc, ttS_enc, rhoS_enc, dblS_enc, beq_enc] at h
  obtain ⟨h0, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, hi⟩ := h
  unfold PsiA
  refine ⟨h0, ext4 ((eqH c0 d0 h0).comp (eqH c d hd)) (ttH.comp (eqH c0 d0 h0)) a1 a2 a3 a4,
    ext4 ((eqH c0 d0 h0).comp rhoH) (rhoH.comp (eqH c0 d0 h0)) b1 b2 b3 b4, fun p hp => ?_⟩
  have := hi (cmp p) (cmp_lt p)
  rw [dec_cmp] at this
  exact this hp

theorem stageA_of (h : stageAB = true) : StageA := by
  unfold StageA RowA
  intro c d hT
  simp only [stageAB, stageAT, allR_iff] at h
  have h2 := h (cmp c) (cmp_lt c) (cmp d) (cmp_lt d)
  rw [spr_cmp, spr_cmp, rowAN, bI_iff] at h2
  obtain ⟨i, -, h3⟩ := anyR_iff.1 (h2 (isT_twin hT))
  obtain ⟨j, -, h4⟩ := anyR_iff.1 h3
  simp only [spr_eq] at h4
  exact ⟨dec i, dec j, psiA_of hT.1 h4⟩

theorem isS_twin {c d : A} (h : IsS c d) : isSN (enc c) (enc d) = true := by
  unfold IsS at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [isSN, gen4, bA_iff, bI_iff, allR_iff, spr_eq, cE1_eq, cE2_eq, cR1_eq, cR2_eq, cZ_eq,
    eqS_enc, ttS_enc, negS_enc, dblS_enc, beq_enc]
  exact ⟨h0, ⟨h1 _, h1 _, h1 _, h1 _⟩, ⟨h2 _, h2 _, h2 _, h2 _⟩, fun k _ => h3 (dec k)⟩

theorem isL_twin {c d l1 l3 : A} (h : IsL c d l1 l3) :
    isLN (enc c) (enc d) (enc l1) (enc l3) = true := by
  unfold IsL at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [isLN, gen4, bA_iff, cE1_eq, cE2_eq, cR1_eq, cR2_eq, cZ_eq, eqS_enc, anS_enc, ttS_enc,
    dblS_enc, beq_enc]
  exact ⟨h0, ⟨h1 _, h1 _, h1 _, h1 _⟩, ⟨h2 _, h2 _, h2 _, h2 _⟩, ⟨h3 _, h3 _, h3 _, h3 _⟩⟩

theorem psiB_of {c d l1 l3 c0 d0 : A} (hd : (2 : ℕ) • d = 0) (hl : (2 : ℕ) • l3 = 0)
    (h : psiBN (enc c) (enc d) (enc l1) (enc l3) (enc c0) (enc d0) = true) :
    PsiB c d l1 l3 c0 d0 := by
  simp only [psiBN, injS, gen4, bA_iff, bO_iff, bI_iff, allR_iff, spr_eq, cE1_eq, cE2_eq, cR1_eq,
    cR2_eq, cZ_eq, eqS_enc, anS_enc, ttS_enc, ssS_enc, llS_enc, rhoS_enc, dblS_enc, beq_enc] at h
  obtain ⟨h0, ⟨a1, a2, a3, a4⟩, hS, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩, hi⟩ := h
  unfold PsiB
  refine ⟨h0, ext4 ((eqH c0 d0 h0).comp (anH l1 l3 hl)) (llH.comp (eqH c0 d0 h0)) a1 a2 a3 a4, ?_,
    ext4 ((eqH c0 d0 h0).comp ttH) (ttH.comp (eqH c0 d0 h0)) b1 b2 b3 b4,
    ext4 ((eqH c0 d0 h0).comp rhoH) (rhoH.comp (eqH c0 d0 h0)) c1 c2 c3 c4, fun p hp => ?_⟩
  · rcases hS with ⟨s1, s2, s3, s4⟩ | ⟨s1, s2, s3, s4⟩
    · exact Or.inl (ext4 ((eqH c0 d0 h0).comp (eqH c d hd)) (ssH.comp (eqH c0 d0 h0)) s1 s2 s3 s4)
    · exact Or.inr (ext4 ((eqH c0 d0 h0).comp (eqH c d hd)) ((ssH.comp ttH).comp (eqH c0 d0 h0))
        s1 s2 s3 s4)
  · have := hi (cmp p) (cmp_lt p)
    rw [dec_cmp] at this
    exact this hp

def encP (ψ : A × A) : ℕ := enc ψ.1 + 4294967296 * enc ψ.2

theorem psiCodes_eq : psiCodes = psiCands.map encP := by decide

theorem encP_mod (ψ : A × A) : Nat.mod (encP ψ) 4294967296 = enc ψ.1 := by
  have := enc_lt ψ.1
  rw [nMod, encP]
  omega

theorem encP_div (ψ : A × A) : Nat.div (encP ψ) 4294967296 = enc ψ.2 := by
  have := enc_lt ψ.1
  rw [nD, encP]
  omega

theorem stageB_of (h : stageBB = true) : StageB := by
  unfold StageB RowS RowL
  intro c d hS l1 l3 hL
  simp only [stageBB, stageBL, allR_iff] at h
  have h2 := h (cmp c) (cmp_lt c) (cmp d) (cmp_lt d)
  rw [spr_cmp, spr_cmp, rowSN, bI_iff] at h2
  have h3 := h2 (isS_twin hS)
  simp only [allR_iff] at h3
  have h4 := h3 (cmp l1) (cmp_lt l1) (cmp l3) (cmp_lt l3)
  rw [spr_cmp, spr_cmp, rowLN, bI_iff, psiCodes_eq] at h4
  obtain ⟨ψ, hψ, h5⟩ := anyL_map encP _ psiCands (h4 (isL_twin hL))
  rw [encP_mod, encP_div] at h5
  unfold IsS at hS
  unfold IsL at hL
  exact ⟨ψ, hψ, psiB_of hS.1 hL.1 h5⟩

end CFSG.FzL410K

end
