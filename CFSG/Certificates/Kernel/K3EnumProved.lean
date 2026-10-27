module

public import CFSG.Certificates.Kernel.K3SlpProved
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Th.Native CFSG.KS.MulH
open CFSG.KS.BfsReplay SP CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

namespace EP

variable {K : K3C}

theorem bI {c t e : Bool} : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem bIfz {k : Nat} {X Y : Bool} (h : Bool.rec (motive := fun _ => Bool) Y X (Nat.beq k 0) = true) :
    (k = 0 → X = true) ∧ (0 < k → Y = true) := by
  cases k with
  | zero => exact ⟨fun _ => h, fun h' => absurd h' (Nat.lt_irrefl 0)⟩
  | succ k => exact ⟨fun e => absurd e (Nat.succ_ne_zero k), fun _ => h⟩

theorem bIfl {a b : Nat} {X : Bool} (h : Bool.rec (motive := fun _ => Bool) true X (Nat.blt a b) = true) :
    a < b → X = true := fun hab => by
  rw [Nat.blt_eq.mpr hab] at h
  exact h

theorem bNe {a b : Nat} (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true) :
    a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem bLex {q k l a b : Nat}
    (h : Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false
      (lexLtK k l a b)) true (Nat.beq q 0) = true) : q = 0 ∨ ¬ LexLt k l a b := by
  by_cases hq : q = 0
  · exact Or.inl hq
  · right
    have e : Nat.beq q 0 = false := by
      cases e' : Nat.beq q 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e') hq
    rw [e] at h
    intro hl
    rw [lexLtK_iffH.2 hl] at h
    exact absurd h (by decide)

structure HF (K : K3C) : Prop where
  sz : szOK K.n K.w = true
  gR : K.g ≤ K.R
  ord : 0 < K.ord
  gc : ∀ i < K.g, Cn K (K.GP i)
  syl : ∀ a < K.sy, K.SY a < K.R ∧ Cn K (K.AI a) ∧
    permOK K.n K.w (mask K.w) (K.n * K.w) (K.A a) (K.AI a) = true
  off : CFSG.KC.Child3.offOK K.CS K.OFF K.NC = true
  re : K.RE.length = K.CS.length
  nw : K.nw = K.CS.length
  rel : ∀ r ∈ K.RE, r < K.ord

theorem hf_of (h : K.headK = true) : HF K := by
  unfold K3C.headK at h
  obtain ⟨h1, h⟩ := bA.1 h
  obtain ⟨h2, h⟩ := bA.1 h
  obtain ⟨h3, h⟩ := bA.1 h
  obtain ⟨h4, h⟩ := bA.1 h
  obtain ⟨h5, h⟩ := bA.1 h
  obtain ⟨h6, h⟩ := bA.1 h
  obtain ⟨h7, h⟩ := bA.1 h
  obtain ⟨h8, h9⟩ := bA.1 h
  refine ⟨h1, Nat.le_of_ble_eq_true h2, Nat.blt_eq.mp h3, fun i hi => allN_spec h4 i hi,
    fun a ha => ?_, h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8,
    fun r hr => Nat.blt_eq.mp (List.all_eq_true.1 h9 r hr)⟩
  have := allN_spec h5 a ha
  obtain ⟨b1, b2⟩ := bA.1 this
  obtain ⟨b3, b4⟩ := bA.1 b2
  exact ⟨Nat.blt_eq.mp b1, b3, b4⟩

theorem ek_facts {k : Nat} (h : K.eK k = true) :
    Cn K (K.E k) ∧ (k = 0 → K.E k = K.one) ∧
    (0 < k → K.EP k < k ∧ K.EL k < K.sy ∧ K.E k = K.pc (K.E (K.EP k)) (K.A (K.EL k))) ∧
    (0 < k → k + 1 < K.ord → LexLt (K.EP k) (K.EL k) (K.EP (k + 1)) (K.EL (k + 1))) ∧
    (∀ l < K.sy, K.EK (K.sy * k + l) < K.ord ∧
      K.E (K.EK (K.sy * k + l)) = K.pc (K.E k) (K.A l) ∧
      (K.EK (K.sy * k + l) = 0 ∨
        ¬ LexLt k l (K.EP (K.EK (K.sy * k + l))) (K.EL (K.EK (K.sy * k + l))))) ∧
    (∀ l < K.sy, K.EKI (K.sy * k + l) < K.ord ∧
      K.E (K.EKI (K.sy * k + l)) = K.pc (K.E k) (K.AI l)) ∧
    K.ES k < K.ord ∧ K.ESI k < K.ord ∧ K.ES (K.ESI k) = k ∧
    (k + 1 < K.ord → K.hk (K.E (K.ES k)) < K.hk (K.E (K.ES (k + 1)))) := by
  unfold K3C.eK at h
  rw [CFSG.KC.K3.SP.sB] at h
  obtain ⟨c1, h⟩ := bA.1 h
  obtain ⟨c2, h⟩ := bA.1 h
  obtain ⟨c3, h⟩ := bA.1 h
  obtain ⟨c4, h⟩ := bA.1 h
  obtain ⟨c5, h⟩ := bA.1 h
  obtain ⟨c6, h⟩ := bA.1 h
  obtain ⟨c7, h⟩ := bA.1 h
  obtain ⟨c8, c9⟩ := bA.1 h
  obtain ⟨z1, z2⟩ := bIfz c2
  obtain ⟨-, z3⟩ := bIfz c3
  refine ⟨c1, fun e => Nat.eq_of_beq_eq_true (z1 e), fun hk => ?_, fun hk hk' => ?_,
    fun l hl => ?_, fun l hl => ?_, Nat.blt_eq.mp c6, Nat.blt_eq.mp c7, Nat.eq_of_beq_eq_true c8,
    fun hk' => Nat.blt_eq.mp (bIfl c9 hk')⟩
  · obtain ⟨a1, a2⟩ := bA.1 (z2 hk)
    obtain ⟨a3, a4⟩ := bA.1 a2
    exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a3, Nat.eq_of_beq_eq_true a4⟩
  · exact lexLtK_iffH.1 (bIfl (z3 hk) hk')
  · have := allN_spec c4 l hl
    rw [CFSG.KC.K3.SP.sB] at this
    obtain ⟨a1, a2⟩ := bA.1 this
    obtain ⟨a3, a4⟩ := bA.1 a2
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a3, bLex a4⟩
  · have := allN_spec c5 l hl
    rw [CFSG.KC.K3.SP.sB] at this
    obtain ⟨a1, a2⟩ := bA.1 this
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2⟩

@[expose] noncomputable def key2 (K : K3C) (q : Nat) : Nat :=
  Nat.add (Nat.mul (K.CI q) 18446744073709551616) (K.hk (K.CE q))

theorem ck_facts {p : Nat} (h : K.cK p = true) :
    K.CI p < K.CS.length ∧ lget K.OFF (K.CI p) ≤ p ∧ p - lget K.OFF (K.CI p) < lget K.CS (K.CI p) ∧
    Cn K (K.CE p) ∧
    (p - lget K.OFF (K.CI p) = 0 → K.CE p = K.E (lget K.RE (K.CI p))) ∧
    (0 < p - lget K.OFF (K.CI p) → K.CP p < p - lget K.OFF (K.CI p) ∧ K.CL p < K.sy ∧
      K.CE p = K.cj (K.CL p) (K.CE (lget K.OFF (K.CI p) + K.CP p))) ∧
    (0 < p - lget K.OFF (K.CI p) → p - lget K.OFF (K.CI p) + 1 < lget K.CS (K.CI p) →
      LexLt (K.CP p) (K.CL p) (K.CP (p + 1)) (K.CL (p + 1))) ∧
    (∀ l < K.sy, K.CK (K.sy * p + l) < lget K.CS (K.CI p) ∧
      K.CE (lget K.OFF (K.CI p) + K.CK (K.sy * p + l)) = K.cj l (K.CE p) ∧
      (K.CK (K.sy * p + l) = 0 ∨ ¬ LexLt (p - lget K.OFF (K.CI p)) l
        (K.CP (lget K.OFF (K.CI p) + K.CK (K.sy * p + l)))
        (K.CL (lget K.OFF (K.CI p) + K.CK (K.sy * p + l))))) ∧
    K.CO p < K.NC ∧ K.COI p < K.NC ∧ K.CO (K.COI p) = p ∧
    (p + 1 < K.NC → key2 K (K.CO p) < key2 K (K.CO (p + 1))) := by
  unfold K3C.cK at h
  simp only [CFSG.KC.K3.SP.sB] at h
  obtain ⟨c1, h⟩ := bA.1 h
  obtain ⟨c2, h⟩ := bA.1 h
  obtain ⟨c3, h⟩ := bA.1 h
  obtain ⟨c4, h⟩ := bA.1 h
  obtain ⟨c5, h⟩ := bA.1 h
  obtain ⟨c6, h⟩ := bA.1 h
  obtain ⟨c7, h⟩ := bA.1 h
  obtain ⟨c8, h⟩ := bA.1 h
  obtain ⟨c9, h⟩ := bA.1 h
  obtain ⟨c10, c11⟩ := bA.1 h
  obtain ⟨z1, z2⟩ := bIfz c5
  obtain ⟨-, z3⟩ := bIfz c6
  refine ⟨Nat.blt_eq.mp c1, Nat.le_of_ble_eq_true c2, Nat.blt_eq.mp c3, c4,
    fun e => Nat.eq_of_beq_eq_true (z1 e), fun hk => ?_, fun hk hk' => ?_, fun l hl => ?_,
    Nat.blt_eq.mp c8, Nat.blt_eq.mp c9, Nat.eq_of_beq_eq_true c10,
    fun hp => Nat.blt_eq.mp (bIfl c11 hp)⟩
  · obtain ⟨a1, a2⟩ := bA.1 (z2 hk)
    obtain ⟨a3, a4⟩ := bA.1 a2
    exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a3, Nat.eq_of_beq_eq_true a4⟩
  · exact lexLtK_iffH.1 (bIfl (z3 hk) hk')
  · have := allN_spec c7 l hl
    obtain ⟨a1, a2⟩ := bA.1 this
    obtain ⟨a3, a4⟩ := bA.1 a2
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a3, bLex a4⟩

theorem mem_facts {k : Nat} (h : K.memK k = true) (h1 : K.E k ≠ K.one)
    (h3 : K.pc (K.E k) (K.pc (K.E k) (K.E k)) = K.one) :
    K.MW k / 2 < K.NC ∧ (K.CE (K.MW k / 2) = K.E k ∨ K.CE (K.MW k / 2) = K.pc (K.E k) (K.E k)) := by
  unfold K3C.memK at h
  rw [CFSG.KC.K3.SP.sB] at h
  have e1 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (K.E k) K.one) = true := by
    cases e : Nat.beq (K.E k) K.one
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h1
  have e2 : Nat.beq (K.pc (K.E k) (K.pc (K.E k) (K.E k))) K.one = true := by rw [h3, Nat.beq_refl]
  rw [e1, e2] at h
  change strictB _ _ = true at h
  rw [CFSG.KC.K3.SP.sB] at h
  obtain ⟨a1, a2⟩ := bA.1 h
  refine ⟨Nat.blt_eq.mp a1, ?_⟩
  rcases bI.1 a2 with ⟨-, b⟩ | ⟨-, b⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true b)
  · exact Or.inr (Nat.eq_of_beq_eq_true b)

theorem wit_facts {j : Nat} (h : K.witK j = true) :
    (K.WT j = 0 → K.WU j < K.R ∧ K.pc (K.reg (K.WU j)) (K.E (lget K.RE j)) =
        K.pc (K.E (lget K.RE j)) (K.reg (K.WU j)) ∧
      K.pc (K.reg (K.WU j)) (K.reg (K.WU j)) ≠ K.one ∧ K.pw (K.reg (K.WU j)) 4 = K.one) ∧
    (K.WT j ≠ 0 → K.WU j < K.R ∧ K.WV j < K.R ∧
      K.pc (K.reg (K.WU j)) (K.reg (K.WU j)) = K.one ∧ K.reg (K.WU j) ≠ K.one ∧
      K.pc (K.reg (K.WV j)) (K.reg (K.WV j)) = K.one ∧ K.reg (K.WV j) ≠ K.one ∧
      K.reg (K.WU j) ≠ K.reg (K.WV j) ∧
      K.pc (K.reg (K.WU j)) (K.reg (K.WV j)) = K.pc (K.reg (K.WV j)) (K.reg (K.WU j)) ∧
      K.pc (K.reg (K.WU j)) (K.E (lget K.RE j)) = K.pc (K.E (lget K.RE j)) (K.reg (K.WU j)) ∧
      K.pc (K.reg (K.WV j)) (K.E (lget K.RE j)) = K.pc (K.E (lget K.RE j)) (K.reg (K.WV j))) := by
  unfold K3C.witK at h
  simp only [CFSG.KC.K3.SP.sB] at h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [e] at h
    obtain ⟨a1, a2⟩ := bA.1 h
    obtain ⟨a3, a4⟩ := bA.1 a2
    obtain ⟨a5, a6⟩ := bA.1 a4
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a3, bNe a5, Nat.eq_of_beq_eq_true a6⟩
  · have e' : Nat.beq (K.WT j) 0 = false := by
      cases e'' : Nat.beq (K.WT j) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e'') e
    rw [e'] at h
    obtain ⟨a1, h⟩ := bA.1 h
    obtain ⟨a2, h⟩ := bA.1 h
    obtain ⟨a3, h⟩ := bA.1 h
    obtain ⟨a4, h⟩ := bA.1 h
    obtain ⟨a5, h⟩ := bA.1 h
    obtain ⟨a6, h⟩ := bA.1 h
    obtain ⟨a7, h⟩ := bA.1 h
    obtain ⟨a8, h⟩ := bA.1 h
    obtain ⟨a9, a10⟩ := bA.1 h
    exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3, bNe a4,
      Nat.eq_of_beq_eq_true a5, bNe a6, bNe a7, Nat.eq_of_beq_eq_true a8,
      Nat.eq_of_beq_eq_true a9, Nat.eq_of_beq_eq_true a10⟩

theorem hk_go (X : Nat) : ∀ r ≤ K.n, ∀ s : Nat,
    (List.range r).foldr (fun i h => Nat.mod (Nat.mul (Nat.xor h
      (pg K.w (mask K.w) X (Nat.sub (Nat.sub K.n 1) i))) 1099511628211) 18446744073709551616) s =
      hkGo K.w (mask K.w) X r (K.n - r) s
  | 0, _, _ => rfl
  | r + 1, hr, s => by
    have e1 : K.n - (r + 1) + 1 = K.n - r := by omega
    have e2 : Nat.sub (Nat.sub K.n 1) r = K.n - (r + 1) := by
      change K.n - 1 - r = K.n - (r + 1)
      omega
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, hk_go X r (by omega),
      hkGo_succ, e1]
    rw [e2]
    rfl

theorem hk_eq {X : Nat} (hX : Cn K X) : (hkey K.n (tb K X)).toNat = K.hk X := by
  rw [hkey_tabT hX]
  unfold K3C.hk
  rw [CFSG.KS.Raw.Orb.foldN_eq, hk_go X K.n (Nat.le_refl _), Nat.sub_self]
  rfl

theorem inj_of_sort' {cnt : Nat} {T S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI i < cnt ∧ S (SI i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hS j (by omega)).2.2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2.2 hj
  intro a ha b hb e
  have ea := (hS a ha).2.2.1
  have eb := (hS b hb).2.2.1
  rw [← ea, ← eb] at e
  have hsa := (hS a ha).2.1
  have hsb := (hS b hb).2.1
  rcases Nat.lt_trichotomy (SI a) (SI b) with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono _ _ h hsb))
  · rw [← ea, ← eb, h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono _ _ h hsa))

theorem e_inj (he : ∀ k < K.ord, K.eK k = true) :
    ∀ a < K.ord, ∀ b < K.ord, K.hk (K.E a) = K.hk (K.E b) → a = b :=
  inj_of_sort' fun i hi => by
    obtain ⟨-, -, -, -, -, -, a1, a2, a3, a4⟩ := ek_facts (he i hi)
    exact ⟨a1, a2, a3, a4⟩

theorem c_inj (hc : ∀ p < K.NC, K.cK p = true) :
    ∀ a < K.NC, ∀ b < K.NC, key2 K a = key2 K b → a = b :=
  inj_of_sort' fun i hi => by
    obtain ⟨-, -, -, -, -, -, -, -, a1, a2, a3, a4⟩ := ck_facts (hc i hi)
    exact ⟨a1, a2, a3, a4⟩

@[expose] noncomputable def parE (K : K3C) (i : Nat) : Nat := if i = 0 then 0 else K.EP i

@[expose] noncomputable def labE (K : K3C) (i : Nat) : Nat := if i = 0 then 0 else K.EL i

theorem mul_replay (hF : HF K) (he : ∀ k < K.ord, K.eK k = true) {gens : Array Table}
    (hg : gens.size = K.sy) (hgt : ∀ j < K.sy, gens[j]! = tb K (K.A j))
    (hA : ∀ j < K.sy, Cn K (K.A j)) :
    CFSG.KS.HBfs.HReplay (hkey K.n) (fun j y => compT K.n y gens[j]!) gens.size (idT K.n) K.ord
      (fun i => tb K (K.E i)) (parE K) (labE K) (fun h j => K.EK (K.sy * h + j)) := by
  have F := fun k (hk : k < K.ord) => ek_facts (he k hk)
  refine ⟨hF.ord, ?_, rfl, rfl, fun a ha b hb e => ?_, fun i h0 hi => ?_, fun i h0 hi => ?_,
    fun h hh j hj => ?_⟩
  · rw [(F 0 hF.ord).2.1 rfl, tb_one hF.sz]
  · refine e_inj he a ha b hb ?_
    rw [← hk_eq (F a ha).1, ← hk_eq (F b hb).1]
    rw [e]
  · obtain ⟨a1, a2, a3⟩ := (F i hi).2.2.1 h0
    have hp : parE K i = K.EP i := by simp [parE, Nat.pos_iff_ne_zero.1 h0]
    have hl : labE K i = K.EL i := by simp [labE, Nat.pos_iff_ne_zero.1 h0]
    rw [hp, hl, hg]
    refine ⟨a1, a2, ?_⟩
    rw [hgt _ a2, tb_pc (F _ (by omega)).1 (hA _ a2), ← a3]
  · have hp : parE K i = K.EP i := by simp [parE, Nat.pos_iff_ne_zero.1 h0]
    have hl : labE K i = K.EL i := by simp [labE, Nat.pos_iff_ne_zero.1 h0]
    have hp' : parE K (i + 1) = K.EP (i + 1) := by simp [parE]
    have hl' : labE K (i + 1) = K.EL (i + 1) := by simp [labE]
    rw [hp, hl, hp', hl']
    exact (F i (by omega)).2.2.2.1 h0 hi
  · rw [hg] at hj
    obtain ⟨a1, a2, a3⟩ := (F h hh).2.2.2.2.1 j hj
    refine ⟨a1, ?_, ?_⟩
    · rw [hgt _ hj, tb_pc (F h hh).1 (hA _ hj), a2]
    · rcases a3 with a3 | a3
      · exact Or.inl a3
      · by_cases h0 : K.EK (K.sy * h + j) = 0
        · exact Or.inl h0
        · right
          have hp : parE K (K.EK (K.sy * h + j)) = K.EP (K.EK (K.sy * h + j)) := by
            simp [parE, h0]
          have hl : labE K (K.EK (K.sy * h + j)) = K.EL (K.EK (K.sy * h + j)) := by
            simp [labE, h0]
          rw [hp, hl]
          exact a3

theorem cls_mem (hF : HF K) (hc : ∀ p < K.NC, K.cK p = true) {c : Nat} (hcl : c < K.CS.length)
    {i : Nat} (hi : i < lget K.CS c) :
    lget K.OFF c + i < K.NC ∧ K.CI (lget K.OFF c + i) = c := by
  obtain ⟨ho, hsum⟩ := CFSG.KC.Child3.offOK_facts hF.off
  rw [CFSG.KC.Child3.lget_eq K.CS] at hi
  have e2 := ho c hcl
  have hlt : lget K.OFF c + i < K.NC := by
    rw [e2, ← hsum]
    have h1 := CFSG.KC.Child3.sum_take_succ' K.CS hcl
    have h2 := CFSG.KC.Child3.sum_take_le K.CS (c + 1)
    omega
  refine ⟨hlt, ?_⟩
  obtain ⟨a1, a2, a3, -⟩ := ck_facts (hc _ hlt)
  rw [CFSG.KC.Child3.lget_eq K.CS] at a3
  have e1 := ho _ a1
  rw [e1] at a2 a3
  exact (CFSG.KC.Child3.class_unique hcl a1 (by omega) (by omega) a2 (by omega)).symm

abbrev PR (K : K3C) (P : Nat) (g : Equiv.Perm (Fin K.n)) : Prop := CFSG.KS.Raw.Orb.PRep K.n K.w P g

theorem pr_eq {P Q : Nat} {g : Equiv.Perm (Fin K.n)} (hP : Cn K P) (hQ : Cn K Q) (h1 : PR K P g)
    (h2 : PR K Q g) : P = Q := by
  refine unpack_injH hP hQ (Array.ext (by simp [unpack]) fun i a b => ?_)
  have hi : i < K.n := by simpa [unpack] using a
  rw [← getElem!_pos _ i a, ← getElem!_pos _ i b, CFSG.KS.Raw.Orb.unpack_get hi,
    CFSG.KS.Raw.Orb.unpack_get hi]
  exact (h1 ⟨i, hi⟩).trans (h2 ⟨i, hi⟩).symm

theorem pr_uniq {P : Nat} {g h : Equiv.Perm (Fin K.n)} (h1 : PR K P g) (h2 : PR K P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

theorem class_le (hF : HF K) (he : ∀ k < K.ord, K.eK k = true) (hc : ∀ p < K.NC, K.cK p = true)
    {c : Nat} (hcl : c < K.CS.length) :
    lget K.CS c ≤ K.ord := by
  classical
  have F := fun k (hk : k < K.ord) => ek_facts (he k hk)
  obtain ⟨hn, hw⟩ := CFSG.KC.BfsPin.szOK_facts' hF.sz
  have hn32 : K.n < 2 ^ 32 := by omega
  have ha : ∀ l < K.sy, ∃ a : Equiv.Perm (Fin K.n), PR K (K.A l) a ∧ PR K (K.AI l) a⁻¹ := by
    intro l hl
    have hr := CFSG.Monster.B.Co2.rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack (hF.syl l hl).2.2)
    exact ⟨_, CFSG.KS.Raw.Orb.prep_of_rep hr.1, CFSG.KS.Raw.Orb.prep_of_rep hr.2⟩
  choose! a haA haI using ha
  have hE : ∀ k < K.ord, ∃ g : Equiv.Perm (Fin K.n), PR K (K.E k) g ∧
      g ∈ Subgroup.closure {x | ∃ l < K.sy, x = a l} := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        rw [(F 0 hk).2.1 rfl]
        exact ⟨1, CFSG.KS.Raw.Orb.prep_pidn hn hw, Subgroup.one_mem _⟩
      · obtain ⟨a1, a2, a3⟩ := (F k hk).2.2.1 h0
        obtain ⟨g, hg, hgm⟩ := ih _ a1 (by omega)
        refine ⟨g * a (K.EL k), ?_, Subgroup.mul_mem _ hgm (Subgroup.subset_closure ⟨_, a2, rfl⟩)⟩
        rw [a3]
        exact CFSG.KS.Raw.Orb.prep_pcomp hn32 hg (haA _ a2)
  let S : Set (Equiv.Perm (Fin K.n)) := {g | ∃ k < K.ord, PR K (K.E k) g}
  have hS : ∀ g ∈ Subgroup.closure {x | ∃ l < K.sy, x = a l}, g ∈ S := by
    intro g hg
    refine Subgroup.closure_induction_right (p := fun x _ => x ∈ S) ⟨0, hF.ord, ?_⟩
      (fun x _ y hy hxS => ?_) (fun x _ y hy hxS => ?_) hg
    · rw [(F 0 hF.ord).2.1 rfl]
      exact CFSG.KS.Raw.Orb.prep_pidn hn hw
    · obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨k, hk, hkx⟩ := hxS
      obtain ⟨b1, b2, -⟩ := (F k hk).2.2.2.2.1 l hl
      refine ⟨_, b1, ?_⟩
      rw [b2]
      exact CFSG.KS.Raw.Orb.prep_pcomp hn32 hkx (haA l hl)
    · obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨k, hk, hkx⟩ := hxS
      obtain ⟨b1, b2⟩ := (F k hk).2.2.2.2.2.1 l hl
      refine ⟨_, b1, ?_⟩
      rw [b2]
      exact CFSG.KS.Raw.Orb.prep_pcomp hn32 hkx (haI l hl)
  have hcls := fun i (hi : i < lget K.CS c) => cls_mem hF hc hcl hi
  have hCE : ∀ i < lget K.CS c, ∃ q < K.ord, K.CE (lget K.OFF c + i) = K.E q := by
    have key : ∀ i < lget K.CS c, ∃ g : Equiv.Perm (Fin K.n), PR K (K.CE (lget K.OFF c + i)) g ∧
        g ∈ Subgroup.closure {x | ∃ l < K.sy, x = a l} := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        obtain ⟨hp, hci⟩ := hcls i hi
        have C := ck_facts (hc _ hp)
        rw [hci, Nat.add_sub_cancel_left] at C
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · obtain ⟨-, -, -, -, b, -⟩ := C
          rw [b h0]
          obtain ⟨g, hg, hgm⟩ := hE _ (hF.rel (lget K.RE c) (by
            rw [CFSG.KC.Child3.lget_eq, List.getD_eq_getElem _ _ (by rw [hF.re]; exact hcl)]
            exact List.getElem_mem _))
          exact ⟨g, hg, hgm⟩
        · obtain ⟨-, -, -, -, -, b, -⟩ := C
          obtain ⟨b1, b2, b3⟩ := b h0
          obtain ⟨g, hg, hgm⟩ := ih _ b1 (by omega)
          refine ⟨a (K.CL (lget K.OFF c + i)) * g * (a (K.CL (lget K.OFF c + i)))⁻¹, ?_, ?_⟩
          · rw [b3]
            exact CFSG.KS.Raw.Orb.prep_pcomp hn32 (CFSG.KS.Raw.Orb.prep_pcomp hn32 (haA _ b2) hg)
              (haI _ b2)
          · have hm : a (K.CL (lget K.OFF c + i)) ∈ Subgroup.closure {x | ∃ l < K.sy, x = a l} :=
              Subgroup.subset_closure ⟨_, b2, rfl⟩
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hgm) (Subgroup.inv_mem _ hm)
    intro i hi
    obtain ⟨g, hg, hgm⟩ := key i hi
    obtain ⟨q, hq, hqg⟩ := hS g hgm
    exact ⟨q, hq, pr_eq (ck_facts (hc _ (hcls i hi).1)).2.2.2.1 (F q hq).1 hg hqg⟩
  have hinj : Set.InjOn (fun i => K.CE (lget K.OFF c + i)) (Finset.range (lget K.CS c)) := by
    intro i hi i' hi' e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    have := c_inj hc _ (hcls i hi).1 _ (hcls i' hi').1 (by
      unfold key2
      rw [(hcls i hi).2, (hcls i' hi').2]
      simp only at e
      rw [e])
    omega
  have hsub : (Finset.range (lget K.CS c)).image (fun i => K.CE (lget K.OFF c + i)) ⊆
      (Finset.range K.ord).image K.E := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, hq, e⟩ := hCE i (Finset.mem_range.1 hi)
    exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 hq, e.symm⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
  exact h1.trans (Finset.card_image_le.trans (by rw [Finset.card_range]))

@[expose] noncomputable def parC (K : K3C) (o i : Nat) : Nat := if i = 0 then 0 else K.CP (o + i)

@[expose] noncomputable def labC (K : K3C) (o i : Nat) : Nat := if i = 0 then 0 else K.CL (o + i)

theorem tb_cj (hA : ∀ j < K.sy, Cn K (K.A j)) (hAI : ∀ j < K.sy, Cn K (K.AI j)) {l Y : Nat}
    (hl : l < K.sy) (hY : Cn K Y) :
    conjT K.n (tb K (K.A l)) (tb K (K.AI l)) (tb K Y) = tb K (K.cj l Y) := by
  unfold conjT
  rw [tb_pc (hA l hl) hY, tb_pc (cn_pc (hA l hl) hY) (hAI l hl)]
  rfl

theorem cls_replay (hF : HF K) (hc : ∀ p < K.NC, K.cK p = true) {gens gensI : Array Table} (hg : gens.size = K.sy)
    (hgt : ∀ j < K.sy, gens[j]! = tb K (K.A j)) (hgi : ∀ j < K.sy, gensI[j]! = tb K (K.AI j))
    (hA : ∀ j < K.sy, Cn K (K.A j)) {c : Nat} (hcl : c < K.CS.length) (hpos : 0 < lget K.CS c) :
    CFSG.KS.HBfs.HReplay (hkey K.n) (fun j y => conjT K.n gens[j]! gensI[j]! y) gens.size
      (tb K (K.E (lget K.RE c))) (lget K.CS c) (fun i => tb K (K.CE (lget K.OFF c + i)))
      (parC K (lget K.OFF c)) (labC K (lget K.OFF c))
      (fun h j => K.CK (K.sy * (lget K.OFF c + h) + j)) := by
  have hAI : ∀ j < K.sy, Cn K (K.AI j) := fun j hj => (hF.syl j hj).2.1
  have C : ∀ i < lget K.CS c, _ := fun i (hi : i < lget K.CS c) => by
    have h1 := ck_facts (hc _ (cls_mem hF hc hcl hi).1)
    rw [(cls_mem hF hc hcl hi).2, Nat.add_sub_cancel_left] at h1
    exact h1
  have hcn : ∀ i < lget K.CS c, Cn K (K.CE (lget K.OFF c + i)) := fun i hi => (C i hi).2.2.2.1
  refine ⟨hpos, ?_, rfl, rfl, fun a ha b hb e => ?_, fun i h0 hi => ?_, fun i h0 hi => ?_,
    fun h hh j hj => ?_⟩
  · rw [(C 0 hpos).2.2.2.2.1 rfl]
  · have e' : K.hk (K.CE (lget K.OFF c + a)) = K.hk (K.CE (lget K.OFF c + b)) := by
      rw [← hk_eq (hcn a ha), ← hk_eq (hcn b hb)]
      rw [e]
    have := c_inj hc _ (cls_mem hF hc hcl ha).1 _ (cls_mem hF hc hcl hb).1 (by
      unfold key2
      rw [(cls_mem hF hc hcl ha).2, (cls_mem hF hc hcl hb).2, e'])
    omega
  · obtain ⟨a1, a2, a3⟩ := (C i hi).2.2.2.2.2.1 h0
    have hp : parC K (lget K.OFF c) i = K.CP (lget K.OFF c + i) := by
      simp [parC, Nat.pos_iff_ne_zero.1 h0]
    have hl : labC K (lget K.OFF c) i = K.CL (lget K.OFF c + i) := by
      simp [labC, Nat.pos_iff_ne_zero.1 h0]
    rw [hp, hl, hg]
    refine ⟨a1, a2, ?_⟩
    rw [hgt _ a2, hgi _ a2, tb_cj hA hAI a2 (hcn _ (by omega)), ← a3]
  · have hp : parC K (lget K.OFF c) i = K.CP (lget K.OFF c + i) := by
      simp [parC, Nat.pos_iff_ne_zero.1 h0]
    have hl : labC K (lget K.OFF c) i = K.CL (lget K.OFF c + i) := by
      simp [labC, Nat.pos_iff_ne_zero.1 h0]
    have hp' : parC K (lget K.OFF c) (i + 1) = K.CP (lget K.OFF c + i + 1) := by
      simp [parC, Nat.add_assoc]
    have hl' : labC K (lget K.OFF c) (i + 1) = K.CL (lget K.OFF c + i + 1) := by
      simp [labC, Nat.add_assoc]
    rw [hp, hl, hp', hl']
    exact (C i (by omega)).2.2.2.2.2.2.1 h0 hi
  · rw [hg] at hj
    obtain ⟨a1, a2, a3⟩ := (C h hh).2.2.2.2.2.2.2.1 j hj
    refine ⟨a1, ?_, ?_⟩
    · rw [hgt _ hj, hgi _ hj, tb_cj hA hAI hj (hcn h hh), a2]
    · rcases a3 with a3 | a3
      · exact Or.inl a3
      · by_cases h0 : K.CK (K.sy * (lget K.OFF c + h) + j) = 0
        · exact Or.inl h0
        · right
          have hp : parC K (lget K.OFF c) (K.CK (K.sy * (lget K.OFF c + h) + j)) =
              K.CP (lget K.OFF c + K.CK (K.sy * (lget K.OFF c + h) + j)) := by
            simp [parC, h0]
          have hl : labC K (lget K.OFF c) (K.CK (K.sy * (lget K.OFF c + h) + j)) =
              K.CL (lget K.OFF c + K.CK (K.sy * (lget K.OFF c + h) + j)) := by
            simp [labC, h0]
          rw [hp, hl]
          exact a3

end EP

end CFSG.KC.K3

end
