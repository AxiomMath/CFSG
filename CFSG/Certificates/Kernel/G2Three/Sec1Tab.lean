module

public import CFSG.Certificates.Kernel.G2Three.Sec1Pair
public import CFSG.Certificates.Kernel.G2Three.Tables
import CFSG.Certificates.Kernel.Co1DceCover

public section

namespace CFSG.KC.G2Three.Sec1

open Subgroup CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

theorem notB_true {b : Bool} (h : Bool.not' b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem eqK_at {A B C D : ℕ → ℕ} {m hi : ℕ} (h : eqK A B C D m hi = true) (hm : m ≤ 64 * hi) :
    ∀ q < m, MULP (A q) (B q) = MULP (C q) (D q) := fun q hq =>
  Nat.eq_of_beq_eq_true (allBelow_g2 h hm q hq)

theorem neK_at {A B C D : ℕ → ℕ} {m hi : ℕ} (h : neK A B C D m hi = true) (hm : m ≤ 64 * hi) :
    ∀ q < m, MULP (A q) (B q) ≠ MULP (C q) (D q) := fun q hq =>
  Nat.ne_of_beq_eq_false (notB_true (allBelow_g2 h hm q hq))

theorem idxK_at {X Y I : ℕ → ℕ} {n m hi : ℕ} (h : idxK X Y I n m hi = true) (hm : m ≤ 64 * hi) :
    ∀ q < m, I q < n ∧ X (I q) = Y q := fun q hq => by
  obtain ⟨h1, h2⟩ := bAnd_g2 (allBelow_g2 h hm q hq)
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem ltK_at {I : ℕ → ℕ} {n m hi : ℕ} (h : ltK I n m hi = true) (hm : m ≤ 64 * hi) :
    ∀ q < m, I q < n := fun q hq => Nat.blt_eq.mp (allBelow_g2 h hm q hq)

theorem neqK_at {U V : ℕ → ℕ} {m hi : ℕ} (h : neqK U V m hi = true) (hm : m ≤ 64 * hi) :
    ∀ q < m, U q ≠ V q := fun q hq =>
  Nat.ne_of_beq_eq_false (notB_true (allBelow_g2 h hm q hq))

theorem parK_at {PA PB POS : ℕ → ℕ} {k m hi : ℕ} (h : parK PA PB POS k m hi = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, PA i ≤ i ∧ PB i < k ∧ POS (PA i * k + PB i) = i + 1 :=
  fun i hi' => by
  obtain ⟨h1, h2⟩ := bAnd_g2 (allBelow_g2 h hm i hi')
  obtain ⟨h2, h3⟩ := bAnd_g2 h2
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem closP_at {X G POS : ℕ → ℕ} {n k lo m hi : ℕ} (h : closP X G POS n k lo m hi = true)
    (hm : m ≤ 64 * hi) :
    ∀ j < m, POS (lo + j) < n ∧ X (POS (lo + j)) = MULP (X ((lo + j) / k)) (G ((lo + j) % k)) :=
  fun j hj => by
  obtain ⟨h1, h2⟩ := bAnd_g2 (allBelow_g2 h hm j hj)
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem basisK_at {X G : ℕ → ℕ} {r n hi : ℕ} (h : basisK X G r n hi = true) (hm : n ≤ 64 * hi) :
    ∀ c < n, X c = pwP G r c := fun c hc => Nat.eq_of_beq_eq_true (allBelow_g2 h hm c hc)

theorem actK_at {X G M : ℕ → ℕ} {k hi : ℕ} (h : actK X G M k hi = true) (hm : 3 * k ≤ 64 * hi) :
    ∀ s < k, ∀ j < 3, MULP (G s) (X (2 ^ j)) = MULP (X ((M s >>> (3 * j)) &&& 7)) (G s) := by
  intro s hs j hj
  have hq : 3 * s + j < Nat.mul 3 k := by
    change 3 * s + j < 3 * k
    omega
  have e := Nat.eq_of_beq_eq_true (allBelow_g2 h hm (3 * s + j) hq)
  have hd : (3 * s + j) / 3 = s := by omega
  have hmod : (3 * s + j) % 3 = j := by omega
  change MULP (G ((3 * s + j) / 3)) (X (1 <<< ((3 * s + j) % 3))) =
    MULP (X ((M ((3 * s + j) / 3) >>> (3 * ((3 * s + j) % 3))) &&& 7)) (G ((3 * s + j) / 3)) at e
  rw [hd, hmod, Nat.shiftLeft_eq, Nat.one_mul] at e
  exact e

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sqInK_at {X Y IQ : ℕ → ℕ} {nY n hi : ℕ} (h : sqInK X Y IQ nY n hi = true)
    (hm : n ≤ 64 * hi) : ∀ i < n, MULP (MULP (X i) (X i)) (MULP (X i) (X i)) = ONEP →
      IQ i < nY ∧ Y (IQ i) = MULP (X i) (X i) := by
  intro i hi' h4
  have e := allBelow_g2 h hm i hi'
  change strictB (MULP (X i) (X i)) (fun q => Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq (Y (IQ i)) q) (Nat.blt (IQ i) nY))
    (Nat.beq (MULP q q) ONEP)) = true at e
  have hb : Nat.beq (MULP (MULP (X i) (X i)) (MULP (X i) (X i))) ONEP = true := by
    rw [Nat.beq_eq]
    exact h4
  rw [strictB_eq] at e
  beta_reduce at e
  rw [hb] at e
  obtain ⟨h1, h2⟩ := bAnd_g2 e
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

variable {G : Type} [Group G] (ρ : G →* Wm)

@[expose] def TabOf (X : ℕ → ℕ) (n : ℕ) (K : Set G) : Prop :=
  (∀ i < n, ∃ g ∈ K, Enc ρ (X i) g) ∧ ∀ g ∈ K, ∃ i < n, Enc ρ (X i) g

variable {ρ}

theorem mem_of_tabOf (hρ : Function.Injective ρ) {X : ℕ → ℕ} {n i : ℕ} {K : Set G} {g : G}
    (ht : TabOf ρ X n K) (hi : i < n) (hg : Enc ρ (X i) g) : g ∈ K := by
  obtain ⟨g', hg'K, hg'⟩ := ht.1 i hi
  rwa [enc_unique hρ hg hg']

theorem tab_closure (hρ : Function.Injective ρ) {X Gd POS PA PB : ℕ → ℕ} {n k : ℕ} {g : ℕ → G}
    (hn : 0 < n) (hg : ∀ s < k, Enc ρ (Gd s) (g s)) (h0 : X 0 = ONEP)
    (hcl : ∀ i < n * k, POS i < n ∧ X (POS i) = MULP (X (i / k)) (Gd (i % k)))
    (hpar : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ POS (PA i * k + PB i) = i + 1) :
    TabOf ρ X n (closure (g '' {s | s < k}) : Set G) := by
  have : Finite Wm := inferInstanceAs (Finite (Fin 14 ⊕ Fin 14 → Fin 14 ⊕ Fin 14 → ZMod 3))
  have : Finite G := Finite.of_injective ρ hρ
  have hgK : ∀ s < k, g s ∈ closure (g '' {s | s < k}) := fun s hs => subset_closure ⟨s, hs, rfl⟩
  have hX0 : Enc ρ (X 0) 1 := by
    rw [h0]
    exact enc_one ρ
  refine ⟨fun i => ?_, fun y hy => ?_⟩
  · induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | i
      · exact ⟨1, one_mem _, hX0⟩
      · obtain ⟨hpa, hpb, hpos⟩ := hpar i (by omega)
        obtain ⟨x, hxK, hx⟩ := ih (PA i) (by omega) (by omega)
        obtain ⟨hlt, hdv, hmd⟩ := flat_facts (by omega) (show PA i < n by omega) hpb
        obtain ⟨-, hXe⟩ := hcl _ hlt
        rw [hpos, hdv, hmd] at hXe
        refine ⟨x * g (PB i), mul_mem hxK (hgK _ hpb), ?_⟩
        rw [hXe]
        exact enc_mul ρ hx (hg _ hpb)
  · let S : Set G := {x | ∃ i < n, Enc ρ (X i) x}
    have hSg : ∀ x ∈ S, ∀ s < k, x * g s ∈ S := by
      rintro x ⟨i, hi, hx⟩ s hs
      obtain ⟨hlt, hdv, hmd⟩ := flat_facts (by omega) hi hs
      obtain ⟨hp, hXe⟩ := hcl _ hlt
      rw [hdv, hmd] at hXe
      refine ⟨_, hp, ?_⟩
      rw [hXe]
      exact enc_mul ρ hx (hg s hs)
    let T : Submonoid G :=
      { carrier := {y | ∀ x ∈ S, x * y ∈ S}
        one_mem' := fun x hx => by rwa [mul_one]
        mul_mem' := fun {a b} ha hb x hx => by
          rw [← mul_assoc]
          exact hb _ (ha x hx) }
    have hTinv : ∀ y ∈ T, y⁻¹ ∈ T := by
      intro y hy
      have ho := orderOf_pos y
      have e : y ^ (orderOf y - 1) * y = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one]
      rw [← eq_inv_of_mul_eq_one_left e]
      exact T.pow_mem hy _
    let H : Subgroup G := { T with inv_mem' := fun {y} hy => hTinv y hy }
    have hle : closure (g '' {s | s < k}) ≤ H := by
      rw [closure_le]
      rintro _ ⟨s, hs, rfl⟩ x hx
      exact hSg x hx s hs
    obtain ⟨i, hi, hyi⟩ := (hle hy : y ∈ T) 1 ⟨0, hn, hX0⟩
    rw [one_mul] at hyi
    exact ⟨i, hi, hyi⟩

theorem tab_card (hρ : Function.Injective ρ) {X : ℕ → ℕ} {n : ℕ} {K : Subgroup G}
    (ht : TabOf ρ X n (K : Set G)) (hinj : ∀ i < n, ∀ j < n, X i = X j → i = j) :
    Nat.card K = n := by
  have hch : ∀ i : Fin n, ∃ x ∈ (K : Set G), Enc ρ (X i) x := fun i => ht.1 i i.2
  choose e heK hee using hch
  have hbij : Function.Bijective (fun i : Fin n => (⟨e i, heK i⟩ : K)) := by
    constructor
    · intro i j hij
      have hij' : e i = e j := congrArg Subtype.val hij
      have hj : Enc ρ (X j) (e i) := by
        rw [hij']
        exact hee j
      exact Fin.ext (hinj i i.2 j j.2 (enc_inj (hee i) hj))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hxi⟩ := ht.2 x hx
      exact ⟨⟨i, hi⟩, Subtype.ext (enc_unique hρ (hee ⟨i, hi⟩) hxi)⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def pwG (g : ℕ → G) (r c : ℕ) : G :=
  Nat.rec (motive := fun _ => G) 1 (fun i acc => if c.testBit i then acc * g i else acc) r

theorem pwG_succ (g : ℕ → G) (r c : ℕ) :
    pwG g (r + 1) c = pwG g r c * (if c.testBit r then g r else 1) := by
  change (if c.testBit r then pwG g r c * g r else pwG g r c) = _
  split <;> simp

theorem blt_land_bit (c i : ℕ) : Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)) = c.testBit i := by
  change Nat.blt 0 (c &&& 1 <<< i) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow]
  cases c.testBit i
  · simp only [Bool.toNat_false, Nat.zero_mul]
    rfl
  · simp [Nat.two_pow_pos]

variable (ρ) in
theorem enc_pwP {Gd : ℕ → ℕ} {g : ℕ → G} {r : ℕ} (hg : ∀ s < r, Enc ρ (Gd s) (g s)) (c : ℕ) :
    Enc ρ (pwP Gd r c) (pwG g r c) := by
  induction r with
  | zero => exact enc_one ρ
  | succ r ih =>
    have ih' := ih (fun s hs => hg s (by omega))
    change Enc ρ (Bool.rec (motive := fun _ => ℕ) (pwP Gd r c) (MULP (pwP Gd r c) (Gd r))
      (Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 r)))) _
    rw [blt_land_bit, pwG_succ]
    cases hb : c.testBit r
    · simpa using ih'
    · simpa using enc_mul ρ ih' (hg r (by omega))

theorem pwG_one_of {g : ℕ → G} {c : ℕ} : ∀ {r : ℕ}, (∀ i < r, c.testBit i = false) → pwG g r c = 1
  | 0, _ => rfl
  | r + 1, h => by
    rw [pwG_succ, h r (by omega), pwG_one_of (fun i hi => h i (by omega))]
    simp

theorem pwG_zero (g : ℕ → G) (r : ℕ) : pwG g r 0 = 1 :=
  pwG_one_of fun i _ => Nat.zero_testBit i

theorem pwG_two_pow {g : ℕ → G} {r j : ℕ} (hj : j < r) : pwG g r (2 ^ j) = g j := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [pwG_succ, Nat.testBit_two_pow]
    by_cases hjr : j = r
    · subst hjr
      rw [pwG_one_of (fun i hi => by rw [Nat.testBit_two_pow]; simp; omega)]
      simp
    · rw [ih (by omega)]
      simp [hjr]

theorem pwG_comm {g : ℕ → G} {R t : ℕ} (hc : ∀ s < R, ∀ t < R, g s * g t = g t * g s)
    (ht : t < R) (c : ℕ) : ∀ r ≤ R, g t * pwG g r c = pwG g r c * g t
  | 0, _ => by simp [pwG]
  | r + 1, hr => by
    rw [pwG_succ, ← mul_assoc, pwG_comm hc ht c r (by omega), mul_assoc, mul_assoc]
    congr 1
    split
    · exact hc t ht r (by omega)
    · simp

theorem pwG_mul {g : ℕ → G} {r : ℕ} (hc : ∀ s < r, ∀ t < r, g s * g t = g t * g s)
    (hs : ∀ s < r, g s * g s = 1) (c d : ℕ) : pwG g r c * pwG g r d = pwG g r (c ^^^ d) := by
  induction r with
  | zero => simp [pwG]
  | succ r ih =>
    have ih' := ih (fun s hs' t ht => hc s (by omega) t (by omega)) (fun s hs' => hs s (by omega))
    have hcm : ∀ (b : Bool), (if b then g r else 1) * pwG g r d =
        pwG g r d * (if b then g r else 1) := by
      intro b
      split
      · exact pwG_comm hc (by omega) d r (by omega)
      · simp
    rw [pwG_succ, pwG_succ, pwG_succ, Nat.testBit_xor]
    simp only [mul_assoc]
    rw [← mul_assoc (if c.testBit r = true then g r else 1) (pwG g r d), hcm, mul_assoc,
      ← mul_assoc (pwG g r c), ih']
    congr 1
    have h1 := hs r (by omega)
    cases c.testBit r <;> cases d.testBit r <;> simp [h1]

theorem basis_tab {Gd X : ℕ → ℕ} {g : ℕ → G} {r : ℕ} (hg : ∀ s < r, Enc ρ (Gd s) (g s))
    (hc : ∀ s < r, ∀ t < r, g s * g t = g t * g s) (hs : ∀ s < r, g s * g s = 1)
    (hX : ∀ c < 2 ^ r, X c = pwP Gd r c) :
    TabOf ρ X (2 ^ r) (closure (g '' {s | s < r}) : Set G) := by
  have hmem : ∀ c, ∀ r' ≤ r, pwG g r' c ∈ closure (g '' {s | s < r}) := by
    intro c r'
    induction r' with
    | zero => exact fun _ => one_mem _
    | succ r' ih =>
      intro hr
      rw [pwG_succ]
      refine mul_mem (ih (by omega)) ?_
      split
      · exact subset_closure ⟨r', by simp only [Set.mem_setOf_eq]; omega, rfl⟩
      · exact one_mem _
  have hK : ∀ y ∈ closure (g '' {s | s < r}), ∃ c < 2 ^ r, pwG g r c = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨2 ^ s, Nat.pow_lt_pow_right (by norm_num) hs, pwG_two_pow hs⟩
    | one => exact ⟨0, Nat.two_pow_pos r, pwG_zero g r⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a ^^^ b, Nat.xor_lt_two_pow ha hb, (pwG_mul hc hs a b).symm⟩
    | inv x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [eq_inv_iff_mul_eq_one, pwG_mul hc hs, Nat.xor_self, pwG_zero]
  refine ⟨fun c hc' => ⟨pwG g r c, hmem c r le_rfl, ?_⟩, fun y hy => ?_⟩
  · rw [hX c hc']
    exact enc_pwP ρ hg c
  · obtain ⟨c, hc', rfl⟩ := hK y hy
    refine ⟨c, hc', ?_⟩
    rw [hX c hc']
    exact enc_pwP ρ hg c

theorem spanM_bit (a b c : ℕ) :
    (spanM a b).testBit c = decide (c = 0 ∨ c = a ∨ c = b ∨ c = a ^^^ b) := by
  have e : spanM a b = (2 ^ 0 ||| 2 ^ a) ||| (2 ^ b ||| 2 ^ (a ^^^ b)) := by
    change (1 ||| 1 <<< a) ||| (1 <<< b ||| 1 <<< (a ^^^ b)) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, pow_zero]
  rw [e, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow,
    Nat.testBit_two_pow, Nat.testBit_two_pow]
  generalize a ^^^ b = x
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

theorem closure_pair_ne {g : ℕ → G} (hc : ∀ s < 3, ∀ t < 3, g s * g t = g t * g s)
    (hs : ∀ s < 3, g s * g s = 1) (hinj : ∀ c < 8, ∀ d < 8, pwG g 3 c = pwG g 3 d → c = d)
    {a b a' b' : ℕ} (ha : a < 8) (hb : b < 8) (ha' : a' < 8) (hb' : b' < 8)
    (hne : spanM a b ≠ spanM a' b') :
    closure {pwG g 3 a, pwG g 3 b} ≠ closure {pwG g 3 a', pwG g 3 b'} := by
  have key : ∀ a b, a < 8 → b < 8 → ∀ c < 8,
      pwG g 3 c ∈ closure {pwG g 3 a, pwG g 3 b} ↔ (c = 0 ∨ c = a ∨ c = b ∨ c = a ^^^ b) := by
    intro a b ha hb c hc'
    constructor
    · intro hm
      have hS : ∀ y ∈ closure {pwG g 3 a, pwG g 3 b},
          ∃ d, (d = 0 ∨ d = a ∨ d = b ∨ d = a ^^^ b) ∧ pwG g 3 d = y := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem x hx =>
          rcases hx with rfl | rfl
          · exact ⟨a, by simp, rfl⟩
          · exact ⟨b, by simp, rfl⟩
        | one => exact ⟨0, by simp, pwG_zero g 3⟩
        | mul x y _ _ hx hy =>
          obtain ⟨d1, hd1, rfl⟩ := hx
          obtain ⟨d2, hd2, rfl⟩ := hy
          refine ⟨d1 ^^^ d2, ?_, (pwG_mul hc hs d1 d2).symm⟩
          rcases hd1 with rfl | rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl | rfl <;>
            simp [Nat.xor_comm, Nat.xor_left_comm]
        | inv x _ hx =>
          obtain ⟨d, hd, rfl⟩ := hx
          refine ⟨d, hd, ?_⟩
          rw [eq_inv_iff_mul_eq_one, pwG_mul hc hs, Nat.xor_self, pwG_zero]
      obtain ⟨d, hd, he⟩ := hS _ hm
      have hd8 : d < 8 := by
        have hab : a ^^^ b < 2 ^ 3 := Nat.xor_lt_two_pow ha hb
        generalize a ^^^ b = x at hab hd
        omega
      rw [← hinj d hd8 c hc' he]
      exact hd
    · rintro (rfl | rfl | rfl | rfl)
      · rw [pwG_zero]
        exact one_mem _
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · rw [← pwG_mul hc hs]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  intro he
  apply hne
  apply Nat.eq_of_testBit_eq
  intro c
  rw [spanM_bit, spanM_bit]
  by_cases hc8 : c < 8
  · rw [decide_eq_decide, ← key a b ha hb c hc8, ← key a' b' ha' hb' c hc8, he]
  · have h1 : ¬ (c = 0 ∨ c = a ∨ c = b ∨ c = a ^^^ b) := by
      have hab : a ^^^ b < 2 ^ 3 := Nat.xor_lt_two_pow ha hb
      generalize a ^^^ b = x at hab
      omega
    have h2 : ¬ (c = 0 ∨ c = a' ∨ c = b' ∨ c = a' ^^^ b') := by
      have hab : a' ^^^ b' < 2 ^ 3 := Nat.xor_lt_two_pow ha' hb'
      generalize a' ^^^ b' = x at hab
      omega
    simp only [h1, h2]

theorem allR_iff (f : ℕ → Bool) : ∀ k, allR k f = true ↔ ∀ s < k, f s = true
  | 0 => by simp [allR]
  | k + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (allR k f) (f k) = true ↔ _
    rw [Nat.forall_lt_succ_right, ← allR_iff f k]
    cases f k <;> simp

theorem cntK_card [Finite G] (hρ : Function.Injective ρ) {X Gd : ℕ → ℕ} {g : ℕ → G}
    {k n hi : ℕ} {K : Subgroup G} (ht : TabOf ρ X n (K : Set G))
    (hinj : ∀ i < n, ∀ j < n, X i = X j → i = j) (hg : ∀ s < k, Enc ρ (Gd s) (g s))
    (hn : n ≤ 64 * hi) :
    cntK X Gd k n hi = Nat.card ↥(K ⊓ centralizer (g '' {s | s < k})) := by
  let P : ℕ → Prop := fun i => ∀ s < k, MULP (X i) (Gd s) = MULP (Gd s) (X i)
  have hf : ∀ i, strictN (X i) (fun x => Bool.rec (motive := fun _ => ℕ) 0 1
      (allR k fun s => Nat.beq (MULP x (Gd s)) (MULP (Gd s) x))) = if P i then 1 else 0 := by
    intro i
    rw [CFSG.KS.Mat3.strictN_eq3]
    by_cases hp : P i
    · have : allR k (fun s => Nat.beq (MULP (X i) (Gd s)) (MULP (Gd s) (X i))) = true :=
        (allR_iff _ k).2 fun s hs => Nat.beq_eq.mpr (hp s hs)
      rw [this, if_pos hp]
    · have : allR k (fun s => Nat.beq (MULP (X i) (Gd s)) (MULP (Gd s) (X i))) = false := by
        cases e : allR k (fun s => Nat.beq (MULP (X i) (Gd s)) (MULP (Gd s) (X i)))
        · rfl
        · exact absurd (fun s hs => Nat.eq_of_beq_eq_true ((allR_iff _ k).1 e s hs)) hp
      rw [this, if_neg hp]
  have hcnt : cntK X Gd k n hi = ((Finset.range n).filter P).card := by
    rw [Finset.card_filter]
    unfold cntK
    rw [CFSG.Certificates.Co1D.sumBelow_spec _ hn]
    exact Finset.sum_congr rfl fun i _ => hf i
  rw [hcnt]
  have hch : ∀ i : ↥((Finset.range n).filter P), ∃ x ∈ (K : Set G), Enc ρ (X i) x := fun i =>
    ht.1 i (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1)
  choose e heK hee using hch
  have hcomm : ∀ (x : G) (i : ℕ), Enc ρ (X i) x →
      (x ∈ centralizer (g '' {s | s < k}) ↔ P i) := by
    intro x i hx
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      exact enc_inj (enc_mul ρ hx (hg s hs))
        (by rw [← h _ ⟨s, hs, rfl⟩]; exact enc_mul ρ (hg s hs) hx)
    · rintro h _ ⟨s, hs, rfl⟩
      exact (mul_eq_of_MULP hρ hx (hg s hs) (hg s hs) hx (h s hs)).symm
  have hbij : Function.Bijective
      (fun i : ↥((Finset.range n).filter P) =>
        (⟨e i, heK i, (hcomm _ _ (hee i)).2 (Finset.mem_filter.1 i.2).2⟩ :
          ↥(K ⊓ centralizer (g '' {s | s < k})))) := by
    constructor
    · intro i j hij
      have hij' : e i = e j := congrArg Subtype.val hij
      have hj : Enc ρ (X j) (e i) := by
        rw [hij']
        exact hee j
      exact Subtype.ext (hinj i (Finset.mem_range.1 (Finset.mem_filter.1 i.2).1) j
        (Finset.mem_range.1 (Finset.mem_filter.1 j.2).1) (enc_inj (hee i) hj))
    · rintro ⟨x, hxK, hxC⟩
      obtain ⟨i, hi, hxi⟩ := ht.2 x hxK
      have hPi : P i := (hcomm x i hxi).1 hxC
      refine ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hPi⟩⟩, ?_⟩
      exact Subtype.ext (enc_unique hρ (hee _) hxi)
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem sqInK_sound (hρ : Function.Injective ρ) {X Y IQ : ℕ → ℕ} {nY n hi : ℕ} {S F : Set G}
    (h : sqInK X Y IQ nY n hi = true) (hm : n ≤ 64 * hi) (hS : TabOf ρ X n S)
    (hF : TabOf ρ Y nY F) : ∀ x ∈ S, x ^ 4 = 1 → x ^ 2 ∈ F := by
  intro x hx h4
  obtain ⟨i, hi, hxi⟩ := hS.2 x hx
  have h2 := enc_mul ρ hxi hxi
  have h4' := enc_mul ρ h2 h2
  have e4 : x * x * (x * x) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4] at h4'
  obtain ⟨hq, hY⟩ := sqInK_at h hm i hi (enc_inj h4' (enc_one ρ))
  have hY' : Enc ρ (Y (IQ i)) (x ^ 2) := by
    rw [hY, sq]
    exact h2
  exact mem_of_tabOf hρ hF hq hY'

end CFSG.KC.G2Three.Sec1

end
