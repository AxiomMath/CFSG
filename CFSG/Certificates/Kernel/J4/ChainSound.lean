module

public import CFSG.Certificates.Kernel.J4.DceS
public import CFSG.Certificates.Kernel.LceSP.Popcount
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.J4Chain

open CFSG.KJ4 CFSG.KJ4.S CFSG.KC.Loop Finset

structure RightAct (G α : Type*) [Monoid G] where
  act : α → G → α
  act_one : ∀ a, act a 1 = a
  act_mul : ∀ a x y, act a (x * y) = act (act a x) y

variable {G α M : Type*}

def RightAct.fixSub [Group G] (A : RightAct G α) (P : Set α) : Subgroup G where
  carrier := {g | ∀ a ∈ P, A.act a g = a}
  one_mem' := fun a _ => A.act_one a
  mul_mem' := fun {x y} hx hy a ha => by
    rw [A.act_mul, hx a ha, hy a ha]
  inv_mem' := fun {x} hx a ha => by
    have h := A.act_mul a x x⁻¹
    rw [mul_inv_cancel, A.act_one, hx a ha] at h
    exact h.symm

theorem RightAct.mem_fixSub [Group G] (A : RightAct G α) {P : Set α} {g : G} :
    g ∈ A.fixSub P ↔ ∀ a ∈ P, A.act a g = a := Iff.rfl

theorem card_mul_le_of_orbit [Group G] (A : RightAct G α) (S : Subgroup G) [Finite S] (b : α)
    (n : ℕ) (x : ℕ → G) (hx : ∀ k < n, x k ∈ S)
    (hinj : ∀ k < n, ∀ j < n, A.act b (x k) = A.act b (x j) → k = j) :
    n * Nat.card (A.fixSub {b} ⊓ S : Subgroup G) ≤ Nat.card S := by
  rw [← Subgroup.relIndex_mul_card (A.fixSub {b}) S]
  apply Nat.mul_le_mul_right
  let F : Fin n → S ⧸ (A.fixSub {b}).subgroupOf S := fun k =>
    QuotientGroup.mk ⟨(x k)⁻¹, S.inv_mem (hx k k.2)⟩
  have hF : Function.Injective F := by
    intro k j hkj
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hkj
    have hfix : A.act b (x k * (x j)⁻¹) = b := by
      have := (A.mem_fixSub).1 hkj b (Set.mem_singleton b)
      simpa using this
    have hkj' : A.act b (x k) = A.act b (x j) := by
      calc A.act b (x k) = A.act b (x k * (x j)⁻¹ * x j) := by rw [inv_mul_cancel_right]
        _ = A.act (A.act b (x k * (x j)⁻¹)) (x j) := A.act_mul _ _ _
        _ = A.act b (x j) := by rw [hfix]
    exact Fin.ext (hinj k k.2 j j.2 hkj')
  have := Nat.card_le_card_of_injective F hF
  simpa [Subgroup.relIndex, Subgroup.index] using this

structure PackedModel (M α : Type*) [Monoid M] where
  ev : ℕ → M
  vv : ℕ → α
  A : RightAct M α
  ev_mul : ∀ a b, a < 2 ^ 144 → b < 2 ^ 144 → ev (mul12 a b) = ev a * ev b
  ev_one : ev ident12 = 1
  vv_vecmul : ∀ v X, v < 4096 → X < 2 ^ 144 → vv (vecmul v X) = A.act (vv v) (ev X)
  vv_inj : ∀ v w, v < 4096 → w < 4096 → vv v = vv w → v = w

variable [Monoid M]

def PackedModel.uA (P : PackedModel M α) : RightAct Mˣ α where
  act a g := P.A.act a g
  act_one a := by simp [P.A.act_one]
  act_mul a x y := by simp [P.A.act_mul]

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem mulF_eq (A B : ℕ) : mulF A B = mul12 A B := by
  simp only [mulF, strictN_eq]

theorem boolRec_cases {Q : ℕ → Prop} {c : Bool} {x y : ℕ} (hx : Q x) (hy : c = true → Q y) :
    Q (Bool.rec (motive := fun _ => ℕ) x y c) := by
  cases c
  · exact hx
  · exact hy rfl

theorem recAll (g : ℕ → Bool) (m : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun l ih => andB (g l) ih) m = true) :
    ∀ l < m, g l = true := by
  induction m with
  | zero => intro l hl; omega
  | succ m ih =>
    have h' : andB (g m) (Nat.rec (motive := fun _ => Bool) true (fun l ih => andB (g l) ih) m)
      = true := h
    rw [andB_iff] at h'
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact ih h'.2 l hl
    · exact h'.1

theorem recAllR (g : ℕ → Bool) (m : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun l ih => andB ih (g l)) m = true) :
    ∀ l < m, g l = true := by
  induction m with
  | zero => intro l hl; omega
  | succ m ih =>
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun l ih => andB ih (g l)) m) (g m)
      = true := h
    rw [andB_iff] at h'
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact ih h'.1 l hl
    · exact h'.2

theorem rngAll_spec {a b hi : ℕ} {f : ℕ → Bool} (h : rngAll a b hi f = true) {i : ℕ}
    (hai : a ≤ i) (hib : i < b) (hih : i < a + 64 * hi) : f i = true := by
  have hout := recAll _ hi h
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 64 ∧ i = a + (64 * q + r) :=
    ⟨(i - a) / 64, (i - a) % 64, Nat.mod_lt _ (by omega), by omega⟩
  have hq : q < hi := by omega
  have hin := recAll (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i b))
    (Nat.add a (Nat.add (Nat.shiftLeft q (nat_lit 6)) l))) (nat_lit 64) (hout q hq) r hr
  beta_reduce at hin
  have hX : Nat.add a (Nat.add (Nat.shiftLeft q (nat_lit 6)) r) = a + (64 * q + r) := by
    change a + (q <<< 6 + r) = a + (64 * q + r)
    rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 by norm_num]
    omega
  rw [hX, Nat.blt_eq.mpr hib] at hin
  exact hin

theorem lv_eq (L k : ℕ) : lv L k = (L >>> (12 * k)) &&& (2 ^ 12 - 1) := rfl

theorem lv_lt (L k : ℕ) : lv L k < 4096 :=
  Nat.and_lt_two_pow _ (n := 12) (by decide)

theorem gmat_eq (G g : ℕ) : gmat G g = (G >>> (144 * g)) &&& (2 ^ 144 - 1) := rfl

theorem gmat_lt (G g : ℕ) : gmat G g < 2 ^ 144 :=
  Nat.and_lt_two_pow _ (by decide)

theorem eM_lt (E : ℕ) : eM E < 2 ^ 144 :=
  Nat.and_lt_two_pow _ (by decide)

@[expose] def pack (w : ℕ) (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (f k) (Nat.mul w k))) m

theorem pack_succ (w : ℕ) (f : ℕ → ℕ) (m : ℕ) :
    pack w f (m + 1) = Nat.lor (pack w f m) (Nat.shiftLeft (f m) (Nat.mul w m)) := rfl

theorem pack_testBit {w : ℕ} {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ w) {k i : ℕ} (hi : i < w) :
    ∀ m, (pack w f m).testBit (w * k + i) = (decide (k < m) && (f k).testBit i)
  | 0 => by simp [pack]
  | m + 1 => by
    have e : pack w f (m + 1) = pack w f m ||| f m <<< (w * m) := rfl
    rw [e, Nat.testBit_or, pack_testBit hf hi m, Nat.testBit_shiftLeft]
    rcases lt_trichotomy k m with hk | rfl | hk
    · have h1 : w * (k + 1) ≤ w * m := Nat.mul_le_mul_left w hk
      rw [Nat.mul_succ] at h1
      have h2 : ¬ w * k + i ≥ w * m := by omega
      have h3 : k < m + 1 := by omega
      simp [hk, h2, h3]
    · simp
    · have h1 : w * (m + 1) ≤ w * k := Nat.mul_le_mul_left w hk
      rw [Nat.mul_succ] at h1
      have h0 : (f m).testBit (w * k + i - w * m) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf m) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h2 : ¬ k < m := by omega
      have h3 : ¬ k < m + 1 := by omega
      simp [h0, h2, h3]

theorem pack_get {w : ℕ} {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ w) {m g : ℕ} (hg : g < m) :
    (pack w f m >>> (w * g)) &&& (2 ^ w - 1) = f g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · rw [pack_testBit hf hi m]
    simp [hi, hg]
  · have h0 : (f g).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf g) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, h0]

theorem pack_congr {w : ℕ} {f f' : ℕ → ℕ} : ∀ {m}, (∀ k < m, f k = f' k) → pack w f m = pack w f' m
  | 0, _ => rfl
  | m + 1, h => by
    rw [pack_succ, pack_succ, pack_congr (fun k hk => h k (by omega)), h m (by omega)]

@[expose] def stMk (p nb B : ℕ) : ℕ :=
  Nat.lor p (Nat.lor (Nat.shiftLeft nb (nat_lit 64)) (Nat.shiftLeft B (nat_lit 72)))

theorem stMk_eq {p nb B : ℕ} (hp : p < 2 ^ 64) (hnb : nb < 2 ^ 8) :
    stMk p nb B = p + 2 ^ 64 * (nb + 2 ^ 8 * B) := by
  have h1 : Nat.shiftLeft B (nat_lit 72) = (B <<< 8) <<< 64 := by
    rw [← Nat.shiftLeft_add]
    rfl
  unfold stMk
  rw [h1]
  change p ||| ((nb <<< 64) ||| ((B <<< 8) <<< 64)) = _
  rw [← Nat.shiftLeft_or_distrib, Nat.or_comm nb, ← Nat.shiftLeft_add_eq_or_of_lt hnb,
    Nat.or_comm p, ← Nat.shiftLeft_add_eq_or_of_lt hp, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

theorem stMk_prod {p nb B : ℕ} (hp : p < 2 ^ 64) (hnb : nb < 2 ^ 8) :
    Nat.land (stMk p nb B) (nat_lit 18446744073709551615) = p := by
  change stMk p nb B &&& (2 ^ 64 - 1) = p
  rw [Nat.and_two_pow_sub_one_eq_mod, stMk_eq hp hnb, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hp]

theorem stMk_nb {p nb B : ℕ} (hp : p < 2 ^ 64) (hnb : nb < 2 ^ 8) :
    Nat.land (Nat.shiftRight (stMk p nb B) (nat_lit 64)) (nat_lit 255) = nb := by
  change (stMk p nb B >>> 64) &&& (2 ^ 8 - 1) = nb
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, stMk_eq hp hnb,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hp, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnb]

theorem stMk_B {p nb B : ℕ} (hp : p < 2 ^ 64) (hnb : nb < 2 ^ 8) :
    Nat.shiftRight (stMk p nb B) (nat_lit 72) = B := by
  change stMk p nb B >>> 72 = B
  rw [Nat.shiftRight_eq_div_pow, stMk_eq hp hnb, show (2 : ℕ) ^ 72 = 2 ^ 64 * 2 ^ 8 by norm_num,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hp,
    Nat.zero_add, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hnb, Nat.zero_add]

theorem popcount_4096 (x : ℕ) : CFSG.KJ4.popcount x 4096 = ∑ j ∈ range 4096, x / 2 ^ j % 2 :=
  CFSG.Certificates.LceP.pc4096_eq x

theorem sum_bits_eq (x N : ℕ) :
    ∑ j ∈ range N, x / 2 ^ j % 2 = #((range N).filter (fun j => x.testBit j = true)) := by
  rw [card_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem orAll_testBit (L : ℕ) : ∀ n j, (orAll L n).testBit j = true ↔ ∃ k < n, lv L k = j
  | 0, j => by
    change (0 : ℕ).testBit j = true ↔ _
    simp
  | n + 1, j => by
    have e : orAll L (n + 1) = orAll L n ||| 2 ^ lv L n := by
      rw [← Nat.one_shiftLeft]
      rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, orAll_testBit L n j, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (⟨k, hk, rfl⟩ | h)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact Or.inl ⟨k, h, rfl⟩
      · exact Or.inr rfl

theorem orAll_injOn {L n : ℕ} (h : CFSG.KJ4.popcount (orAll L n) 4096 = n) :
    Set.InjOn (lv L) (range n : Set ℕ) := by
  rw [popcount_4096, sum_bits_eq] at h
  have himg : (range 4096).filter (fun j => (orAll L n).testBit j = true) = (range n).image (lv L) := by
    ext j
    simp only [mem_filter, mem_range, mem_image, orAll_testBit]
    constructor
    · rintro ⟨_, k, hk, hj⟩
      exact ⟨k, hk, hj⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨lv_lt L k, k, hk, rfl⟩
  rw [himg] at h
  exact card_image_iff.1 (h.trans (card_range n).symm)

structure GivensIn (P : PackedModel M α) (S : Set Mˣ) (FT ET : ℕ → ℕ) (LET W0 TR Dc GM ne : ℕ) :
    Prop where
  letter : ∀ l < 7, gmHas GM l = true → ∃ u ∈ S, (u : M) = P.ev (letMat LET l)
  fact : ∀ e < ne, eK (ET e) = 1 → gmHas GM 8 = true → fD (FT (eA (ET e))) = Dc →
    fDp (FT (eA (ET e))) = Dc → fJ (FT (eA (ET e))) = 0 →
    ∃ u ∈ S, (u : M) = P.ev (fPi (FT (eA (ET e))))
  w0 : gmHas GM 9 = true → ∃ u ∈ S, (u : M) = P.ev W0
  tr : gmHas GM 10 = true → ∃ u ∈ S, (u : M) = P.ev TR

theorem etOK_mem (P : PackedModel M α) {S : Set Mˣ} {FT ET : ℕ → ℕ} {LET W0 TR Dc GM ne : ℕ}
    (hG : GivensIn P S FT ET LET W0 TR Dc GM ne)
    (hall : ∀ e < ne, etOK FT ET LET W0 TR Dc GM e = true) :
    ∀ e < ne, ∃ u ∈ Subgroup.closure S, (u : M) = P.ev (eM (ET e)) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  have h := hall e he
  simp only [etOK, letB_eq, eEnt] at h
  revert h
  cases h0 : Nat.beq (eK (ET e)) (nat_lit 0)
  · cases h1 : Nat.beq (eK (ET e)) (nat_lit 1)
    · cases h2 : Nat.beq (eK (ET e)) (nat_lit 2)
      · cases h3 : Nat.beq (eK (ET e)) (nat_lit 3)
        · cases h4 : Nat.beq (eK (ET e)) (nat_lit 4)
          · intro h
            simp only [andB_iff, Nat.beq_eq, Nat.blt_eq, mulF_eq] at h
            obtain ⟨-, ha, hinv⟩ := h
            obtain ⟨ua, hua, hue⟩ := ih _ ha (by omega)
            have hm : P.ev (eM (ET e)) * (ua : M) = 1 := by
              rw [hue, ← P.ev_mul _ _ (eM_lt _) (eM_lt _), hinv, P.ev_one]
            exact ⟨ua⁻¹, Subgroup.inv_mem _ hua, ((Units.mul_eq_one_iff_eq_inv).1 hm).symm⟩
          · intro h
            simp only [andB_iff, Nat.beq_eq, Nat.blt_eq, mulF_eq] at h
            obtain ⟨ha, hb, hab⟩ := h
            obtain ⟨ua, hua, hea⟩ := ih _ ha (by omega)
            obtain ⟨ub, hub, heb⟩ := ih _ hb (by omega)
            refine ⟨ua * ub, Subgroup.mul_mem _ hua hub, ?_⟩
            rw [hab, P.ev_mul _ _ (eM_lt _) (eM_lt _), Units.val_mul, hea, heb]
        · intro h
          simp only [andB_iff, Nat.beq_eq] at h
          obtain ⟨u, hu, hue⟩ := hG.tr h.1
          exact ⟨u, Subgroup.subset_closure hu, by rw [h.2, hue]⟩
      · intro h
        simp only [andB_iff, Nat.beq_eq] at h
        obtain ⟨u, hu, hue⟩ := hG.w0 h.1
        exact ⟨u, Subgroup.subset_closure hu, by rw [h.2, hue]⟩
    · intro h
      simp only [andB_iff, Nat.beq_eq] at h
      obtain ⟨hgm, hD, hDp, hJ, heq⟩ := h
      obtain ⟨u, hu, hue⟩ := hG.fact e he (Nat.eq_of_beq_eq_true h1) hgm hD hDp hJ
      exact ⟨u, Subgroup.subset_closure hu, by rw [heq, hue]⟩
  · intro h
    simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at h
    obtain ⟨h7, hgm, -, heq⟩ := h
    obtain ⟨u, hu, hue⟩ := hG.letter _ h7 hgm
    exact ⟨u, Subgroup.subset_closure hu, by rw [heq, hue]⟩

theorem fixAll_spec {G ng B nb : ℕ} (h : fixAll G ng B nb = true) :
    ∀ k < ng, ∀ i < nb, vecmul (lv B i) (gmat G k) = lv B i := by
  intro k hk i hi
  have h1 := recAllR _ ng h k hk
  have h2 := recAllR _ nb h1 i hi
  simpa [chkFix] using h2

theorem lvG_eq (ET : ℕ → ℕ) (ne R : ℕ) : lvG ET ne R = pack 144 (fun k =>
    Bool.rec (motive := fun _ => ℕ) 0 (eM (eEnt ET (lvGen R k))) (Nat.blt (lvGen R k) ne)) (lvNg R) :=
  rfl

theorem tree_orbit (P : PackedModel M α) (K : Subgroup Mˣ) {L PG G ng n : ℕ} (u : ℕ → Mˣ)
    (hu : ∀ k < ng, u k ∈ K) (hue : ∀ k < ng, (u k : M) = P.ev (gmat G k))
    (h : treeOKs L PG G ng n = true) :
    ∀ k < n, ∃ g ∈ K, P.vv (lv L k) = P.uA.act (P.vv (lv L 0)) g := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hk' := recAllR _ _ h k hk
  simp only [orB_iff, andB_iff, Nat.beq_eq, Nat.blt_eq, strictN_eq] at hk'
  rcases hk' with h0 | ⟨hpar, hgen, -, hv⟩
  · subst h0
    exact ⟨1, K.one_mem, (P.uA.act_one _).symm⟩
  · obtain ⟨g, hg, hgv⟩ := ih _ hpar (by omega)
    refine ⟨g * u (lgen PG k), K.mul_mem hg (hu _ hgen), ?_⟩
    rw [← hv, P.vv_vecmul _ _ (lv_lt _ _) (gmat_lt _ _), ← hue _ hgen, hgv]
    exact (P.uA.act_mul _ _ _).symm

def basesSet (P : PackedModel M α) (bs : ℕ → ℕ) (nb : ℕ) : Set α := {a | ∃ i < nb, a = P.vv (bs i)}

def ChainInv (P : PackedModel M α) (H : Subgroup Mˣ) (st : ℕ) : Prop :=
  ∃ p nb : ℕ, ∃ bs : ℕ → ℕ, p < 2 ^ 64 ∧ nb < 2 ^ 8 ∧ (∀ i, bs i < 4096) ∧
    st = stMk p nb (pack 12 bs nb) ∧
    p * Nat.card (P.uA.fixSub (basesSet P bs nb) ⊓ H : Subgroup Mˣ) ≤ Nat.card H

theorem chainInv_zero [Finite Mˣ] (P : PackedModel M α) (H : Subgroup Mˣ) : ChainInv P H 0 :=
  ⟨0, 0, fun _ => 0, by norm_num, by norm_num, fun _ => by norm_num,
    by rw [stMk_eq (by norm_num) (by norm_num)]; simp [pack], by simp⟩

theorem chainInv_one [Finite Mˣ] (P : PackedModel M α) (H : Subgroup Mˣ) :
    ChainInv P H (nat_lit 1) :=
  ⟨1, 0, fun _ => 0, by norm_num, by norm_num, fun _ => by norm_num,
    by rw [stMk_eq (by norm_num) (by norm_num)]; simp [pack],
    by rw [Nat.one_mul]; exact Subgroup.card_le_of_le inf_le_right⟩

theorem chainInv_land [Finite Mˣ] (P : PackedModel M α) {H : Subgroup Mˣ} {st : ℕ}
    (h : ChainInv P H st) : Nat.land st (nat_lit 18446744073709551615) ≤ Nat.card H := by
  obtain ⟨p, nb, bs, hp, hnb, -, rfl, hc⟩ := h
  rw [stMk_prod hp hnb]
  exact le_trans (Nat.le_mul_of_pos_right p Nat.card_pos) hc

theorem chLevel_inv [Finite Mˣ] (P : PackedModel M α) {H : Subgroup Mˣ} {ET : ℕ → ℕ} {ne R st : ℕ}
    (hET : ∀ e < ne, ∃ u ∈ H, (u : M) = P.ev (eM (ET e))) (h : ChainInv P H st) :
    ChainInv P H (chLevel ET ne R st) := by
  obtain ⟨p, nb, bs, hp, hnb, hbs, rfl, hcard⟩ := h
  unfold chLevel
  simp only [strictN_eq]
  rw [stMk_prod hp hnb, stMk_nb hp hnb, stMk_B hp hnb]
  refine boolRec_cases (Q := ChainInv P H) (chainInv_zero P H) ?_
  intro hc
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hc
  obtain ⟨-, -, hpn, hnb', hgb, hpop, htree, hfix⟩ := hc
  have hgen : ∀ k < lvNg R, lvGen R k < ne := fun k hk => by
    have := recAllR _ _ hgb k hk
    simpa using this
  have hfG : ∀ k, (fun k => Bool.rec (motive := fun _ => ℕ) 0 (eM (eEnt ET (lvGen R k)))
      (Nat.blt (lvGen R k) ne)) k < 2 ^ 144 := by
    intro k
    beta_reduce
    cases Nat.blt (lvGen R k) ne
    · exact Nat.two_pow_pos 144
    · exact eM_lt _
  have hgm : ∀ k < lvNg R, gmat (lvG ET ne R) k = eM (ET (lvGen R k)) := fun k hk => by
    rw [gmat_eq, lvG_eq, pack_get hfG hk]
    have hb : Nat.blt (lvGen R k) ne = true := Nat.blt_eq.mpr (hgen k hk)
    simp only [hb, eEnt]
  have hlv : ∀ i < nb, lv (pack 12 bs nb) i = bs i := fun i hi => by
    rw [lv_eq, pack_get (fun j => hbs j) hi]
  have hu : ∀ k < lvNg R, ∃ u ∈ P.uA.fixSub (basesSet P bs nb) ⊓ H,
      (u : M) = P.ev (gmat (lvG ET ne R) k) := by
    intro k hk
    obtain ⟨u, huH, hue⟩ := hET _ (hgen k hk)
    refine ⟨u, Subgroup.mem_inf.2 ⟨?_, huH⟩, by rw [hgm k hk, hue]⟩
    rw [RightAct.mem_fixSub]
    rintro a ⟨i, hi, rfl⟩
    have hf := fixAll_spec hfix k hk i hi
    rw [hlv i hi] at hf
    change P.A.act (P.vv (bs i)) (u : M) = P.vv (bs i)
    rw [hue, ← hgm k hk, ← P.vv_vecmul _ _ (hbs i) (gmat_lt _ _), hf]
  choose! u hu1 hu2 using hu
  have horb := tree_orbit P _ u hu1 hu2 htree
  choose! x hx1 hx2 using horb
  have hinj : ∀ k < lvN R, ∀ j < lvN R, P.uA.act (P.vv (lv (lvL R) 0)) (x k) =
      P.uA.act (P.vv (lv (lvL R) 0)) (x j) → k = j := by
    intro k hk j hj hkj
    rw [← hx2 k hk, ← hx2 j hj] at hkj
    have := P.vv_inj _ _ (lv_lt _ _) (lv_lt _ _) hkj
    exact orAll_injOn hpop (by simpa using hk) (by simpa using hj) this
  have hcnt := card_mul_le_of_orbit P.uA _ _ _ x hx1 hinj
  obtain ⟨bs', hbs'⟩ : ∃ f : ℕ → ℕ, f = fun i => if i = nb then lv (lvL R) 0 else bs i := ⟨_, rfl⟩
  have hb1 : bs' nb = lv (lvL R) 0 := by simp [hbs']
  have hb2 : ∀ i, i ≠ nb → bs' i = bs i := fun i hi => by simp [hbs', hi]
  have hset : P.uA.fixSub (basesSet P bs' (nb + 1)) ⊓ H =
      P.uA.fixSub {P.vv (lv (lvL R) 0)} ⊓ (P.uA.fixSub (basesSet P bs nb) ⊓ H) := by
    ext g
    simp only [Subgroup.mem_inf, RightAct.mem_fixSub]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => h1 a ⟨nb, Nat.lt_succ_self nb, by rw [hb1]; exact ha⟩,
        fun a ⟨i, hi, ha⟩ => h1 a ⟨i, by omega, by rw [hb2 i (by omega)]; exact ha⟩, h2⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun a ⟨i, hi, ha⟩ => ?_, h3⟩
      by_cases hin : i = nb
      · subst hin
        rw [hb1] at ha
        exact h1 a ha
      · rw [hb2 i hin] at ha
        exact h2 a ⟨i, by omega, ha⟩
  refine ⟨p * lvN R, nb + 1, bs', hpn, ?_, ?_, ?_, ?_⟩
  · have : nb < 255 := hnb'
    norm_num
    omega
  · intro i
    by_cases hi : i = nb
    · rw [hi, hb1]
      exact lv_lt _ _
    · rw [hb2 i hi]
      exact hbs i
  · rw [pack_succ 12 bs' nb, hb1, pack_congr (fun k hk => hb2 k (by omega))]
    rfl
  · rw [hset]
    calc p * lvN R * Nat.card (P.uA.fixSub {P.vv (lv (lvL R) 0)} ⊓
          (P.uA.fixSub (basesSet P bs nb) ⊓ H) : Subgroup Mˣ)
        = p * (lvN R * Nat.card (P.uA.fixSub {P.vv (lv (lvL R) 0)} ⊓
          (P.uA.fixSub (basesSet P bs nb) ⊓ H) : Subgroup Mˣ)) := Nat.mul_assoc _ _ _
      _ ≤ p * Nat.card (P.uA.fixSub (basesSet P bs nb) ⊓ H : Subgroup Mˣ) :=
          Nat.mul_le_mul_left _ hcnt
      _ ≤ Nat.card H := hcard

theorem listRec_strict (F : ℕ → ℕ → ℕ) (Q : ℕ → Prop) (hF : ∀ R st, Q st → Q (F R st)) :
    ∀ (l : List ℕ) (st : ℕ), Q st → Q (List.rec (motive := fun _ => ℕ → ℕ) (fun st => st)
      (fun R _ ih st => strictN (F R st) ih) l st)
  | [], _, h => h
  | R :: l, st, h => by
    change Q (strictN (F R st) (List.rec (motive := fun _ => ℕ → ℕ) (fun st => st)
      (fun R _ ih st => strictN (F R st) ih) l))
    rw [strictN_eq]
    exact listRec_strict F Q hF l _ (hF R st h)

theorem chainRun_etOK {FT ET : ℕ → ℕ} {LET W0 TR Dc GM ne : ℕ} {lvls : List ℕ}
    (h : 0 < chainRun FT ET LET W0 TR Dc GM ne lvls) :
    ∀ e < ne, etOK FT ET LET W0 TR Dc GM e = true := by
  intro e he
  unfold chainRun at h
  revert h
  cases hr : rngAll (nat_lit 0) ne (Nat.add (Nat.shiftRight ne (nat_lit 6)) (nat_lit 1))
    (etOK FT ET LET W0 TR Dc GM)
  · intro h
    exact absurd h (Nat.lt_irrefl 0)
  · intro _
    refine rngAll_spec hr (Nat.zero_le e) he ?_
    have h64 : ne >>> 6 = ne / 64 := by
      rw [Nat.shiftRight_eq_div_pow]
    change e < 0 + 64 * (ne >>> 6 + 1)
    rw [h64]
    omega

theorem chainRun_mem (P : PackedModel M α) {S : Set Mˣ} {FT ET : ℕ → ℕ}
    {LET W0 TR Dc GM ne : ℕ} {lvls : List ℕ} (hG : GivensIn P S FT ET LET W0 TR Dc GM ne)
    (h : 0 < chainRun FT ET LET W0 TR Dc GM ne lvls) :
    ∀ e < ne, ∃ u ∈ Subgroup.closure S, (u : M) = P.ev (eM (ET e)) :=
  etOK_mem P hG (chainRun_etOK h)

theorem chainRun_le [Finite Mˣ] (P : PackedModel M α) {S : Set Mˣ} {FT ET : ℕ → ℕ}
    {LET W0 TR Dc GM ne : ℕ} (lvls : List ℕ) (hG : GivensIn P S FT ET LET W0 TR Dc GM ne) :
    chainRun FT ET LET W0 TR Dc GM ne lvls ≤ Nat.card (Subgroup.closure S) := by
  rcases Nat.eq_zero_or_pos (chainRun FT ET LET W0 TR Dc GM ne lvls) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hET := chainRun_mem P hG hpos
  have key := chainInv_land P (listRec_strict (chLevel ET ne) (ChainInv P (Subgroup.closure S))
    (fun _ _ h => chLevel_inv P hET h) lvls (nat_lit 1) (chainInv_one P _))
  unfold chainRun
  cases rngAll (nat_lit 0) ne (Nat.add (Nat.shiftRight ne (nat_lit 6)) (nat_lit 1))
    (etOK FT ET LET W0 TR Dc GM)
  · exact Nat.zero_le _
  · exact key

end CFSG.Certificates.J4Chain

end
