module

public import Certificates.Data.Kernel.Fin76bAutFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.EvenSporadicStandard.Fin76b.AutETable

theorem beq_t {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem eBEq_iff {a b : Bool} : eBEq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem eCm_iff {ET : ℕ → ℕ} {x y : ℕ} : eCm ET x y = true ↔ eMul ET x y = eMul ET y x := beq_t

theorem eZ_spec {x : ℕ} (h : eZ x = true) : x = 0 ∨ x = 21 := by
  unfold eZ at h
  cases h0 : Nat.beq x (nat_lit 0)
  · rw [h0] at h
    exact Or.inr (Nat.eq_of_beq_eq_true h)
  · exact Or.inl (Nat.eq_of_beq_eq_true h0)

theorem eG_eq (p i : ℕ) : eG p i = p / 2 ^ (6 * i) % 64 := by
  have h := pg_eq 6 p i
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
  exact h

theorem lor_shl_eq {X x n : ℕ} (hX : X < 2 ^ n) : Nat.lor X (Nat.shiftLeft x n) = X + x * 2 ^ n := by
  change X ||| x <<< n = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hX, Nat.shiftLeft_eq, Nat.add_comm]

theorem eG_pack {X x d i : ℕ} (hX : X < 2 ^ (6 * d)) (hx : x < 64) (hi : i ≤ d) :
    eG (Nat.lor X (Nat.shiftLeft x (Nat.mul 6 d))) i = if i < d then eG X i else x := by
  rw [show Nat.mul 6 d = 6 * d from rfl, lor_shl_eq hX, eG_eq, eG_eq]
  split_ifs with h
  · obtain ⟨e, rfl⟩ : ∃ e, d = i + 1 + e := ⟨d - i - 1, by omega⟩
    have h2 : x * 2 ^ (6 * (i + 1 + e)) = x * 2 ^ (6 * e) * 64 * 2 ^ (6 * i) := by
      rw [show 6 * (i + 1 + e) = 6 * i + 6 + 6 * e by ring, pow_add, pow_add]
      norm_num
      ring
    rw [h2, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
  · have hid : i = d := by omega
    subst hid
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hX, zero_add,
      Nat.mod_eq_of_lt hx]

theorem pack_lt {X x d : ℕ} (hX : X < 2 ^ (6 * d)) (hx : x < 64) :
    Nat.lor X (Nat.shiftLeft x (Nat.mul 6 d)) < 2 ^ (6 * (d + 1)) := by
  rw [show Nat.mul 6 d = 6 * d from rfl, lor_shl_eq hX, show 6 * (d + 1) = 6 * d + 6 by ring,
    pow_add]
  have h1 : x * 2 ^ (6 * d) ≤ 63 * 2 ^ (6 * d) := Nat.mul_le_mul_right _ (by omega)
  norm_num
  linarith

theorem foldUp_inv {P : ℕ → Prop} {n : ℕ} {f : ℕ → ℕ → ℕ} {s : ℕ} (h0 : P s)
    (hf : ∀ i < n, ∀ s, P s → P (f i s)) : P (foldUp n f s) := by
  rw [foldUp_eq]
  suffices H : ∀ l : List ℕ, (∀ i ∈ l, i < n) → ∀ s, P s → P (l.foldl (fun s i => f i s) s) from
    H _ (fun i hi => List.mem_range.1 hi) s h0
  intro l
  induction l with
  | nil => intro _ s hs; exact hs
  | cons i l ih =>
    intro hl s hs
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
      (hf i (hl i List.mem_cons_self) s hs)

theorem foldl_count (c : ℕ → Bool) (v : ℕ → ℕ) : ∀ (l : List ℕ) (s : ℕ),
    l.foldl (fun s i => Bool.rec (motive := fun _ => ℕ) s (Nat.add s (v i)) (c i)) s =
      s + (l.map fun i => if c i = true then v i else 0).sum := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons i l ih =>
    intro s
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    cases c i <;> simp <;> omega

theorem list_sum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

def TupAdm (ET : ℕ → ℕ) (GN : ℕ) : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | d, X, x :: xs => x < 32 ∧ eTupOk ET GN d X x = true ∧
      TupAdm ET GN (d + 1) (Nat.lor X (Nat.shiftLeft x (Nat.mul 6 d))) xs

theorem eTupRec_succ (ET : ℕ → ℕ) (GN r d X : ℕ) :
    eTupRec ET GN (r + 1) d X = ∑ x ∈ Finset.range 32, if eTupOk ET GN d X x = true then
      eTupRec ET GN r (d + 1) (Nat.lor X (Nat.shiftLeft x (Nat.mul 6 d))) else 0 := by
  have h : eTupRec ET GN (r + 1) d X = foldUp 32 (fun x acc =>
      Bool.rec (motive := fun _ => ℕ) acc
        (Nat.add acc (eTupRec ET GN r (d + 1) (Nat.lor X (Nat.shiftLeft x (Nat.mul 6 d)))))
        (eTupOk ET GN d X x)) 0 := rfl
  rw [h, foldUp_eq, foldl_count, zero_add, list_sum_range]

theorem cons_of_adm {ET : ℕ → ℕ} {GN d X r : ℕ} {l : List ℕ} (hl : l.length = r + 1)
    (ha : TupAdm ET GN d X l) : ∃ y ys, l = y :: ys ∧ ys.length = r ∧ y < 32 ∧
      eTupOk ET GN d X y = true ∧
      TupAdm ET GN (d + 1) (Nat.lor X (Nat.shiftLeft y (Nat.mul 6 d))) ys := by
  cases l with
  | nil => simp at hl
  | cons y ys => exact ⟨y, ys, rfl, by simpa using hl, ha.1, ha.2.1, ha.2.2⟩

theorem card_le_eTupRec (ET : ℕ → ℕ) (GN : ℕ) {α : Type*} [DecidableEq α] : ∀ (r : ℕ)
    (F : α → List ℕ) (d X : ℕ) (S : Finset α),
    (∀ a ∈ S, (F a).length = r ∧ TupAdm ET GN d X (F a)) → Set.InjOn F S →
    S.card ≤ eTupRec ET GN r d X := by
  intro r
  induction r with
  | zero =>
    intro F d X S hS hinj
    refine Finset.card_le_one.2 fun a ha b hb => hinj ha hb ?_
    rw [List.eq_nil_of_length_eq_zero (hS a ha).1, List.eq_nil_of_length_eq_zero (hS b hb).1]
  | succ r ih =>
    intro F d X S hS hinj
    rw [eTupRec_succ, Finset.card_eq_sum_card_fiberwise (f := fun a => (F a).headD 0)
      (t := Finset.range 32) fun a ha => ?_]
    · refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with hok
      · refine ih (fun a => (F a).tail) (d + 1) _ _ (fun a ha => ?_) (fun a ha b hb hab => ?_)
        · obtain ⟨haS, hax⟩ := Finset.mem_filter.1 ha
          obtain ⟨y, ys, hF, hlen, -, -, hadm⟩ := cons_of_adm (hS a haS).1 (hS a haS).2
          simp only [hF, List.headD_cons] at hax
          subst hax
          simpa [hF] using ⟨hlen, hadm⟩
        · obtain ⟨haS, hax⟩ := Finset.mem_filter.1 ha
          obtain ⟨hbS, hbx⟩ := Finset.mem_filter.1 hb
          obtain ⟨y, ys, hF, -⟩ := cons_of_adm (hS a haS).1 (hS a haS).2
          obtain ⟨y', ys', hF', -⟩ := cons_of_adm (hS b hbS).1 (hS b hbS).2
          simp only [hF, List.headD_cons] at hax
          simp only [hF', List.headD_cons] at hbx
          simp only [hF, hF', List.tail_cons] at hab
          refine hinj haS hbS ?_
          rw [hF, hF', hax, hbx, hab]
      · refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a ha hax => ?_))
        obtain ⟨y, ys, hF, -, -, hy, -⟩ := cons_of_adm (hS a ha).1 (hS a ha).2
        simp only [hF, List.headD_cons] at hax
        exact hok (hax ▸ hy)
    · obtain ⟨y, ys, hF, -, hy, -⟩ := cons_of_adm (hS a ha).1 (hS a ha).2
      simpa [hF] using hy

section Aut

variable {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)

include R hM

theorem tmul_lt {a b : ℕ} (ha : a < 32) (hb : b < 32) : eMul ET a b < 32 :=
  hM a ha b hb ▸ R.lt a b ha hb

theorem sg_tmul (φ : MulAut H) {a b : ℕ} (ha : a < 32) (hb : b < 32) :
    sg R φ (eMul ET a b) = eMul ET (sg R φ a) (sg R φ b) := by
  rw [← hM a ha b hb, sg_mt R φ ha hb, hM _ (sg_lt R φ a) _ (sg_lt R φ b)]

omit hM in
theorem sg_inj (φ : MulAut H) {a b : ℕ} (ha : a < 32) (hb : b < 32) (h : sg R φ a = sg R φ b) :
    a = b :=
  R.inj a b ha hb (φ.injective (by rw [← sg_elt R φ a, ← sg_elt R φ b, h]))

omit hM in
theorem sg_surj (φ : MulAut H) {z : ℕ} (hz : z < 32) : sg R φ (sg R φ⁻¹ z) = z := by
  rw [← sg_mul, mul_inv_cancel, sg_one R hz]

def Cen (ET : ℕ → ℕ) (y : ℕ) : Prop := ∀ z < 32, eMul ET y z = eMul ET z y

theorem cen_sg (φ : MulAut H) {y : ℕ} (hy : y < 32) : Cen ET (sg R φ y) ↔ Cen ET y := by
  constructor
  · intro h z hz
    apply sg_inj R φ (tmul_lt R hM hy hz) (tmul_lt R hM hz hy)
    rw [sg_tmul R hM φ hy hz, sg_tmul R hM φ hz hy]
    exact h _ (sg_lt R φ z)
  · intro h z hz
    rw [← sg_surj R φ hz, ← sg_tmul R hM φ hy (sg_lt R _ z), ← sg_tmul R hM φ (sg_lt R _ z) hy,
      h _ (sg_lt R _ z)]

omit R hM in
theorem ctr_spec (h : eCtrK ET = true) {x : ℕ} (hx : x < 32) : eZ x = true ↔ Cen ET x := by
  have h1 := eBEq_iff.1 ((allN_iff.1 h) x hx)
  rw [← h1, allN_iff]
  exact forall₂_congr fun z _ => eCm_iff

theorem sg_eZ (hc : eCtrK ET = true) (φ : MulAut H) {y : ℕ} (hy : y < 32) :
    eZ (sg R φ y) = eZ y :=
  Bool.eq_iff_iff.2 ((ctr_spec hc (sg_lt R φ y)).trans ((cen_sg R hM φ hy).trans (ctr_spec hc hy).symm))

theorem sg_21 (hc : eCtrK ET = true) (φ : MulAut H) : sg R φ 21 = 21 := by
  have h1 : eZ (sg R φ 21) = true := by rw [sg_eZ R hM hc φ (by norm_num)]; rfl
  rcases eZ_spec h1 with h0 | h21
  · rw [← sg_zero R φ] at h0
    exact absurd (sg_inj R φ (by norm_num) (by norm_num) h0) (by norm_num)
  · exact h21

theorem sg_cm (φ : MulAut H) {a b : ℕ} (ha : a < 32) (hb : b < 32) :
    eCm ET (sg R φ a) (sg R φ b) = eCm ET a b := by
  refine Bool.eq_iff_iff.2 ((eCm_iff).trans (Iff.trans ?_ eCm_iff.symm))
  rw [← sg_tmul R hM φ ha hb, ← sg_tmul R hM φ hb ha]
  exact ⟨sg_inj R φ (tmul_lt R hM ha hb) (tmul_lt R hM hb ha), fun h => by rw [h]⟩

theorem adm_tup (hc : eCtrK ET = true) {GN k : ℕ}
    (hg : ∀ d < k, eG GN d < 32 ∧ eZ (eMul ET (eG GN d) (eG GN d)) = true) (φ : MulAut H) :
    ∀ m d X, d + m = k → X < 2 ^ (6 * d) → (∀ i < d, eG X i = sg R φ (eG GN i)) →
      TupAdm ET GN d X ((List.range' d m).map fun i => sg R φ (eG GN i)) := by
  intro m
  induction m with
  | zero => intro d X _ _ _; trivial
  | succ m ih =>
    intro d X hdm hX hXi
    have hd : d < k := by omega
    obtain ⟨hgd, hzd⟩ := hg d hd
    have hx : sg R φ (eG GN d) < 32 := sg_lt R φ _
    change TupAdm ET GN d X (sg R φ (eG GN d) ::
      (List.range' (d + 1) m).map fun i => sg R φ (eG GN i))
    refine ⟨hx, ?_, ih (d + 1) _ (by omega) (pack_lt hX (by omega)) fun i hi => ?_⟩
    · unfold eTupOk
      rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨eBEq_iff.2 (sg_eZ R hM hc φ hgd), ?_, allN_iff.2 fun i hi => eBEq_iff.2 ?_⟩
      · rw [← sg_tmul R hM φ hgd hgd]
        rcases eZ_spec hzd with h0 | h21
        · rw [h0, sg_zero]
          exact beq_t.2 rfl
        · rw [h21, sg_21 R hM hc]
          exact beq_t.2 rfl
      · rw [hXi i hi, sg_cm R hM φ (hg i (by omega)).1 hgd]
    · rw [eG_pack hX (by omega) (by omega)]
      split_ifs with h
      · exact hXi i h
      · rw [show i = d by omega]

theorem sg_eq_of_gen {S k f : ℕ} (hS : ∀ j < k, eG S j < 32) (hgen : eGenK ET S k f = true)
    (φ ψ : MulAut H) (h : ∀ j < k, sg R φ (eG S j) = sg R ψ (eG S j)) :
    ∀ a < 32, sg R φ a = sg R ψ a := by
  let Good : ℕ → Prop := fun X => ∀ b, X.testBit b = true → b < 32 ∧ sg R φ b = sg R ψ b
  have hstep : ∀ X, Good X → Good (eGenStep ET S k X) := by
    intro X hX
    unfold eGenStep
    refine foldUp_inv hX fun a ha s hs => ?_
    rw [nIf_eq]
    split_ifs with hb
    · rw [hasBit_eq] at hb
      obtain ⟨-, hab⟩ := hX a hb
      refine foldUp_inv hs fun j hj s' hs' b hbit => ?_
      have hlor : Nat.lor s' (Nat.shiftLeft (nat_lit 1) (eMul ET a (eG S j))) =
          s' ||| 2 ^ eMul ET a (eG S j) := by
        rw [← one_mul (2 ^ eMul ET a (eG S j)), ← Nat.shiftLeft_eq]
        rfl
      rw [hlor, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hbit
      rcases hbit with hbit | hbit
      · exact hs' b hbit
      · have hbm : eMul ET a (eG S j) = b := of_decide_eq_true hbit
        subst hbm
        refine ⟨tmul_lt R hM ha (hS j hj), ?_⟩
        rw [sg_tmul R hM φ ha (hS j hj), sg_tmul R hM ψ ha (hS j hj), hab, h j hj]
    · exact hs
  have hreach : ∀ f, Good (eGenReach ET S k f) := by
    intro f
    induction f with
    | zero =>
      intro b hb
      change (2 ^ 0 : ℕ).testBit b = true at hb
      rw [Nat.testBit_two_pow] at hb
      have hb0 : b = 0 := (of_decide_eq_true hb).symm
      subst hb0
      exact ⟨by norm_num, by rw [sg_zero, sg_zero]⟩
    | succ f ih =>
      change Good (strictN (eGenReach ET S k f) (fun X => eGenStep ET S k X))
      rw [strictN_eq]
      exact hstep _ ih
  have hfull : eGenReach ET S k f = 2 ^ 32 - 1 := beq_t.1 hgen
  intro a ha
  refine (hreach f a ?_).2
  rw [hfull, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true ha

omit hM in
theorem mulAut_ext_sg {φ ψ : MulAut H} (h : ∀ a < 32, sg R φ a = sg R ψ a) : φ = ψ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨k, hk, rfl⟩ := R.surj x
  rw [← sg_elt R φ k, ← sg_elt R ψ k, h k hk]

theorem card_aut_le {GN k f c : ℕ} (h : eTupK ET GN k f c = true) : Nat.card (MulAut H) ≤ c := by
  classical
  simp only [eTupK, bAnd_eq, Bool.and_eq_true, allN_iff, strictB_eq] at h
  obtain ⟨hc, hg, hgen, hcnt⟩ := h
  have hg' : ∀ d < k, eG GN d < 32 ∧ eZ (eMul ET (eG GN d) (eG GN d)) = true := fun d hd =>
    ⟨Nat.le_of_ble_eq_true (hg d hd).1, (hg d hd).2⟩
  have hfin : Finite (MulAut H) := Finite.of_injective
    (fun φ : MulAut H => fun i : Fin 32 => (⟨sg R φ i, sg_lt R φ i⟩ : Fin 32))
    fun φ ψ hφψ => mulAut_ext_sg R fun a ha => by
      have := congrFun hφψ ⟨a, ha⟩
      simpa using this
  have : Fintype (MulAut H) := Fintype.ofFinite _
  let F : MulAut H → List ℕ := fun φ => (List.range' 0 k).map fun i => sg R φ (eG GN i)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← beq_t.1 hcnt]
  refine card_le_eTupRec ET GN k F 0 0 Finset.univ (fun φ _ => ⟨by simp [F], ?_⟩)
    (fun φ _ ψ _ hφψ => ?_)
  · exact adm_tup R hM hc hg' φ k 0 0 (by omega) (by norm_num) fun i hi => absurd hi (by omega)
  · refine mulAut_ext_sg R (sg_eq_of_gen R hM (fun j hj => (hg' j hj).1) hgen φ ψ fun j hj => ?_)
    have h1 := congrArg (fun l : List ℕ => l.getD j 0) hφψ
    simp only [F, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range',
      show j < k from hj, if_true] at h1
    simpa using h1

end Aut

theorem eTabK_spec {ET : ℕ → ℕ} {mul : ℕ → ℕ → ℕ} (h : eTabK ET mul = true) :
    ∀ a < 32, ∀ b < 32, eMul ET a b = mul a b := by
  intro a ha b hb
  simp only [eTabK, bAnd_eq, Bool.and_eq_true, allN_iff] at h
  exact beq_t.1 ((h a ha).2 b hb)

end CFSG.KS.EAut

end
