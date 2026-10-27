module

public import Certificates.Data.Kernel.M23AutK
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KC.M23Aut

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P

theorem nth_eq (l : List ℕ) (k : ℕ) : nth l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    cases k with
    | zero =>
      rw [List.getD_cons_zero]
      rfl
    | succ k =>
      rw [List.getD_cons_succ]
      exact ih k

theorem eqLK_eq : ∀ {a b : List ℕ}, eqLK a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    change andB (Nat.beq x y) (eqLK a b) = true at h
    rw [andB_iff, beq_iff] at h
    rw [h.1, eqLK_eq h.2]

theorem cntN_eq (N : ℕ) (f : ℕ → Bool) :
    cntN N f = ((Finset.range N).filter fun i => f i = true).card := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change Nat.add (cntN N f) (Bool.rec (motive := fun _ => ℕ) 0 1 (f N)) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases h : f N <;> simp

theorem repIn_iff (R : List (ℕ × List (ℕ × ℕ))) (ri : ℕ) :
    repIn R ri = true ↔ ∃ r ∈ R, r.1 = ri := by
  induction R with
  | nil =>
    change false = true ↔ _
    simp
  | cons r R ih =>
    change orB (Nat.beq r.1 ri) (repIn R ri) = true ↔ _
    rw [orB_iff, beq_iff, ih]
    simp

theorem anyW_iff (W : List (ℕ × ℕ)) (j : ℕ) (g : ℕ → Bool) :
    anyW W j g = true ↔ ∃ jg ∈ W, jg.1 = j ∧ g jg.2 = true := by
  induction W with
  | nil =>
    change false = true ↔ _
    simp
  | cons jg W ih =>
    change orB (andB (Nat.beq jg.1 j) (g jg.2)) (anyW W j g) = true ↔ _
    rw [orB_iff, andB_iff, beq_iff, ih]
    simp

theorem pwK_iff (n e : ℕ) (S : List ℕ) (pW : List (List ℕ)) :
    pwK n e S pW = true ↔ ∀ w ∈ pW, inPbarK (evK n e S w) = true := by
  induction pW with
  | nil =>
    change true = true ↔ _
    simp
  | cons w pW ih =>
    change andB (inPbarK (evK n e S w)) (pwK n e S pW) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem iwK_iff (n e : ℕ) (S : List ℕ) (g : ℕ) (iWT : List (List ℕ × ℕ)) :
    iwK n e S g iWT = true ↔ ∀ wt ∈ iWT, mul n (evK n e S wt.1) g = mul n g wt.2 := by
  induction iWT with
  | nil =>
    change true = true ↔ _
    simp
  | cons wt iWT ih =>
    change andB (Nat.beq (mul n (evK n e S wt.1) g) (mul n g wt.2)) (iwK n e S g iWT) = true ↔ _
    rw [andB_iff, beq_iff, ih]
    simp

theorem scanK_iff (n e N pt PT : ℕ) (I2 : List ℕ) (pW : List (List ℕ))
    (iWT : List (List ℕ × ℕ)) (R : List (ℕ × List (ℕ × ℕ))) :
    scanK n e N pt PT I2 pW iWT R = true ↔ ∀ r ∈ R, repK n e N pt PT I2 pW iWT r = true := by
  induction R with
  | nil =>
    change true = true ↔ _
    simp
  | cons r R ih =>
    change andB (repK n e N pt PT I2 pW iWT r) (scanK n e N pt PT I2 pW iWT R) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem repK_iff (n e N pt PT : ℕ) (I2 : List ℕ) (pW : List (List ℕ))
    (iWT : List (List ℕ × ℕ)) (r : ℕ × List (ℕ × ℕ)) :
    repK n e N pt PT I2 pW iWT r = true ↔ r.1 < N ∧ ∀ j ∈ I2,
      ord5K n e (mul n (tC n PT r.1) (tC n PT j)) = true →
      pwK n e (withInv n [tC n PT r.1, tC n PT j]) pW = true →
      ∃ jg ∈ r.2, jg.1 = j ∧ jg.2 < N ∧ img (tC n PT jg.2) pt = pt ∧
        iwK n e (withInv n [tC n PT r.1, tC n PT j]) (tC n PT jg.2) iWT = true := by
  simp only [repK, letB_eq, andB_iff, blt_iff, allL_iff, impB_iff, anyW_iff, beq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj h5 hp => h2 j hj ⟨h5, hp⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj h => h2 j hj h.1 h.2⟩

theorem invAt_iff (n e PT : ℕ) (I2 : List ℕ) (j : ℕ) :
    invAt n e PT I2 j = true ↔ (ord2K n e (tC n PT j) = true → j ∈ I2) := by
  rw [invAt, impB_iff, anyL_iff]
  simp only [beq_iff]
  constructor
  · intro h h2
    obtain ⟨x, hx, rfl⟩ := h h2
    exact hx
  · intro h h2
    exact ⟨j, h h2, rfl⟩

theorem orbAt_iff (n e N pt PT PC PR : ℕ) (R : List (ℕ × List (ℕ × ℕ))) (i : ℕ) :
    orbAt n e N pt PT PC PR R i = true ↔ (ord8K n e (tC n PT i) = true →
      fl PC 16 i < N ∧ repIn R (fl PR 16 i) = true ∧ img (tC n PT (fl PC 16 i)) pt = pt ∧
        mul n (tC n PT (fl PC 16 i)) (tC n PT i) =
          mul n (tC n PT (fl PR 16 i)) (tC n PT (fl PC 16 i))) := by
  simp only [orbAt, letB_eq, impB_iff, andB_iff, blt_iff, beq_iff]

theorem sepK_iff (n x f c d : ℕ) : sepK n x f c d = true ↔
    (d = 0 → mul n x f ≠ mul n c x) ∧ (d ≠ 0 → mul n f x ≠ mul n x c) := by
  unfold sepK
  cases h : Nat.beq d 0
  · have hd : d ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
    change notB (Nat.beq (mul n f x) (mul n x c)) = true ↔ _
    rw [notB_iff, beq_iff]
    exact ⟨fun h1 => ⟨fun e => absurd e hd, fun _ => h1⟩, fun h1 => h1.2 hd⟩
  · have hd : d = 0 := beq_iff.1 h
    change notB (Nat.beq (mul n x f) (mul n c x)) = true ↔ _
    rw [notB_iff, beq_iff]
    exact ⟨fun h1 => ⟨fun _ => h1, fun e => absurd hd e⟩, fun h1 => h1.1 hd⟩

theorem autAt_iff (n e PT lX : ℕ) (FW : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    autAt n e PT lX FW i = true ↔ (ord3K n e (tC n PT i) = true → tC n PT i ≠ lX →
      ∃ r ∈ FW, sepK n (tC n PT i) (tC n PT r.1) (tC n PT r.2.1) r.2.2 = true) := by
  have hL : ∀ L : List (ℕ × ℕ × ℕ), List.rec (motive := fun _ => Bool) false
      (fun r _ ih => orB (sepK n (tC n PT i) (tC n PT r.1) (tC n PT r.2.1) r.2.2) ih) L = true ↔
      ∃ r ∈ L, sepK n (tC n PT i) (tC n PT r.1) (tC n PT r.2.1) r.2.2 = true := by
    intro L
    induction L with
    | nil =>
      change false = true ↔ _
      simp
    | cons r L ih =>
      change orB _ (List.rec (motive := fun _ => Bool) false _ L) = true ↔ _
      rw [orB_iff, ih]
      simp
  rw [autAt, letB_eq, impB_iff, andB_iff, notB_iff, beq_iff, hL]
  exact ⟨fun h h3 hx => h ⟨h3, hx⟩, fun h hh => h hh.1 hh.2⟩

theorem fwOK_iff (n N PT lX : ℕ) (FW : List (ℕ × ℕ × ℕ)) :
    fwOK n N PT lX FW = true ↔ ∀ r ∈ FW, r.1 < N ∧ r.2.1 < N ∧
      inF4K (tC n PT r.1) = true ∧ inF4K (tC n PT r.2.1) = true ∧
      (r.2.2 = 0 → mul n (tC n PT r.2.1) lX = mul n lX (tC n PT r.1)) ∧
      (r.2.2 ≠ 0 → mul n lX (tC n PT r.2.1) = mul n (tC n PT r.1) lX) := by
  induction FW with
  | nil =>
    change true = true ↔ _
    simp
  | cons r FW ih =>
    have hb : Bool.rec (motive := fun _ => Bool)
        (Nat.beq (mul n lX (tC n PT r.2.1)) (mul n (tC n PT r.1) lX))
        (Nat.beq (mul n (tC n PT r.2.1) lX) (mul n lX (tC n PT r.1))) (Nat.beq r.2.2 0) = true ↔
        (r.2.2 = 0 → mul n (tC n PT r.2.1) lX = mul n lX (tC n PT r.1)) ∧
        (r.2.2 ≠ 0 → mul n lX (tC n PT r.2.1) = mul n (tC n PT r.1) lX) := by
      cases h : Nat.beq r.2.2 0
      · have hd : r.2.2 ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
        change Nat.beq _ _ = true ↔ _
        rw [beq_iff]
        exact ⟨fun h1 => ⟨fun e => absurd e hd, fun _ => h1⟩, fun h1 => h1.2 hd⟩
      · have hd : r.2.2 = 0 := beq_iff.1 h
        change Nat.beq _ _ = true ↔ _
        rw [beq_iff]
        exact ⟨fun h1 => ⟨fun _ => h1, fun e => absurd hd e⟩, fun h1 => h1.1 hd⟩
    change andB (andB (Nat.blt r.1 N) (Nat.blt r.2.1 N))
      (letB (tC n PT r.1) fun f => letB (tC n PT r.2.1) fun c =>
        andB (andB (inF4K f) (inF4K c))
          (andB (Bool.rec (motive := fun _ => Bool) (Nat.beq (mul n lX c) (mul n f lX))
            (Nat.beq (mul n c lX) (mul n lX f)) (Nat.beq r.2.2 0))
            (fwOK n N PT lX FW))) = true ↔ _
    rw [letB_eq, letB_eq]
    simp only [andB_iff, blt_iff, hb, ih, List.mem_cons, forall_eq_or_imp]
    tauto

@[expose] def prodW {M : Type*} [Monoid M] (S : List M) (w : List ℕ) : M :=
  (w.map fun l => S.getD l 1).prod

theorem prodW_nil {M : Type*} [Monoid M] (S : List M) : prodW S [] = 1 := rfl

theorem prodW_cons {M : Type*} [Monoid M] (S : List M) (l : ℕ) (w : List ℕ) :
    prodW S (l :: w) = S.getD l 1 * prodW S w := by
  rw [prodW, List.map_cons, List.prod_cons, ← prodW]

theorem map_prodW {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N) (S : List M) (w : List ℕ) :
    φ (prodW S w) = prodW (S.map φ) w := by
  have hget : ∀ l, (S.map φ).getD l 1 = φ (S.getD l 1) := by
    intro l
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases S[l]? <;> simp
  induction w with
  | nil => rw [prodW_nil, prodW_nil, map_one]
  | cons l w ih =>
    rw [prodW_cons, prodW_cons, map_mul, ih, hget]

variable {n : ℕ} {G : Type*} [Group G] (f : G →* Perm (Fin n))

theorem nth_map_code (S : List G) {k : ℕ} (hk : k < S.length) :
    nth (S.map fun g => code (f g)) k = code (f S[k]) := by
  rw [nth_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

theorem evAcc_hom (hn : n ≤ 32) (S : List G) : ∀ (w : List ℕ), (∀ l ∈ w, l < S.length) →
    ∀ a : G, evAcc n (S.map fun g => code (f g)) w (code (f a)) = code (f (a * prodW S w))
  | [], _, a => by
    rw [prodW_nil, mul_one]
    rfl
  | l :: w, hw, a => by
    have hl : l < S.length := hw l List.mem_cons_self
    have e1 : evAcc n (S.map fun g => code (f g)) (l :: w) (code (f a)) =
        evAcc n (S.map fun g => code (f g)) w
          (mul n (code (f a)) (nth (S.map fun g => code (f g)) l)) :=
      CFSG.KS.Raw.Orb.strictN_eq _ _
    have e2 : S.getD l 1 = S[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
      rfl
    rw [e1, nth_map_code f S hl, code_mul hn, ← map_mul,
      evAcc_hom hn S w (fun l' h => hw l' (List.mem_cons_of_mem _ h)), prodW_cons, e2, mul_assoc]

theorem evK_hom (hn : n ≤ 32) (S : List G) (w : List ℕ) (hw : ∀ l ∈ w, l < S.length) :
    evK n (one n) (S.map fun g => code (f g)) w = code (f (prodW S w)) := by
  rw [evK, code_one, ← map_one f, evAcc_hom f hn S w hw, one_mul]

theorem withInv_hom (hn : n ≤ 32) (S : List G) :
    withInv n (S.map fun g => code (f g)) = (S ++ S.map (·⁻¹)).map fun g => code (f g) := by
  rw [withInv, List.map_append, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => by
    simp only [Function.comp, map_inv, code_inv hn]

theorem treeK_sound (hn : n ≤ 32) {N PT PP PG PD : ℕ} {Gs : List G}
    (h : treeK n (one n) N (Gs.map fun g => code (f g)) PT PP PG PD = true)
    (hg : ∀ i < N, fl PG 4 i < Gs.length) :
    (∀ i < N, ∃ g ∈ Subgroup.closure {x | x ∈ Gs}, code (f g) = tC n PT i) ∧
      ∀ i j, i < j → j < N → tC n PT i < tC n PT j := by
  have hrec := CFSG.KS.Raw.Orb.allN_iff.1 h
  have hstep : ∀ i < N, (i + 1 < N → tC n PT i < tC n PT (i + 1)) ∧
      (fl PD (nat_lit 8) i = 0 → tC n PT i = one n) ∧
      (fl PD (nat_lit 8) i ≠ 0 → fl PP 16 i < N ∧
        fl PD (nat_lit 8) (fl PP 16 i) + 1 = fl PD (nat_lit 8) i ∧
        tC n PT i = mul n (nth (Gs.map fun g => code (f g)) (fl PG 4 i))
          (tC n PT (fl PP 16 i))) := by
    intro i hi
    have h1 := hrec i hi
    rw [treeAt, letB_eq, andB_iff, impB_iff, blt_iff, blt_iff, letB_eq] at h1
    obtain ⟨h1, h2⟩ := h1
    refine ⟨h1, fun hd => ?_, fun hd => ?_⟩
    · cases hb : Nat.beq (fl PD (nat_lit 8) i) (nat_lit 0)
      · exact absurd (beq_iff.2 hd) (by rw [hb]; decide)
      · rw [hb] at h2
        exact beq_iff.1 h2
    · cases hb : Nat.beq (fl PD (nat_lit 8) i) (nat_lit 0)
      · rw [hb, letB_eq, andB_iff, andB_iff, blt_iff, beq_iff, beq_iff] at h2
        exact ⟨h2.1, h2.2.1, h2.2.2⟩
      · exact absurd (beq_iff.1 hb) hd
  refine ⟨?_, ?_⟩
  · have key : ∀ d, ∀ i < N, fl PD (nat_lit 8) i = d →
        ∃ g ∈ Subgroup.closure {x | x ∈ Gs}, code (f g) = tC n PT i := by
      intro d
      induction d with
      | zero =>
        intro i hi hd
        exact ⟨1, Subgroup.one_mem _, by rw [map_one, ← code_one, (hstep i hi).2.1 hd]⟩
      | succ d ih =>
        intro i hi hd
        obtain ⟨hp, hpd, ht⟩ := (hstep i hi).2.2 (by omega)
        obtain ⟨g, hgm, hgc⟩ := ih _ hp (by omega)
        have hk := hg i hi
        refine ⟨Gs[fl PG 4 i] * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure (List.getElem_mem hk)) hgm, ?_⟩
        rw [ht, nth_map_code f Gs hk, ← hgc, code_mul hn, map_mul]
    exact fun i hi => key _ i hi rfl
  · intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact lt_trans (ih h' (by omega)) ((hstep j (by omega)).1 hj)
      · exact (hstep i (by omega)).1 hj

theorem tC_inj {N PT : ℕ} (hmono : ∀ i j, i < j → j < N → tC n PT i < tC n PT j) {i j : ℕ}
    (hi : i < N) (hj : j < N) (h : tC n PT i = tC n PT j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd h (ne_of_lt (hmono _ _ h' hj))
  · exact h'
  · exact absurd h.symm (ne_of_lt (hmono _ _ h' hi))

theorem listed_all {X : Type*} [Group X] [Finite X] (φ : X →* Perm (Fin n)) {N PT : ℕ}
    (hex : ∀ i < N, ∃ g : X, code (φ g) = tC n PT i)
    (hmono : ∀ i j, i < j → j < N → tC n PT i < tC n PT j) (hcard : Nat.card X ≤ N) (x : X) :
    ∃ i < N, code (φ x) = tC n PT i := by
  classical
  have : Fintype X := Fintype.ofFinite X
  choose F hF using fun i : Fin N => hex i i.isLt
  have hinj : Function.Injective F := by
    intro i j hij
    have h := (hF i).symm.trans ((congrArg (fun g => code (φ g)) hij).trans (hF j))
    exact Fin.ext (tC_inj hmono i.isLt j.isLt h)
  have hsub : Finset.univ.image F ⊆ Finset.univ := Finset.subset_univ _
  have hc : (Finset.univ : Finset X).card ≤ (Finset.univ.image F).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hcard
  have hx : x ∈ Finset.univ.image F := by
    rw [Finset.eq_of_subset_of_card_le hsub hc]
    exact Finset.mem_univ x
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  exact ⟨i, i.isLt, hF i⟩

theorem ord8K_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    ord8K n (one n) (code σ) = true ↔ σ ^ 4 ≠ 1 ∧ σ ^ 8 = 1 := by
  simp only [ord8K, letB_eq, code_mul hn, code_one, andB_iff, notB_iff, beq_code hn]
  have e4 : σ * σ * (σ * σ) = σ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e8 : σ * σ * (σ * σ) * (σ * σ * (σ * σ)) = σ ^ 8 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e8, e4, ne_eq]

theorem ord2K_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    ord2K n (one n) (code σ) = true ↔ σ ≠ 1 ∧ σ ^ 2 = 1 := by
  simp only [ord2K, code_mul hn, code_one, andB_iff, notB_iff, beq_code hn, pow_two]

theorem ord5K_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    ord5K n (one n) (code σ) = true ↔ σ ≠ 1 ∧ σ ^ 5 = 1 := by
  simp only [ord5K, letB_eq, code_mul hn, code_one, andB_iff, notB_iff, beq_code hn]
  have e5 : σ * σ * (σ * σ) * σ = σ ^ 5 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e5, ne_eq]

theorem ord3K_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    ord3K n (one n) (code σ) = true ↔ σ ≠ 1 ∧ σ ^ 3 = 1 := by
  simp only [ord3K, code_mul hn, code_one, andB_iff, notB_iff, beq_code hn]
  have e3 : σ * σ * σ = σ ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e3, ne_eq]

theorem fixK_iff (t : ℕ) (F : List ℕ) : fixK t F = true ↔ ∀ p ∈ F, img t p = p := by
  simp only [fixK, allL_iff, beq_iff]

theorem setK_iff (t : ℕ) (B : List ℕ) : setK t B = true ↔ ∀ p ∈ B, img t p ∈ B := by
  simp only [setK, allL_iff, anyL_iff, beq_iff, exists_eq_right']

theorem pairK_iff (t a b : ℕ) : pairK t a b = true ↔
    (img t a = a ∧ img t b = b) ∨ (img t a = b ∧ img t b = a) := by
  simp only [pairK, orB_iff, andB_iff, beq_iff]

end CFSG.KC.M23Aut

end
