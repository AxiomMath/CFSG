module

public import Certificates.Data.Kernel.S5Ext.Check
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KD.S5Ext

@[expose] def IsAutN (f : Nat → Nat) : Prop :=
  (∀ x, x < 32 → f x < 32) ∧ (∀ x y, x < 32 → y < 32 → f (pm x y) = pm (f x) (f y)) ∧
    ∀ x y, x < 32 → y < 32 → f x = f y → x = y

@[expose] def HasKey (f : Nat → Nat) (k : Nat) : Prop :=
  f 1 = k >>> 15 ∧ f 2 = (k >>> 10) &&& 31 ∧ f 8 = (k >>> 5) &&& 31 ∧ f 16 = k &&& 31

theorem recAll {Q : Nat → Prop} {F : Nat → Bool → Bool}
    (hF : ∀ i b, F i b = true → b = true ∧ Q i) :
    ∀ n, Nat.rec (motive := fun _ => Bool) true F n = true → ∀ i, i < n → Q i := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    have hn := hF n _ h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih hn.1 i h'
    · subst h'
      exact hn.2

theorem recAnd {G : Nat → Bool} :
    ∀ n, Nat.rec (motive := fun _ => Bool) true (fun i ih => ih && G i) n = true →
      ∀ i, i < n → G i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun i ih => ih && G i) n && G n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · exact ih h'.1 i hi'
    · rw [hi']
      exact h'.2

theorem tb_iff (x i : Nat) : tb x i = true ↔ x.testBit i = true := by
  unfold tb Nat.testBit
  rw [Nat.beq_eq, Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

theorem FULL_eq : FULL = 2 ^ 128 - 1 := by decide

theorem tb_lC_lt {CATP k g : Nat} (h : tb (lC CATP k) g = true) : g < 128 := by
  rw [tb_iff] at h
  unfold lC at h
  rw [FULL_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_iff] at h
  exact h.2

theorem tb_single {L g : Nat} : tb (1 <<< L) g = true ↔ g = L := by
  rw [tb_iff, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
  exact eq_comm

theorem tb_or {x y i : Nat} : tb (x ||| y) i = true ↔ tb x i = true ∨ tb y i = true := by
  rw [tb_iff, tb_iff, tb_iff, Nat.testBit_or, Bool.or_eq_true]

theorem tb_zero {i : Nat} : tb 0 i = false := by
  cases h : tb 0 i
  · rfl
  · rw [tb_iff, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true

theorem mask_sub {w a b x : Nat} (h : a &&& ((2 ^ w - 1) ^^^ b) = 0) (hx : x < w)
    (ha : tb a x = true) : tb b x = true := by
  rw [tb_iff] at ha ⊢
  have h2 := congrArg (Nat.testBit · x) h
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
    ha] at h2
  cases hb : b.testBit x
  · simp [hb, hx] at h2
  · rfl

theorem lT_lt (T x : Nat) : lT T x < 32 := by
  unfold lT
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem lM_lt (MP g c : Nat) : lM MP g c < 128 := by
  unfold lM
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem lCI_lt (CIL t : Nat) : lCI CIL t < 128 := by
  unfold lCI
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem pm_lt : ∀ x y : Fin 32, pm x.val y.val < 32 := by decide +kernel

theorem pm_lt' {x y : Nat} (hx : x < 32) (hy : y < 32) : pm x y < 32 := pm_lt ⟨x, hx⟩ ⟨y, hy⟩

theorem pm_zero : ∀ x : Fin 32, pm x.val 0 = x.val := by decide +kernel

theorem pm_zero' {x : Nat} (hx : x < 32) : pm x 0 = x := pm_zero ⟨x, hx⟩

@[expose] noncomputable def assocZ (x y : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun z ih => ih && Nat.beq (pm (pm x y) z) (pm x (pm y z))) 32

@[expose] noncomputable def assocY (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun y ih => ih && assocZ x y) 32

theorem assocB_ok :
    Nat.rec (motive := fun _ => Bool) true (fun x ih => ih && assocY x) 32 = true := by
  decide +kernel

theorem pm_assoc {x y z : Nat} (hx : x < 32) (hy : y < 32) (hz : z < 32) :
    pm (pm x y) z = pm x (pm y z) := by
  have h1 := recAnd (G := assocY) 32 assocB_ok x hx
  have h2 := recAnd (G := assocZ x) 32 h1 y hy
  have h3 := recAnd (G := fun z => Nat.beq (pm (pm x y) z) (pm x (pm y z))) 32 h2 z hz
  exact Nat.eq_of_beq_eq_true h3

@[expose] def isGen (g : Nat) : Bool := Nat.beq g 1 || Nat.beq g 2 || Nat.beq g 8 || Nat.beq g 16

theorem isGen_lt {g : Nat} (hg : isGen g = true) : g < 32 := by
  unfold isGen at hg
  simp only [Bool.or_eq_true, Nat.beq_eq] at hg
  omega

@[expose] def rpa (y : Nat) : Nat :=
  (706166134003738168389707561982777111920062267392 >>> (5 * y)) &&& 31
@[expose] def rga (y : Nat) : Nat :=
  (753633496413952984341298276259032043098780796960 >>> (5 * y)) &&& 31
@[expose] def rda (y : Nat) : Nat := (89329638053220514541458890144194240784 >>> (4 * y)) &&& 15

@[expose] noncomputable def reachAt (y : Nat) : Bool :=
  Nat.beq y 0 || (Nat.blt (rpa y) 32 && Nat.blt (rda (rpa y)) (rda y) &&
    Nat.beq (pm (rpa y) (rga y)) y && isGen (rga y))

theorem reach_ok :
    Nat.rec (motive := fun _ => Bool) true (fun y ih => ih && reachAt y) 32 = true := by
  decide +kernel

theorem gen_ind {R : Nat → Prop} (h0 : R 0)
    (hs : ∀ z g, z < 32 → isGen g = true → R z → R (pm z g)) : ∀ y, y < 32 → R y := by
  have hr := recAnd (G := reachAt) 32 reach_ok
  have key : ∀ n y, y < 32 → rda y < n → R y := by
    intro n
    induction n with
    | zero => intro y _ h; omega
    | succ n ih =>
      intro y hy hd
      have hy' := hr y hy
      unfold reachAt at hy'
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hy'
      rcases hy' with rfl | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · exact h0
      · rw [← h3]
        exact hs _ _ h1 h4 (ih _ h1 (by omega))
  exact fun y hy => key _ y hy (Nat.lt_succ_self _)

theorem isAutN_comp {g f : Nat → Nat} (hg : IsAutN g) (hf : IsAutN f) :
    IsAutN (fun x => g (f x)) := by
  refine ⟨fun x hx => hg.1 _ (hf.1 x hx), fun x y hx hy => ?_, fun x y hx hy h => ?_⟩
  · change g (f (pm x y)) = pm (g (f x)) (g (f y))
    rw [hf.2.1 x y hx hy, hg.2.1 _ _ (hf.1 x hx) (hf.1 y hy)]
  · exact hf.2.2 x y hx hy (hg.2.2 _ _ (hf.1 x hx) (hf.1 y hy) h)

theorem eqL_sound : ∀ {l r : List Nat}, eqL l r = true → l = r
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: l, y :: r, h => by
    have h' : (Nat.beq x y && eqL l r) = true := h
    rw [Bool.and_eq_true, Nat.beq_eq] at h'
    rw [h'.1, eqL_sound h'.2]

theorem invsL_lt : ∀ x ∈ invsL, x < 32 := by decide

theorem tb32_and {x y i : Nat} : tb32 (x &&& y) i = (tb32 x i && tb32 y i) := by
  apply Bool.eq_iff_iff.mpr
  change tb (x &&& y) i = true ↔ (tb x i && tb y i) = true
  rw [Bool.and_eq_true, tb_iff, tb_iff, tb_iff, Nat.testBit_and, Bool.and_eq_true]

theorem enumD'_rest {a b c m y : Nat} {ds rest : List Nat} (h : y ∈ rest) :
    y ∈ enumD' a b c m ds rest := by
  induction ds with
  | nil => exact h
  | cons d ds ih =>
    change y ∈ cond (tb32 m d && sqD a b c d) (keyN a b c d :: enumD' a b c m ds rest)
      (enumD' a b c m ds rest)
    cases tb32 m d && sqD a b c d
    · exact ih
    · exact List.mem_cons_of_mem _ ih

theorem enumD'_key {a b c m d : Nat} {ds rest : List Nat} (hd : d ∈ ds)
    (h : (tb32 m d && sqD a b c d) = true) : keyN a b c d ∈ enumD' a b c m ds rest := by
  induction ds with
  | nil => cases hd
  | cons d' ds ih =>
    change _ ∈ cond (tb32 m d' && sqD a b c d') (keyN a b c d' :: enumD' a b c m ds rest)
      (enumD' a b c m ds rest)
    rcases List.mem_cons.mp hd with rfl | hd'
    · rw [h]
      exact List.mem_cons.mpr (Or.inl rfl)
    · cases tb32 m d' && sqD a b c d'
      · exact ih hd'
      · exact List.mem_cons_of_mem _ (ih hd')

theorem enumC'_rest {CMP a b ma mb y : Nat} {cs rest : List Nat} (h : y ∈ rest) :
    y ∈ enumC' CMP a b ma mb cs rest := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    change y ∈ cond (tb32 ma c) (enumD' a b c (mb &&& cmM CMP c) invsL
      (enumC' CMP a b ma mb cs rest)) (enumC' CMP a b ma mb cs rest)
    cases tb32 ma c
    · exact ih
    · exact enumD'_rest (a := a) (b := b) (c := c) (m := mb &&& cmM CMP c) (ds := invsL) ih

theorem enumC'_key {CMP a b ma mb c d : Nat} {cs rest : List Nat} (hc : c ∈ cs)
    (hmc : tb32 ma c = true) (hd : d ∈ invsL)
    (h : (tb32 (mb &&& cmM CMP c) d && sqD a b c d) = true) :
    keyN a b c d ∈ enumC' CMP a b ma mb cs rest := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    change _ ∈ cond (tb32 ma c') (enumD' a b c' (mb &&& cmM CMP c') invsL
      (enumC' CMP a b ma mb cs rest)) (enumC' CMP a b ma mb cs rest)
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [hmc]
      exact enumD'_key hd h
    · cases tb32 ma c'
      · exact ih hc'
      · exact enumD'_rest (a := a) (b := b) (c := c') (m := mb &&& cmM CMP c') (ds := invsL)
          (ih hc')

theorem enumB'_rest {CMP a ma y : Nat} {bs rest : List Nat} (h : y ∈ rest) :
    y ∈ enumB' CMP a ma bs rest := by
  induction bs with
  | nil => exact h
  | cons b bs ih =>
    change y ∈ cond (tb32 ma b) (enumC' CMP a b ma (cmM CMP b) invsL (enumB' CMP a ma bs rest))
      (enumB' CMP a ma bs rest)
    cases tb32 ma b
    · exact ih
    · exact enumC'_rest (CMP := CMP) (a := a) (b := b) (ma := ma) (mb := cmM CMP b)
        (cs := invsL) ih

theorem enumB'_key {CMP a ma b c d : Nat} {bs rest : List Nat} (hb : b ∈ bs)
    (hmb : tb32 ma b = true) (hc : c ∈ invsL) (hmc : tb32 ma c = true) (hd : d ∈ invsL)
    (h : (tb32 (cmM CMP b &&& cmM CMP c) d && sqD a b c d) = true) :
    keyN a b c d ∈ enumB' CMP a ma bs rest := by
  induction bs with
  | nil => cases hb
  | cons b' bs ih =>
    change _ ∈ cond (tb32 ma b') (enumC' CMP a b' ma (cmM CMP b') invsL
      (enumB' CMP a ma bs rest)) (enumB' CMP a ma bs rest)
    rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hmb]
      exact enumC'_key hc hmc hd h
    · cases tb32 ma b'
      · exact ih hb'
      · exact enumC'_rest (CMP := CMP) (a := a) (b := b') (ma := ma) (mb := cmM CMP b')
          (cs := invsL) (ih hb')

theorem enumA'_key {CMP a b c d : Nat} {as : List Nat} (ha : a ∈ as)
    (hab : tb32 (cmM CMP a) b = true) (hac : tb32 (cmM CMP a) c = true) (hb : b ∈ invsL)
    (hc : c ∈ invsL) (hd : d ∈ invsL)
    (h : (tb32 (cmM CMP b &&& cmM CMP c) d && sqD a b c d) = true) :
    keyN a b c d ∈ enumA' CMP as := by
  induction as with
  | nil => cases ha
  | cons a' as ih =>
    change _ ∈ enumB' CMP a' (cmM CMP a') invsL (enumA' CMP as)
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact enumB'_key hb hab hc hac hd h
    · exact enumB'_rest (ih ha')

@[expose] noncomputable def cmV : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun x ih => ih ||| (cmRow x 32 <<< (32 * x))) 32

@[expose] noncomputable def cmAt (x y : Nat) : Bool :=
  !Nat.beq (pm x y) (pm y x) || tb32 (cmM cmV x) y

@[expose] noncomputable def cmRowOK (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun y ih => ih && cmAt x y) 32

theorem cmV_ok :
    Nat.rec (motive := fun _ => Bool) true (fun x ih => ih && cmRowOK x) 32 = true := by
  decide +kernel

theorem cm_of {CMP : Nat} (hc : cmpB CMP = true) {x y : Nat} (hx : x < 32) (hy : y < 32)
    (h : pm x y = pm y x) : tb32 (cmM CMP x) y = true := by
  unfold cmpB at hc
  have hC : cmV = CMP := Nat.eq_of_beq_eq_true hc
  subst hC
  have h1 := recAnd (G := cmRowOK) 32 cmV_ok x hx
  have h2 := recAnd (G := cmAt x) 32 h1 y hy
  unfold cmAt at h2
  rw [h, Nat.beq_refl] at h2
  exact h2

theorem enum_mem {CMP : Nat} (hc : cmpB CMP = true) {a b c d : Nat} (ha : a ∈ invsL)
    (hb : b ∈ invsL) (hc' : c ∈ invsL) (hd : d ∈ invsL) (hab : pm a b = pm b a)
    (hac : pm a c = pm c a) (hbd : pm b d = pm d b) (hcd : pm c d = pm d c)
    (hs : pm (pm a d) (pm a d) = pm (pm c b) (pm c b)) (hs0 : pm (pm a d) (pm a d) ≠ 0) :
    keyN a b c d ∈ enumA' CMP invsL := by
  have hl := invsL_lt
  have hk : ∀ {x y : Nat}, x < 32 → y < 32 → pm x y = pm y x → tb32 (cmM CMP x) y = true :=
    fun hx hy h => cm_of hc hx hy h
  refine enumA'_key ha (hk (hl a ha) (hl b hb) hab) (hk (hl a ha) (hl c hc') hac) hb hc' hd ?_
  rw [tb32_and, hk (hl b hb) (hl d hd) hbd, hk (hl c hc') (hl d hd) hcd]
  change (true && true && (Nat.beq (pm (pm a d) (pm a d)) (pm (pm c b) (pm c b)) &&
    !Nat.beq (pm (pm a d) (pm a d)) 0)) = true
  have hne : Nat.beq (pm (pm a d) (pm a d)) 0 = false := by
    cases e : Nat.beq (pm (pm a d) (pm a d)) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hs0
  rw [hne, hs, Nat.beq_refl]
  rfl

theorem enum_sound {CMP : Nat} {K : List Nat} (hc : cmpB CMP = true)
    (he : eqL (enumA' CMP invsL) K = true) {a b c d : Nat} (ha : a ∈ invsL) (hb : b ∈ invsL)
    (hc' : c ∈ invsL) (hd : d ∈ invsL) (hab : pm a b = pm b a) (hac : pm a c = pm c a)
    (hbd : pm b d = pm d b) (hcd : pm c d = pm d c)
    (hs : pm (pm a d) (pm a d) = pm (pm c b) (pm c b)) (hs0 : pm (pm a d) (pm a d) ≠ 0) :
    keyN a b c d ∈ K := by
  rw [← eqL_sound he]
  exact enum_mem hc ha hb hc' hd hab hac hbd hcd hs hs0

theorem pack_lane : ∀ (K : List Nat), (∀ x ∈ K, x < 2 ^ 20) →
    ∀ i (hi : i < K.length), l20 (packL 20 K) i = K[i]
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: K, hK, i, hi => by
    have hx : x < 2 ^ 20 := hK x (List.mem_cons.mpr (Or.inl rfl))
    have hP : packL 20 (x :: K) = x + packL 20 K * 2 ^ 20 := by
      change x ||| (packL 20 K <<< 20) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]
    have e : (1048575 : Nat) = 2 ^ 20 - 1 := by decide
    cases i with
    | zero =>
      unfold l20
      rw [Nat.mul_zero, Nat.shiftRight_zero, hP, e, Nat.and_two_pow_sub_one_eq_mod,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rfl
    | succ i =>
      have hs : packL 20 (x :: K) >>> 20 = packL 20 K := by
        rw [hP, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by decide),
          Nat.div_eq_of_lt hx, Nat.zero_add]
      have ih := pack_lane K (fun y hy => hK y (List.mem_cons_of_mem _ hy)) i
        (Nat.lt_of_succ_lt_succ hi)
      unfold l20 at ih ⊢
      rw [List.getElem_cons_succ, ← ih, Nat.mul_add, Nat.mul_one, Nat.add_comm (20 * i) 20,
        Nat.shiftRight_add, hs]

theorem pack_sound {K : List Nat} {P : Nat} (h : packB 20 K P = true)
    (hK : ∀ x ∈ K, x < 2 ^ 20) : ∀ i (hi : i < K.length), l20 P i = K[i] := by
  have hP := Nat.eq_of_beq_eq_true h
  subst hP
  exact pack_lane K hK

theorem sortLB_sound {b : Nat} : ∀ (K : List Nat) (lo : Nat), sortLB b K lo = true →
    (∀ x ∈ K, lo ≤ x ∧ x < b) ∧ K.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => (by cases h), List.Pairwise.nil⟩
  | x :: K, lo, h => by
    have h' : (Nat.ble lo x && Nat.blt x b && sortLB b K (Nat.succ x)) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := sortLB_sound K (Nat.succ x) h3
    refine ⟨fun y hy => ?_, List.pairwise_cons.mpr ⟨fun y hy => ?_, ih2⟩⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨h1, h2⟩
      · have := ih1 y hy
        omega
    · have := ih1 y hy
      omega

theorem sort_sound {K : List Nat} {b : Nat} (h : sortB K b = true) :
    K.Pairwise (· < ·) ∧ ∀ x ∈ K, x < b := by
  have r := sortLB_sound K 0 h
  exact ⟨r.2, fun x hx => (r.1 x hx).2⟩

theorem lenL_eq : ∀ l : List Nat, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

theorem homN_spec (T : Nat) : ∀ n, ((homN T n).1 = true → ∀ x, x < n → homAt T x (lT T x) = true) ∧
    ∀ v, tb (homN T n).2 v = true ↔ ∃ x, x < n ∧ lT T x = v := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ x hx => absurd hx (Nat.not_lt_zero _), fun v => ?_⟩
    change tb 0 v = true ↔ _
    rw [tb_zero]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hx, _⟩ => absurd hx (Nat.not_lt_zero _)⟩
  | succ n ih =>
    have e : homN T (n + 1) =
        ((homN T n).1 && homAt T n (lT T n), (homN T n).2 ||| (1 <<< lT T n)) := rfl
    rw [e]
    refine ⟨fun h x hx => ?_, fun v => ?_⟩
    · rw [Bool.and_eq_true] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
      · exact ih.1 h.1 x hx
      · rw [hx]
        exact h.2
    · rw [tb_or, ih.2 v, tb_single]
      constructor
      · rintro (⟨x, hx, hv⟩ | hv)
        · exact ⟨x, by omega, hv⟩
        · exact ⟨n, by omega, hv.symm⟩
      · rintro ⟨x, hx, hv⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · exact Or.inl ⟨x, hx, hv⟩
        · subst hx
          exact Or.inr hv.symm

theorem homT_sound {T : Nat} (h : homT T = true) : IsAutN (lT T) := by
  unfold homT at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs := homN_spec T 32
  have hA := hs.1 h1
  have hgen : ∀ x g, x < 32 → isGen g = true → lT T (pm x g) = pm (lT T x) (lT T g) := by
    intro x g hx hg
    have hx' := hA x hx
    unfold homAt at hx'
    simp only [Bool.and_eq_true, Nat.beq_eq] at hx'
    unfold isGen at hg
    simp only [Bool.or_eq_true, Nat.beq_eq] at hg
    rcases hg with ((rfl | rfl) | rfl) | rfl
    · exact hx'.1.1.1
    · exact hx'.1.1.2
    · exact hx'.1.2
    · exact hx'.2
  have hmul : ∀ y, y < 32 → ∀ x, x < 32 → lT T (pm x y) = pm (lT T x) (lT T y) := by
    refine gen_ind (fun x hx => ?_) (fun z g hz hg ih x hx => ?_)
    · rw [pm_zero' hx, h3, pm_zero' (lT_lt T x)]
    · have hg' := isGen_lt hg
      rw [← pm_assoc hx hz hg', hgen _ _ (pm_lt' hx hz) hg, ih x hx,
        pm_assoc (lT_lt T x) (lT_lt T z) (lT_lt T g), ← hgen z g hz hg]
  refine ⟨fun x _ => lT_lt T x, fun x y hx hy => hmul y hy x hx, ?_⟩
  have hsurj : ∀ v, v < 32 → ∃ x, x < 32 ∧ lT T x = v := by
    intro v hv
    refine (hs.2 v).mp ?_
    rw [h2, tb_iff]
    have e : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
    rw [e, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hv
  let F : Fin 32 → Fin 32 := fun x => ⟨lT T x.val, lT_lt T x.val⟩
  have hF : Function.Surjective F := by
    intro v
    obtain ⟨x, hx, hv⟩ := hsurj v.val v.isLt
    exact ⟨⟨x, hx⟩, Fin.ext hv⟩
  have hFi := Finite.injective_iff_surjective.mpr hF
  intro x y hx hy e
  have := @hFi ⟨x, hx⟩ ⟨y, hy⟩ (Fin.ext e)
  exact congrArg Fin.val this

theorem stepOK_sound {S ke kp : Nat} (h : stepOK S ke kp = true) {f : Nat → Nat}
    (hf : HasKey f kp) : HasKey (fun x => lT S (f x)) ke := by
  unfold stepOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨f1, f2, f8, f16⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · change lT S (f 1) = _
    rw [f1]
    exact h1
  · change lT S (f 2) = _
    rw [f2]
    exact h2
  · change lT S (f 8) = _
    rw [f8]
    exact h3
  · change lT S (f 16) = _
    rw [f16]
    exact h4

theorem treeB_spec {S0 S1 A : Nat} (h0 : homT S0 = true) (h1 : homT S1 = true) :
    ∀ (l : List (Nat × Nat × Nat)) (s : Nat),
      (∀ e, tb s e = true → ∃ f : Nat → Nat, IsAutN f ∧ HasKey f (l20 A e)) →
      (treeB S0 S1 A l s).1 = true →
      ∀ e, tb (treeB S0 S1 A l s).2 e = true → ∃ f : Nat → Nat, IsAutN f ∧ HasKey f (l20 A e)
  | [], _, hs, _ => hs
  | r :: t, s, hs, h => by
    have hE : treeB S0 S1 A (r :: t) s = ((tb32 s r.2.2 && !tb32 s r.1 &&
        stepOK (cond (Nat.beq r.2.1 0) S0 S1) (l20 A r.1) (l20 A r.2.2)) &&
        (treeB S0 S1 A t (s ||| (1 <<< r.1))).1, (treeB S0 S1 A t (s ||| (1 <<< r.1))).2) := rfl
    rw [hE] at h ⊢
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, _⟩, hst⟩, ht⟩ := h
    refine treeB_spec h0 h1 t _ ?_ ht
    intro e he
    rcases tb_or.mp he with he | he
    · exact hs e he
    · rw [tb_single] at he
      subst he
      obtain ⟨f, hf, hk⟩ := hs _ hp
      have hS : homT (cond (Nat.beq r.2.1 0) S0 S1) = true := by
        cases Nat.beq r.2.1 0
        · exact h1
        · exact h0
      exact ⟨_, isAutN_comp (homT_sound hS) hf, stepOK_sound hst hk⟩

theorem tree_sound {S0 S1 A ide n : Nat} {l : List (Nat × Nat × Nat)} (h0 : homT S0 = true)
    (h1 : homT S1 = true) (hi : l20 A ide = IDK) (ht : treeOK S0 S1 A ide n l = true) :
    ∀ e, e < n → ∃ f : Nat → Nat, IsAutN f ∧ HasKey f (l20 A e) := by
  intro e he
  unfold treeOK at ht
  simp only [Bool.and_eq_true, Nat.beq_eq] at ht
  obtain ⟨ht1, ht2⟩ := ht
  refine treeB_spec h0 h1 l (1 <<< ide) ?_ ht1 e ?_
  · intro e' he'
    rw [tb_single] at he'
    subst he'
    refine ⟨fun x => x, ⟨fun x hx => hx, fun _ _ _ _ => rfl, fun _ _ _ _ h => h⟩, ?_⟩
    rw [hi]
    unfold HasKey IDK
    decide
  · rw [ht2, tb_iff, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact he

theorem gensOK_sound {T k : Nat} (h : gensOK T k = true) : HasKey (lT T) k := by
  unfold gensOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  unfold HasKey
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem el_sound {ELP KEYL lo n : Nat} (h : elB ELP KEYL lo n = true) :
    ∀ i, lo ≤ i → i < lo + n → IsAutN (lT (lE ELP i)) ∧ HasKey (lT (lE ELP i)) (l20 KEYL i) := by
  intro i hlo hi
  have hm := recAll (Q := fun i => homT (lE ELP (lo + i)) = true ∧
      gensOK (lE ELP (lo + i)) (l20 KEYL (lo + i)) = true)
    (fun _ _ hb => by
      simp only [Bool.and_eq_true] at hb
      exact ⟨hb.1.1, hb.1.2, hb.2⟩) n h (i - lo) (by omega)
  rw [Nat.add_sub_cancel' hlo] at hm
  exact ⟨homT_sound hm.1, gensOK_sound hm.2⟩

theorem inc_sound {KEYL n : Nat} (h : incB KEYL n = true) :
    ∀ i j, i < j → j ≤ n → l20 KEYL i < l20 KEYL j := by
  have hs := recAll (Q := fun i => l20 KEYL i < l20 KEYL (i + 1))
    (fun _ _ hb => by
      simp only [Bool.and_eq_true, Nat.blt_eq] at hb
      exact hb) n h
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h' | h'
    · exact Nat.lt_trans (ih h' (by omega)) (hs j (by omega))
    · subst h'
      exact hs i (by omega)

theorem rowM_all {MP KEYL g T : Nat} : ∀ n, rowM MP KEYL g T n = true →
    ∀ c, c < n → stepOK T (l20 KEYL (lM MP g c)) (l20 KEYL c) = true :=
  recAll (fun _ _ hb => by
    simp only [Bool.and_eq_true] at hb
    exact hb)

theorem invL_all {MP INVP ide : Nat} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun g ih => ih && Nat.beq (lM MP g (lI INVP g)) ide && Nat.blt (lI INVP g) 128) n = true →
    ∀ g, g < n → lM MP g (lI INVP g) = ide ∧ lI INVP g < 128 :=
  recAll (fun _ _ hb => by
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hb
    exact ⟨hb.1.1, hb.1.2, hb.2⟩)

theorem innB_all {T t : Nat} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun x ih => ih && Nat.beq (pm (lT T x) t) (pm t x)) n = true →
    ∀ x, x < n → pm (lT T x) t = pm t x :=
  recAll (fun _ _ hb => by
    simp only [Bool.and_eq_true, Nat.beq_eq] at hb
    exact hb)

theorem ciL_all {ELP CIL : Nat} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => ih && innB (lE ELP (lCI CIL t)) t) n = true →
    ∀ t, t < n → innB (lE ELP (lCI CIL t)) t = true :=
  recAll (fun _ _ hb => by
    simp only [Bool.and_eq_true] at hb
    exact hb)

theorem rows_sound {MP ELP KEYL lo n : Nat} (h : rowsM MP ELP KEYL lo n = true) :
    ∀ g c, lo ≤ g → g < lo + n → c < 128 → ∀ f : Nat → Nat, HasKey f (l20 KEYL c) →
      HasKey (fun x => lT (lE ELP g) (f x)) (l20 KEYL (lM MP g c)) := by
  intro g c hlo hg hc f hf
  have hr := recAll (Q := fun i => rowM MP KEYL (lo + i) (lE ELP (lo + i)) 128 = true)
    (fun _ _ hb => by
      simp only [Bool.and_eq_true] at hb
      exact hb) n h (g - lo) (by omega)
  rw [Nat.add_sub_cancel' hlo] at hr
  exact stepOK_sound (rowM_all 128 hr c hc) hf

theorem inv_sound {MP INVP ide KEYL : Nat} (h : invB MP INVP ide KEYL = true) :
    l20 KEYL ide = IDK ∧ ∀ g, g < 128 → lM MP g (lI INVP g) = ide ∧ lI INVP g < 128 := by
  unfold invB at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, invL_all 128 h.2⟩

theorem sq_fold {MP : Nat} : ∀ n j, (Nat.rec (motive := fun _ => Nat) 0
    (fun g ih => ih ||| (1 <<< (128 * lM MP g g + g))) n).testBit j = true ↔
      ∃ g, g < n ∧ 128 * lM MP g g + g = j
  | 0, j => by
    change (0 : Nat).testBit j = true ↔ _
    rw [Nat.zero_testBit]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hg, _⟩ => absurd hg (Nat.not_lt_zero _)⟩
  | n + 1, j => by
    have e : Nat.rec (motive := fun _ => Nat) 0
        (fun g ih => ih ||| (1 <<< (128 * lM MP g g + g))) (n + 1) =
        Nat.rec (motive := fun _ => Nat) 0 (fun g ih => ih ||| (1 <<< (128 * lM MP g g + g))) n |||
          (1 <<< (128 * lM MP n n + n)) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, sq_fold n j, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨g, hg, e⟩ | e)
      · exact ⟨g, by omega, e⟩
      · exact ⟨n, by omega, e⟩
    · rintro ⟨g, hg, hj⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | hg
      · exact Or.inl ⟨g, hg, hj⟩
      · subst hg
        exact Or.inr hj

theorem sq_sound {MP SQP : Nat} (h : sqB MP SQP = true) :
    ∀ s g, g < 128 → (tb (lS SQP s) g = true ↔ lM MP g g = s) := by
  intro s g hg
  unfold sqB at h
  have hS := Nat.eq_of_beq_eq_true h
  rw [tb_iff]
  unfold lS
  rw [Nat.testBit_and, Nat.testBit_shiftRight, FULL_eq, Nat.testBit_two_pow_sub_one,
    decide_eq_true hg, Bool.and_true, ← hS, sq_fold]
  constructor
  · rintro ⟨g', hg', e⟩
    have : g' = g := by omega
    subst this
    omega
  · intro e
    exact ⟨g, hg, by rw [e]⟩

theorem ci_sound {ELP CIL : Nat} (h : ciB ELP CIL = true) :
    ∀ t x, t < 32 → x < 32 → pm (lT (lE ELP (lCI CIL t)) x) t = pm t x := by
  intro t x ht hx
  unfold ciB at h
  have hi := ciL_all 32 h t ht
  unfold innB at hi
  exact innB_all 32 hi x hx

theorem bnd_sound {CATP n : Nat} (h : bndB CATP n = true) : ∀ k, n ≤ k → lC CATP k = 0 := by
  intro k hk
  unfold bndB at h
  rw [Nat.blt_eq] at h
  have hlt : CATP < 2 ^ (128 * k) :=
    Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 128 hk))
  unfold lC
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt, Nat.zero_and]

theorem recsB_at {MP INVP SQP CATP : Nat} :
    ∀ (rs : List (Nat × List Nat × List (Nat × Nat) × List (Nat × Nat))) (k0 : Nat),
      recsB MP INVP SQP CATP k0 rs = true → ∀ k, k0 ≤ k → k < k0 + rs.length →
      ∃ r : Nat × List Nat × List (Nat × Nat) × List (Nat × Nat),
        r.1 = lC CATP k ∧ recB MP INVP SQP CATP r = true
  | [], k0, _, k, h1, h2 => by
    simp only [List.length_nil, Nat.add_zero] at h2
    omega
  | r :: rs, k0, h, k, h1, h2 => by
    have h' : (Nat.beq r.1 (lC CATP k0) && recB MP INVP SQP CATP r &&
        recsB MP INVP SQP CATP (k0 + 1) rs) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e
      exact ⟨r, h'.1.1, h'.1.2⟩
    · simp only [List.length_cons] at h2
      exact recsB_at rs (k0 + 1) h'.2 k hlt (by omega)

theorem memS_fst {SQP : Nat} : ∀ (Cm : List Nat) (x : Nat), tb (memS SQP Cm).1 x = true ↔ x ∈ Cm
  | [], x => by
    change tb 0 x = true ↔ _
    rw [tb_zero]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun h => by cases h⟩
  | m :: Cm, x => by
    change tb ((memS SQP Cm).1 ||| (1 <<< m)) x = true ↔ _
    rw [tb_or, tb_single, memS_fst Cm x, List.mem_cons]
    exact Or.comm

theorem memS_snd {SQP : Nat} : ∀ (Cm : List Nat) (m x : Nat), m ∈ Cm →
    tb (lS SQP m) x = true → tb (memS SQP Cm).2 x = true
  | [], _, _, hm, _ => by cases hm
  | m' :: Cm, m, x, hm, hx => by
    change tb ((memS SQP Cm).2 ||| lS SQP m') x = true
    rw [tb_or]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Or.inr hx
    · exact Or.inl (memS_snd Cm m x hm hx)

theorem uni_iff {MP C g : Nat} : ∀ (Cm : List Nat) (x : Nat),
    tb (uni MP C g Cm) x = true ↔ tb C x = true ∨ ∃ m, m ∈ Cm ∧ lM MP g m = x
  | [], x => by
    change tb C x = true ↔ _
    constructor
    · exact Or.inl
    · rintro (h | ⟨_, hm, _⟩)
      · exact h
      · cases hm
  | m :: Cm, x => by
    change tb (uni MP C g Cm ||| (1 <<< lM MP g m)) x = true ↔ _
    rw [tb_or, uni_iff Cm x, tb_single]
    constructor
    · rintro ((h | ⟨m', hm', e⟩) | e)
      · exact Or.inl h
      · exact Or.inr ⟨m', List.mem_cons_of_mem _ hm', e⟩
      · exact Or.inr ⟨m, List.mem_cons.mpr (Or.inl rfl), e.symm⟩
    · rintro (h | ⟨m', hm', e⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hm' with rfl | hm'
        · exact Or.inr e.symm
        · exact Or.inl (Or.inr ⟨m', hm', e⟩)

theorem kids_sound {MP CATP C : Nat} {Cm : List Nat} : ∀ (ks : List (Nat × Nat)),
    (kids MP CATP C Cm ks).1 = true → ∀ x, tb (kids MP CATP C Cm ks).2 x = true →
      ∃ p, p ∈ ks ∧ p.1 < 128 ∧ uni MP C p.1 Cm = lC CATP p.2 ∧ tb (lC CATP p.2) x = true
  | [], _, x, hx => by
    change tb 0 x = true at hx
    rw [tb_zero] at hx
    exact absurd hx Bool.false_ne_true
  | p :: ks, h, x, hx => by
    have h' : ((kids MP CATP C Cm ks).1 && Nat.blt p.1 128 &&
        Nat.beq (uni MP C p.1 Cm) (lC CATP p.2)) = true := h
    change tb ((kids MP CATP C Cm ks).2 ||| lC CATP p.2) x = true at hx
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    rcases tb_or.mp hx with hx | hx
    · obtain ⟨q, hq, hq1⟩ := kids_sound ks h'.1.1 x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
    · exact ⟨p, List.mem_cons.mpr (Or.inl rfl), h'.1.2, h'.2, hx⟩

theorem fails_sound {MP INVP C : Nat} : ∀ (fs : List (Nat × Nat)),
    (fails MP INVP C fs).1 = true → ∀ x, tb (fails MP INVP C fs).2 x = true →
      ∃ c, failOK MP INVP C x c = true
  | [], _, x, hx => by
    change tb 0 x = true at hx
    rw [tb_zero] at hx
    exact absurd hx Bool.false_ne_true
  | p :: fs, h, x, hx => by
    have h' : ((fails MP INVP C fs).1 && failOK MP INVP C p.1 p.2) = true := h
    change tb ((fails MP INVP C fs).2 ||| (1 <<< p.1)) x = true at hx
    rw [Bool.and_eq_true] at h'
    rcases tb_or.mp hx with hx | hx
    · exact fails_sound fs h'.1 x hx
    · rw [tb_single] at hx
      subst hx
      exact ⟨p.2, h'.2⟩

theorem recs_sound {MP INVP SQP CATP k0 : Nat}
    {rs : List (Nat × List Nat × List (Nat × Nat) × List (Nat × Nat))} (hsq : sqB MP SQP = true)
    (h : recsB MP INVP SQP CATP k0 rs = true) :
    ∀ k, k0 ≤ k → k < k0 + rs.length → ∀ g, g < 128 → tb (lC CATP k) g = false →
      tb (lC CATP k) (lM MP g g) = true →
      (∀ c, c < 128 → tb (lC CATP k) c = true →
        tb (lC CATP k) (lM MP (lM MP g c) (lI INVP g)) = true) →
      ∃ g₀ k', g₀ < 128 ∧ tb (lC CATP k') g = true ∧
        ∀ x, tb (lC CATP k') x = true ↔
          (tb (lC CATP k) x = true ∨ ∃ c, c < 128 ∧ tb (lC CATP k) c = true ∧ lM MP g₀ c = x) := by
  intro k hk0 hk g hg hgC hgg hnorm
  obtain ⟨⟨C, Cm, ks, fs⟩, hC, hr⟩ := recsB_at rs k0 h k hk0 hk
  change C = lC CATP k at hC
  subst hC
  have hr' : recB3 (lC CATP k) (memS SQP Cm) (kids MP CATP (lC CATP k) Cm ks)
      (fails MP INVP (lC CATP k) fs) = true := hr
  unfold recB3 at hr'
  simp only [Bool.and_eq_true, Nat.beq_eq] at hr'
  obtain ⟨⟨⟨hm1, hk1⟩, hf1⟩, hfin⟩ := hr'
  have hmem : ∀ x, tb (lC CATP k) x = true ↔ x ∈ Cm := by
    intro x
    rw [← hm1]
    exact memS_fst Cm x
  have hgs : tb (memS SQP Cm).2 g = true :=
    memS_snd Cm _ g ((hmem _).mp hgg) ((sq_sound hsq (lM MP g g) g hg).mpr rfl)
  rw [FULL_eq] at hfin
  have hall := mask_sub hfin hg hgs
  rcases tb_or.mp hall with hall | hall
  · rcases tb_or.mp hall with hall | hall
    · rw [hgC] at hall
      exact absurd hall Bool.false_ne_true
    · obtain ⟨p, _, hp128, hpu, hpx⟩ := kids_sound ks hk1 g hall
      refine ⟨p.1, p.2, hp128, hpx, fun x => ?_⟩
      rw [← hpu, uni_iff]
      constructor
      · rintro (hx | ⟨m, hm, e⟩)
        · exact Or.inl hx
        · have hm' := (hmem m).mpr hm
          exact Or.inr ⟨m, tb_lC_lt hm', hm', e⟩
      · rintro (hx | ⟨c, _, hc, e⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨c, (hmem c).mp hc, e⟩
  · obtain ⟨c, hc⟩ := fails_sound fs hf1 g hall
    unfold failOK at hc
    rw [Bool.and_eq_true] at hc
    have h2 := hnorm c (tb_lC_lt hc.1) hc.1
    rw [h2] at hc
    exact absurd hc.2 (by decide)

theorem witsB_at {MP ELP CIL CATP : Nat} :
    ∀ (ws : List (List Nat × List Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat)))
      (k0 : Nat), witsB MP ELP CIL CATP k0 ws = true → ∀ k, k0 ≤ k → k < k0 + ws.length →
      ∃ w : List Nat × List Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat),
        witB MP ELP CIL (lC CATP k) w = true
  | [], k0, _, k, h1, h2 => by
    simp only [List.length_nil, Nat.add_zero] at h2
    omega
  | w :: ws, k0, h, k, h1, h2 => by
    have h' : (witB MP ELP CIL (lC CATP k0) w && witsB MP ELP CIL CATP (k0 + 1) ws) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e
      exact ⟨w, h'.1⟩
    · simp only [List.length_cons] at h2
      exact witsB_at ws (k0 + 1) h'.2 k hlt (by omega)

theorem inL_sound {x : Nat} : ∀ {l : List Nat}, inL x l = true → x ∈ l
  | [], h => absurd h Bool.false_ne_true
  | y :: l, h => by
    have h' : (Nat.beq x y || inL x l) = true := h
    rw [Bool.or_eq_true, Nat.beq_eq] at h'
    rcases h' with e | h'
    · rw [e]
      exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons_of_mem _ (inL_sound h')

theorem asOK_sound {C : Nat} : ∀ (as : List Nat), asOK C as = true → ∀ a ∈ as, tb C a = true
  | [], _, _, ha => by cases ha
  | a :: as, h, b, hb => by
    have h' : (tb C a && asOK C as) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h'.1
    · exact asOK_sound as h'.2 b hb

theorem tsOK_sound {CIL C : Nat} : ∀ (ts : List Nat), tsOK CIL C ts = true →
    ∀ t ∈ ts, t < 32 ∧ tb C (lCI CIL t) = true
  | [], _, _, ht => by cases ht
  | t :: ts, h, u, hu => by
    have h' : (Nat.blt t 32 && tb C (lCI CIL t) && tsOK CIL C ts) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h'.1
    · exact tsOK_sound ts h'.2 u hu

theorem mdB_inv {MP CIL C : Nat} {as : List Nat} {P : Nat → Prop}
    (hb : ∀ i, i < 32 → tb C (lCI CIL i) = true → P (lCI CIL i))
    (hs : ∀ a ∈ as, ∀ x, x < 128 → P x → P (lM MP a x)) :
    ∀ (md : List (Nat × Nat × Nat)) (s : Nat), (mdB MP CIL C as md s).1 = true →
      (∀ v, tb s v = true → v < 128 ∧ P v) →
      ∀ v, tb (mdB MP CIL C as md s).2 v = true → v < 128 ∧ P v
  | [], _, _, hS => hS
  | (t, a, x) :: md, s, h, hS => by
    have h' : (cond (Nat.beq t 0) (Nat.blt a 32 &&
        tb C (cond (Nat.beq t 0) (lCI CIL a) (lM MP a x))) (inL a as && tb s x) &&
        (mdB MP CIL C as md (s ||| (1 <<< cond (Nat.beq t 0) (lCI CIL a) (lM MP a x)))).1) =
          true := h
    have hE : (mdB MP CIL C as ((t, a, x) :: md) s).2 =
        (mdB MP CIL C as md (s ||| (1 <<< cond (Nat.beq t 0) (lCI CIL a) (lM MP a x)))).2 := rfl
    rw [hE]
    rw [Bool.and_eq_true] at h'
    refine mdB_inv hb hs md _ h'.2 ?_
    intro v hv
    rcases tb_or.mp hv with hv | hv
    · exact hS v hv
    · rw [tb_single] at hv
      subst hv
      have h1 := h'.1
      cases e : Nat.beq t 0
      · rw [e] at h1
        change (inL a as && tb s x) = true at h1
        rw [Bool.and_eq_true] at h1
        have hx := hS x h1.2
        exact ⟨lM_lt MP a x, hs a (inL_sound h1.1) x hx.1 hx.2⟩
      · rw [e] at h1
        change (Nat.blt a 32 && tb C (lCI CIL a)) = true at h1
        simp only [Bool.and_eq_true, Nat.blt_eq] at h1
        exact ⟨lCI_lt CIL a, hb a h1.1 h1.2⟩

theorem ldB_inv {ELP C : Nat} {ts : List Nat} {Q : Nat → Prop}
    (hb : ∀ α, tb C α = true → ∀ t ∈ ts, Q (lT (lE ELP α) t))
    (hs : ∀ x y, Q x → Q y → Q (pm x y)) :
    ∀ (ld : List (Nat × Nat × Nat)) (s : Nat), (ldB ELP C ts ld s).1 = true →
      (∀ v, tb s v = true → v < 32 ∧ Q v) →
      ∀ v, tb (ldB ELP C ts ld s).2 v = true → v < 32 ∧ Q v
  | [], _, _, hS => hS
  | (t, x, y) :: ld, s, h, hS => by
    have h' : (cond (Nat.beq t 0) (tb C x && inL y ts) (tb s x && tb s y) &&
        (ldB ELP C ts ld (s ||| (1 <<< cond (Nat.beq t 0) (lT (lE ELP x) y) (pm x y)))).1) =
          true := h
    have hE : (ldB ELP C ts ((t, x, y) :: ld) s).2 =
        (ldB ELP C ts ld (s ||| (1 <<< cond (Nat.beq t 0) (lT (lE ELP x) y) (pm x y)))).2 := rfl
    rw [hE]
    rw [Bool.and_eq_true] at h'
    refine ldB_inv hb hs ld _ h'.2 ?_
    intro v hv
    rcases tb_or.mp hv with hv | hv
    · exact hS v hv
    · rw [tb_single] at hv
      subst hv
      have h1 := h'.1
      cases e : Nat.beq t 0
      · rw [e] at h1
        change (tb s x && tb s y) = true at h1
        rw [Bool.and_eq_true] at h1
        have hx := hS x h1.1
        have hy := hS y h1.2
        exact ⟨pm_lt' hx.1 hy.1, hs x y hx.2 hy.2⟩
      · rw [e] at h1
        change (tb C x && inL y ts) = true at h1
        rw [Bool.and_eq_true] at h1
        exact ⟨lT_lt _ _, hb x h1.1 y (inL_sound h1.2)⟩

theorem lMask_mem {CIL C : Nat} : ∀ n i, i < n → tb C (lCI CIL i) = true →
    tb (Nat.rec (motive := fun _ => Nat) 0
      (fun i ih => cond (tb C (lCI CIL i)) (ih ||| (1 <<< i)) ih) n) i = true
  | 0, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi, hc => by
    have e : Nat.rec (motive := fun _ => Nat) 0
        (fun i ih => cond (tb C (lCI CIL i)) (ih ||| (1 <<< i)) ih) (n + 1) =
        cond (tb C (lCI CIL n))
          (Nat.rec (motive := fun _ => Nat) 0
            (fun i ih => cond (tb C (lCI CIL i)) (ih ||| (1 <<< i)) ih) n ||| (1 <<< n))
          (Nat.rec (motive := fun _ => Nat) 0
            (fun i ih => cond (tb C (lCI CIL i)) (ih ||| (1 <<< i)) ih) n) := rfl
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · have ih := lMask_mem n i hi hc
      cases tb C (lCI CIL n)
      · exact ih
      · exact tb_or.mpr (Or.inl ih)
    · subst hi
      rw [hc]
      exact tb_or.mpr (Or.inr (tb_single.mpr rfl))

theorem wits_sound {MP ELP CIL CATP k0 : Nat}
    {ws : List (List Nat × List Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat))}
    (h : witsB MP ELP CIL CATP k0 ws = true) :
    ∀ k, k0 ≤ k → k < k0 + ws.length → ∃ as ts : List Nat, as.length + ts.length ≤ 4 ∧
      (∀ a ∈ as, tb (lC CATP k) a = true) ∧
      (∀ t ∈ ts, t < 32 ∧ tb (lC CATP k) (lCI CIL t) = true) ∧
      (∀ P : Nat → Prop, (∀ i, i < 32 → tb (lC CATP k) (lCI CIL i) = true → P (lCI CIL i)) →
        (∀ a ∈ as, ∀ x, x < 128 → P x → P (lM MP a x)) →
        ∀ α, tb (lC CATP k) α = true → P α) ∧
      (∀ Q : Nat → Prop, (∀ α, tb (lC CATP k) α = true → ∀ t ∈ ts, Q (lT (lE ELP α) t)) →
        (∀ x y, Q x → Q y → Q (pm x y)) → ∀ i, i < 32 → tb (lC CATP k) (lCI CIL i) = true → Q i) := by
  intro k hk0 hk
  obtain ⟨⟨as, ts, md, ld⟩, hw⟩ := witsB_at ws k0 h k hk0 hk
  have hw' : (asOK (lC CATP k) as && tsOK CIL (lC CATP k) ts && Nat.ble (lenL as + lenL ts) 4 &&
      (mdB MP CIL (lC CATP k) as md 0).1 &&
      Nat.beq (lC CATP k &&& (FULL ^^^ (mdB MP CIL (lC CATP k) as md 0).2)) 0 &&
      (ldB ELP (lC CATP k) ts ld 0).1 &&
      Nat.beq (lMask CIL (lC CATP k) &&& (4294967295 ^^^ (ldB ELP (lC CATP k) ts ld 0).2)) 0) =
        true := hw
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hw'
  obtain ⟨⟨⟨⟨⟨⟨has, hts⟩, hlen⟩, hm1⟩, hm2⟩, hq1⟩, hq2⟩ := hw'
  rw [FULL_eq] at hm2
  have e32 : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
  rw [e32] at hq2
  refine ⟨as, ts, ?_, asOK_sound as has, tsOK_sound ts hts, ?_, ?_⟩
  · rw [lenL_eq, lenL_eq] at hlen
    exact hlen
  · intro P hb hs α hα
    have hm := mdB_inv (P := P) hb hs md 0 hm1 (fun v hv => by
      rw [tb_zero] at hv
      exact absurd hv Bool.false_ne_true) α (mask_sub hm2 (tb_lC_lt hα) hα)
    exact hm.2
  · intro Q hb hs i hi hCi
    have hq := ldB_inv (Q := Q) hb hs ld 0 hq1 (fun v hv => by
      rw [tb_zero] at hv
      exact absurd hv Bool.false_ne_true) i (mask_sub hq2 hi (lMask_mem 32 i hi hCi))
    exact hq.2

end CFSG.KD.S5Ext
