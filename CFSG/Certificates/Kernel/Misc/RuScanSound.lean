module

public import Certificates.Data.Kernel.Misc.RuScanB
public import Certificates.Data.Kernel.Misc.RuScanD
public import Certificates.Data.Kernel.Misc.RuScanL
public import CFSG.Certificates.Kernel.Misc.RuInvPack
public import CFSG.Certificates.Kernel.Misc.RuBaseSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Quasithin.Vol2.KGFactC31BadScan
public import CFSG.Monster.B.Mathieu.Order

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuInv.P
  CFSG.KC.Misc.RuBase CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Quasithin.KGC31

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

@[expose] def PL (ys : List Nat) (gs : List G) : Prop := List.Forall₂ (PRep 4060 12) ys gs

theorem apP_eq {p : Nat} {g : G} (hp : PRep 4060 12 p g) (x : Fin 4060) : apP p x = (g x : Nat) :=
  hp x

theorem yAp_eq {ys : List Nat} {gs : List G} (h : PL ys gs) (x : Fin 4060) :
    yAp ys x = (gs.prod x : Nat) := by
  induction h with
  | nil => rfl
  | @cons p g ps gs' hp _ ih =>
    change strictN (yAp ps x) (fun v => apP p v) = _
    rw [P.strictN_eq, ih, apP_eq hp, List.prod_cons, Equiv.Perm.mul_apply]

theorem yPow_eq {ys : List Nat} {gs : List G} (h : PL ys gs) (j : Nat) (x : Fin 4060) :
    yPow ys j x = ((gs.prod ^ j) x : Nat) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change strictN (yPow ys j x) (fun v => yAp ys v) = _
    rw [P.strictN_eq, ih, yAp_eq h, pow_succ', Equiv.Perm.mul_apply]

theorem pow_gcd_fix {α : Type*} {σ : Equiv.Perm α} {x : α} {k e : Nat} (hk : (σ ^ k) x = x)
    (he : σ ^ e = 1) : (σ ^ Nat.gcd k e) x = x := by
  have h1 : σ ^ Nat.gcd k e = (σ ^ k) ^ (Nat.gcdA k e) * (σ ^ e) ^ (Nat.gcdB k e) := by
    rw [← zpow_natCast σ (Nat.gcd k e), Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul,
      zpow_natCast, zpow_natCast]
  rw [h1, he, one_zpow, mul_one]
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hk _

theorem listRec_false {l : List Nat} {f : Nat → Bool}
    (h : List.rec (motive := fun _ => Bool) true (fun e _ ih => bIf(f e, false, ih)) l = true) :
    ∀ e ∈ l, f e = false := by
  induction l with
  | nil => intro e he; exact absurd he List.not_mem_nil
  | cons a l ih =>
    have h' : (if f a = true then false else
        List.rec (motive := fun _ => Bool) true (fun e _ ih => bIf(f e, false, ih)) l) = true := by
      rw [← RuBase.bIf_eq]
      exact h
    by_cases ha : f a = true
    · rw [if_pos ha] at h'
      exact absurd h' Bool.false_ne_true
    · rw [if_neg ha] at h'
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Bool.eq_false_iff.mpr ha
      · exact ih h' e he

theorem wit0_sound {ys : List Nat} {gs : List G} (h : PL ys gs) {b k : Nat} (hb : b < 4060)
    (hw : wit0 ys b k = true) : ∀ e ∈ [125, 7, 13, 29], gs.prod ^ e ≠ 1 := by
  unfold wit0 at hw
  rw [bAnd_eq', Bool.and_eq_true] at hw
  obtain ⟨hk, hl⟩ := hw
  have hl' := @listRec_false [125, 7, 13, 29] (fun e => Nat.beq (yPow ys (Nat.gcd k e) b) b) hl
  intro e he hy
  have hkb : (gs.prod ^ k) ⟨b, hb⟩ = ⟨b, hb⟩ := by
    apply Fin.ext
    rw [← yPow_eq h]
    exact Nat.eq_of_beq_eq_true hk
  have hg := congrArg Fin.val (pow_gcd_fix hkb hy)
  have hf : Nat.beq (yPow ys (Nat.gcd k e) b) b = false := hl' e he
  have hg' : yPow ys (Nat.gcd k e) b = b := (yPow_eq h (Nat.gcd k e) ⟨b, hb⟩).trans hg
  have ht : Nat.beq (yPow ys (Nat.gcd k e) b) b = true := Nat.beq_eq.mpr hg'
  exact Bool.false_ne_true (hf.symm.trans ht)

theorem wit1_sound {ys : List Nat} {gs : List G} (h : PL ys gs) {T : Nat} {τ : G}
    (hT : PRep 4060 12 T τ) {j x x' : Nat} (hx : x < 4060) (hx' : x' < 4060)
    (hw : wit1 ys T j x x' = true) :
    τ * (gs.prod ^ j * τ * (gs.prod ^ j)⁻¹) ≠ gs.prod ^ j * τ * (gs.prod ^ j)⁻¹ * τ := by
  unfold wit1 at hw
  rw [strictB_eq, bAnd_eq', Bool.and_eq_true] at hw
  obtain ⟨h1, h2⟩ := hw
  have a1 : yPow ys j x = (((gs.prod ^ j) ⟨x, hx⟩ : Fin 4060) : Nat) := yPow_eq h j ⟨x, hx⟩
  have a2 : yPow ys j x' = (((gs.prod ^ j) ⟨x', hx'⟩ : Fin 4060) : Nat) := yPow_eq h j ⟨x', hx'⟩
  have a3 := apP_eq hT ((gs.prod ^ j) ⟨x, hx⟩)
  have a4 : apP T x = ((τ ⟨x, hx⟩ : Fin 4060) : Nat) := apP_eq hT ⟨x, hx⟩
  have a5 : apP T x' = ((τ ⟨x', hx'⟩ : Fin 4060) : Nat) := apP_eq hT ⟨x', hx'⟩
  have a6 := yPow_eq h j (τ ⟨x, hx⟩)
  have a7 := yPow_eq h j (τ ⟨x', hx'⟩)
  have a8 := apP_eq hT ((gs.prod ^ j) (τ ⟨x, hx⟩))
  rw [a1, a3, a2] at h1
  rw [a4, a6, a8, a5, a7] at h2
  have e1 : (gs.prod ^ j) ⟨x', hx'⟩ = τ ((gs.prod ^ j) ⟨x, hx⟩) :=
    Fin.ext (Nat.eq_of_beq_eq_true h1)
  intro hc
  have e3 : (⟨x', hx'⟩ : Fin 4060) = (gs.prod ^ j)⁻¹ (τ ((gs.prod ^ j) ⟨x, hx⟩)) := by
    rw [← e1]
    simp
  have hcx := congrArg (fun g : G => g ((gs.prod ^ j) ⟨x, hx⟩)) hc
  simp only [Equiv.Perm.mul_apply] at hcx
  have he : τ ((gs.prod ^ j) (τ ⟨x, hx⟩)) = (gs.prod ^ j) (τ ⟨x', hx'⟩) := by
    rw [e3]
    simpa using hcx
  have : Nat.beq (((τ ((gs.prod ^ j) (τ ⟨x, hx⟩))) : Fin 4060) : Nat)
      (((gs.prod ^ j) (τ ⟨x', hx'⟩) : Fin 4060) : Nat) = true :=
    Nat.beq_eq.mpr (congrArg Fin.val he)
  simp [this] at h2

theorem witK_sound {ys : List Nat} {gs : List G} (h : PL ys gs) {T : Nat} {τ : G}
    (hT : PRep 4060 12 T τ) {r : Nat} (hb : witB r = true) (hw : witK ys T r = true) :
    (∀ e ∈ [125, 7, 13, 29], gs.prod ^ e ≠ 1) ∨
      ∃ j : Nat, τ * (gs.prod ^ j * τ * (gs.prod ^ j)⁻¹) ≠
        gs.prod ^ j * τ * (gs.prod ^ j)⁻¹ * τ := by
  unfold witK at hw
  unfold witB at hb
  rw [strictB_eq] at hw hb
  simp only [RuBase.bIf_eq] at hw hb
  split_ifs at hw hb with h0 h1 h2
  · exact Or.inl (wit0_sound h (Nat.blt_eq.mp hb) hw)
  · exact Or.inr ⟨_, wit1_sound h hT (Nat.blt_eq.mp h2) (Nat.blt_eq.mp hb) hw⟩

theorem chk2_spec {LR TR W : Nat → Nat} {H T lo cnt : Nat} (h : chk2 LR TR W H T lo cnt = true) :
    ∀ d < cnt, witK [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + (lo + d) % rcnt (LR 1))] T (W (lo + d)) = true := by
  unfold chk2 at h
  simp only [strictB_eq] at h
  intro d hd
  exact RuBase.allN_iff.1 h d hd

theorem chk3_spec {LR TR W : Nat → Nat} {H T lo cnt : Nat} (h : chk3 LR TR W H T lo cnt = true) :
    ∀ d < cnt, witK [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 2) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + (lo + d) / rcnt (LR 2) % rcnt (LR 1)),
      TR (roff 4060 48720 (LR 2) + (lo + d) % rcnt (LR 2))] T (W (lo + d)) = true := by
  unfold chk3 at h
  simp only [strictB_eq] at h
  intro d hd
  exact RuBase.allN_iff.1 h d hd

theorem chunk_of {K cnt i : Nat} (hi : i < K * cnt) :
    i / cnt < K ∧ i % cnt < cnt ∧ cnt * (i / cnt) + i % cnt = i := by
  have hc : 0 < cnt := by
    rcases Nat.eq_zero_or_pos cnt with h | h
    · rw [h, Nat.mul_zero] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · exact h
  exact ⟨(Nat.div_lt_iff_lt_mul hc).2 hi, Nat.mod_lt _ hc, Nat.div_add_mod i cnt⟩

theorem bnd_all {W : Nat → Nat} {K cnt : Nat} (h : ∀ q < K, bndK W (cnt * q) cnt = true) :
    ∀ i < K * cnt, witB (W i) = true := by
  intro i hi
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have hq' := h _ hq
  unfold bndK at hq'
  have := RuBase.allN_iff.1 hq' _ hd
  rwa [Nat.add_eq, e] at this

theorem chk2_all {LR TR W : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chk2 LR TR W H T (cnt * q) cnt = true) :
    ∀ i < K * cnt, witK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))] T (W i) = true := by
  intro i hi
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have := chk2_spec (h _ hq) _ hd
  rwa [e] at this

theorem chk3_all {LR TR W : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chk3 LR TR W H T (cnt * q) cnt = true) :
    ∀ i < K * cnt, witK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 2) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i / rcnt (LR 2) % rcnt (LR 1)),
      TR (roff 4060 48720 (LR 2) + i % rcnt (LR 2))] T (W i) = true := by
  intro i hi
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have := chk3_spec (h _ hq) _ hd
  rwa [e] at this

theorem witKD_eq {ys : List Nat} {T r : Nat} (hr : Nat.land r 3 ≠ 2) : witKD ys T r = witK ys T r := by
  unfold witKD
  rw [RuBase.bIf_eq, if_neg (fun h => hr (Nat.eq_of_beq_eq_true h))]

theorem chk2D_all {LR TR W : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chk2D LR TR W H T (cnt * q) cnt = true) :
    ∀ i < K * cnt, Nat.land (W i) 3 ≠ 2 → witK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))] T (W i) = true := by
  intro i hi hr
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have hq' := h _ hq
  unfold chk2D at hq'
  simp only [strictB_eq] at hq'
  have := RuBase.allN_iff.1 hq' _ hd
  have e' : Nat.add (cnt * (i / cnt)) (i % cnt) = i := e
  rw [e', witKD_eq hr] at this
  exact this

theorem chk3D_all {LR TR W : Nat → Nat} {H T K cnt : Nat}
    (h : ∀ q < K, chk3D LR TR W H T (cnt * q) cnt = true) :
    ∀ i < K * cnt, Nat.land (W i) 3 ≠ 2 →
      witK [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 2) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i / rcnt (LR 2) % rcnt (LR 1)),
      TR (roff 4060 48720 (LR 2) + i % rcnt (LR 2))] T (W i) = true := by
  intro i hi hr
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have hq' := h _ hq
  unfold chk3D at hq'
  simp only [strictB_eq] at hq'
  have := RuBase.allN_iff.1 hq' _ hd
  have e' : Nat.add (cnt * (i / cnt)) (i % cnt) = i := e
  rw [e', witKD_eq hr] at this
  exact this

theorem kbnd_all {Kh : Nat → Nat} {K cnt : Nat} (h : ∀ q < K, kbndK Kh (cnt * q) cnt = true) :
    ∀ i < K * cnt, Kh i < 4060 := by
  intro i hi
  obtain ⟨hq, hd, e⟩ := chunk_of hi
  have hq' := h _ hq
  unfold kbndK at hq'
  have := Nat.blt_eq.mp (RuBase.allN_iff.1 hq' _ hd)
  rwa [Nat.add_eq, e] at this

theorem leafStep_le (ys : List Nat) (T : Nat) (K V : Nat → Nat) (r s : Nat) :
    leafStep ys T K V r s ≤ s := by
  unfold leafStep
  simp only [Orb.nIf_eq]
  split_ifs <;> first | exact Nat.zero_le _ | exact Nat.sub_le _ _ | exact le_refl _

theorem leafStep_spec {ys : List Nat} {T : Nat} {K V : Nat → Nat} {r s : Nat}
    (hr : Nat.land r 3 = 2) (h : leafStep ys T K V r s ≠ 0) :
    2 ≤ s ∧ leafOK ys T K V (r >>> 2) (s - 2) = true := by
  have hr' : Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2) = true := Nat.beq_eq.mpr hr
  unfold leafStep at h
  rw [hr'] at h
  simp only [Orb.nIf_eq] at h
  split_ifs at h <;>
    first
    | exact absurd rfl h
    | exact ⟨Nat.le_of_ble_eq_true (by assumption), by assumption⟩
    | exact absurd rfl (by assumption)
    | simp_all

theorem foldr_le' {f : Nat → Nat → Nat} (hle : ∀ d s, f d s ≤ s) (s : Nat) :
    ∀ l : List Nat, l.foldr f s ≤ s
  | [] => le_refl _
  | a :: l => (hle a _).trans (foldr_le' hle s l)

theorem foldr_ne_zero' {f : Nat → Nat → Nat} {s : Nat} :
    ∀ l : List Nat, l.foldr f s ≠ 0 → (∀ d, f d 0 = 0) → (∀ d s, f d s ≤ s) →
      ∀ d ∈ l, ∃ t ≤ s, f d t ≠ 0
  | [], _, _, _ => by simp
  | a :: l, h, h0, hle => by
    have ht : l.foldr f s ≠ 0 := fun e => h (by rw [List.foldr_cons, e, h0])
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨_, foldr_le' hle s l, h⟩
    · exact foldr_ne_zero' l ht h0 hle d hd

theorem foldr_ne_zero {f : Nat → Nat → Nat} {s c : Nat} {l : List Nat} (h : l.foldr f s = c)
    (hc : c ≠ 0) (h0 : ∀ d, f d 0 = 0) (hle : ∀ d s, f d s ≤ s) : ∀ d ∈ l, ∃ t ≤ s, f d t ≠ 0 :=
  foldr_ne_zero' l (fun e => hc (h.symm.trans e)) h0 hle

theorem leafOK_sound {ys : List Nat} {gs : List G} (h : PL ys gs) {T : Nat} {τ : G}
    (hT : PRep 4060 12 T τ) {Kh V : Nat → Nat} {l p : Nat}
    (hK : ∀ i < 28, Kh (32 * p + i) < 4060) (hc : leafOK ys T Kh V l p = true) :
    1 ≤ V (64 + 32 * l + 28) ∧ V (64 + 32 * l + 28) ≤ 7 ∧ ∀ b (hb : b < 4),
      (∀ j, 1 ≤ j → j < V (64 + 32 * l + 28) →
        (((gs.prod ^ j * τ * (gs.prod ^ j)⁻¹) ⟨b, by omega⟩ : Fin 4060) : Nat) =
          V (64 + 32 * l + 4 * (j - 1) + b)) ∧
      (((gs.prod ^ V (64 + 32 * l + 28) * τ * (gs.prod ^ V (64 + 32 * l + 28))⁻¹)
        ⟨b, by omega⟩ : Fin 4060) : Nat) = (τ ⟨b, by omega⟩ : Nat) := by
  unfold leafOK at hc
  simp only [strictB_eq, bAnd_eq', Bool.and_eq_true] at hc
  obtain ⟨hq1, hq7, hall⟩ := hc
  have hq1' : 1 ≤ V (64 + 32 * l + 28) := Nat.le_of_ble_eq_true hq1
  have hq7' : V (64 + 32 * l + 28) ≤ 7 := Nat.le_of_ble_eq_true hq7
  refine ⟨hq1', hq7', fun b hb => ?_⟩
  have hb' : b < 4060 := by omega
  have nIf_beq : ∀ a b t e : Nat,
      Bool.rec (motive := fun _ => Nat) e t (Nat.beq a b) = if a = b then t else e := by
    intro a b t e
    by_cases h : a = b
    · rw [if_pos h, Nat.beq_eq.mpr h]
    · rw [if_neg h, P.beq_false_of_ne h]
  have step : ∀ i < V (64 + 32 * l + 28),
      yAp ys (Kh (32 * p + (4 * i + b))) =
        (if i = 0 then b else Kh (32 * p + (4 * (i - 1) + b))) ∧
      yPow ys (i + 1) (apP T (Kh (32 * p + (4 * i + b)))) =
        (if i + 1 = V (64 + 32 * l + 28) then apP T b else V (64 + 32 * l + (4 * i + b))) := by
    intro i hi
    have hbi := RuBase.allN_iff.1 (RuBase.allN_iff.1 hall b hb) i hi
    simp only [strictB_eq, bAnd_eq', Bool.and_eq_true, nIf_beq] at hbi
    exact ⟨Nat.eq_of_beq_eq_true hbi.1, Nat.eq_of_beq_eq_true hbi.2⟩
  have hx : ∀ i < V (64 + 32 * l + 28), Kh (32 * p + (4 * i + b)) < 4060 :=
    fun i hi => hK _ (by omega)
  have key : ∀ i (hi : i < V (64 + 32 * l + 28)),
      (gs.prod ^ (i + 1)) ⟨_, hx i hi⟩ = ⟨b, hb'⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      have e := (step 0 hi).1
      rw [if_pos rfl, yAp_eq h ⟨_, hx 0 hi⟩] at e
      rw [zero_add, pow_one]
      exact Fin.ext e
    | succ i ih =>
      intro hi
      have e := (step (i + 1) hi).1
      rw [if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel, yAp_eq h ⟨_, hx _ hi⟩] at e
      have ey : gs.prod ⟨_, hx _ hi⟩ = ⟨_, hx i (by omega)⟩ := Fin.ext e
      rw [pow_succ, Equiv.Perm.mul_apply, ey]
      exact ih (by omega)
  have conj : ∀ i (hi : i < V (64 + 32 * l + 28)),
      (((gs.prod ^ (i + 1) * τ * (gs.prod ^ (i + 1))⁻¹) ⟨b, hb'⟩ : Fin 4060) : Nat) =
        yPow ys (i + 1) (apP T (Kh (32 * p + (4 * i + b)))) := by
    intro i hi
    have hinv : (gs.prod ^ (i + 1))⁻¹ ⟨b, hb'⟩ = ⟨_, hx i hi⟩ := by
      rw [← key i hi]
      simp
    simp only [Equiv.Perm.mul_apply]
    rw [hinv, apP_eq hT ⟨_, hx i hi⟩, yPow_eq h]
  refine ⟨fun j hj1 hjq => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [conj i (by omega), (step i (by omega)).2,
      if_neg (by omega : i + 1 ≠ V (64 + 32 * l + 28)), Nat.add_sub_cancel, Nat.add_assoc _ (4 * i)]
  · have e : V (64 + 32 * l + 28) = V (64 + 32 * l + 28) - 1 + 1 := (Nat.sub_add_cancel hq1').symm
    rw [e, conj (V (64 + 32 * l + 28) - 1) (by omega), (step (V (64 + 32 * l + 28) - 1) (by omega)).2,
      if_pos (Nat.sub_add_cancel hq1')]
    exact apP_eq hT ⟨b, hb'⟩

theorem chkL3_sound {LR TR W Kh V : Nat → Nat} {H T lo cnt s1 s0 : Nat}
    (hc : chkL3 LR TR W Kh V H T lo cnt s1 s0 = true) :
    ∀ d < cnt, Nat.land (W (lo + d)) 3 = 2 → ∃ p < s1,
      leafOK [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 2) / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + (lo + d) / rcnt (LR 2) % rcnt (LR 1)),
        TR (roff 4060 48720 (LR 2) + (lo + d) % rcnt (LR 2))] T Kh V (W (lo + d) >>> 2) p =
          true := by
  unfold chkL3 at hc
  simp only [strictB_eq] at hc
  have hc' := Nat.eq_of_beq_eq_true hc
  rw [foldN_eq] at hc'
  intro d hd hr
  obtain ⟨t, ht, hf⟩ := foldr_ne_zero hc' (Nat.succ_ne_zero s0)
    (fun d => by
      simp only [P.strictN_eq, Orb.nIf_eq]
      split_ifs <;> rfl)
    (fun d s => by
      simp only [P.strictN_eq, Orb.nIf_eq]
      split_ifs <;> first | exact leafStep_le _ _ _ _ _ _ | exact le_refl _)
    d (List.mem_range.mpr hd)
  have hf' : leafStep [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 2) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + (lo + d) / rcnt (LR 2) % rcnt (LR 1)),
      TR (roff 4060 48720 (LR 2) + (lo + d) % rcnt (LR 2))] T Kh V (W (lo + d)) t ≠ 0 := by
    intro e
    apply hf
    simp only [P.strictN_eq]
    have hr' : Nat.beq (Nat.land (W (Nat.add lo d)) (nat_lit 3)) (nat_lit 2) = true :=
      Nat.beq_eq.mpr hr
    rw [hr']
    exact e
  obtain ⟨h2, hl⟩ := leafStep_spec hr hf'
  exact ⟨t - 2, by omega, hl⟩

theorem chkL2_sound {LR TR W Kh V : Nat → Nat} {H T lo cnt s1 s0 : Nat}
    (hc : chkL2 LR TR W Kh V H T lo cnt s1 s0 = true) :
    ∀ d < cnt, Nat.land (W (lo + d)) 3 = 2 → ∃ p < s1,
      leafOK [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + (lo + d) % rcnt (LR 1))] T Kh V (W (lo + d) >>> 2) p =
          true := by
  unfold chkL2 at hc
  simp only [strictB_eq] at hc
  have hc' := Nat.eq_of_beq_eq_true hc
  rw [foldN_eq] at hc'
  intro d hd hr
  obtain ⟨t, ht, hf⟩ := foldr_ne_zero hc' (Nat.succ_ne_zero s0)
    (fun d => by
      simp only [P.strictN_eq, Orb.nIf_eq]
      split_ifs <;> rfl)
    (fun d s => by
      simp only [P.strictN_eq, Orb.nIf_eq]
      split_ifs <;> first | exact leafStep_le _ _ _ _ _ _ | exact le_refl _)
    d (List.mem_range.mpr hd)
  have hf' : leafStep [H, TR (roff 4060 48720 (LR 0) + (lo + d) / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + (lo + d) % rcnt (LR 1))] T Kh V (W (lo + d)) t ≠ 0 := by
    intro e
    apply hf
    simp only [P.strictN_eq]
    have hr' : Nat.beq (Nat.land (W (Nat.add lo d)) (nat_lit 3)) (nat_lit 2) = true :=
      Nat.beq_eq.mpr hr
    rw [hr']
    exact e
  obtain ⟨h2, hl⟩ := leafStep_spec hr hf'
  exact ⟨t - 2, by omega, hl⟩

section Enum

variable {S : Array (Array Nat)} {base : Array Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP : Nat}

theorem levT_prep (hb : Binds 4060 12 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS nb BP) {i : Nat} (hi : i < nb) :
    (ChainArrays.lev 4060 S base i).pts.size = rcnt (LR i) ∧ ∀ k < rcnt (LR i),
      PRep 4060 12 (TR (roff 4060 48720 (LR i) + k)) (ChainArrays.levT 4060 S base i k) := by
  obtain ⟨A, P⟩ := agree_levelK hb hp (base_lt_of_levels hb hl) (R := LR) (TRI := TRI) hi (hl i hi)
  refine ⟨A.cnt.symm, fun k hk => ?_⟩
  have e : ChainArrays.levT 4060 S base i k = permOfArr 4060 (unpack 4060 12 (TR (roff 4060 (4060 * 12) (LR i) + k))) :=
    CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (A.tr k (A.cnt ▸ hk)).1
  rw [e]
  exact (P k hk).1

theorem mem_levList {i : Nat} {t : G} (ht : t ∈ levList 4060 S base i) :
    ∃ k < (ChainArrays.lev 4060 S base i).pts.size, t = ChainArrays.levT 4060 S base i k := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
  exact ⟨k, List.mem_range.mp hk, rfl⟩

theorem mem_products_cons {T : List G} {Ts : List (List G)} {x : G} (h : x ∈ products (T :: Ts)) :
    ∃ t ∈ T, ∃ r ∈ products Ts, x = t * r := by
  rw [products, List.mem_flatMap] at h
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  exact ⟨t, ht, r, hr, rfl⟩

theorem mem_products_nil {x : G} (h : x ∈ products ([] : List (List G))) : x = 1 := by
  rw [products, List.mem_singleton] at h
  exact h

theorem idx2 {a b c0 c1 : Nat} (ha : a < c0) (hb : b < c1) :
    b + c1 * a < c0 * c1 ∧ (b + c1 * a) / c1 = a ∧ (b + c1 * a) % c1 = b := by
  have hc : 0 < c1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · calc b + c1 * a < c1 + c1 * a := by omega
      _ = c1 * (a + 1) := by ring
      _ ≤ c1 * c0 := Nat.mul_le_mul_left _ ha
      _ = c0 * c1 := Nat.mul_comm _ _
  · rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem enum2 (hb : Binds 4060 12 PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP) {c : G}
    (hc : c ∈ products ((List.range 2).map (levList 4060 S base))) :
    ∃ i < rcnt (LR 0) * rcnt (LR 1), ∃ g₀ g₁ : G,
      PRep 4060 12 (TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1))) g₀ ∧
      PRep 4060 12 (TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))) g₁ ∧ c = g₀ * g₁ := by
  rw [show (List.range 2).map (levList 4060 S base) =
    [levList 4060 S base 0, levList 4060 S base 1] from rfl] at hc
  obtain ⟨t0, ht0, r, hr, rfl⟩ := mem_products_cons hc
  obtain ⟨t1, ht1, r', hr', rfl⟩ := mem_products_cons hr
  obtain rfl := mem_products_nil hr'
  obtain ⟨a, ha, rfl⟩ := mem_levList ht0
  obtain ⟨b, hb', rfl⟩ := mem_levList ht1
  obtain ⟨s0, P0⟩ := levT_prep hb hp hl (i := 0) (by omega)
  obtain ⟨s1, P1⟩ := levT_prep hb hp hl (i := 1) (by omega)
  rw [s0] at ha
  rw [s1] at hb'
  obtain ⟨hi, e1, e2⟩ := idx2 ha hb'
  exact ⟨_, hi, _, _, by rw [e1]; exact P0 a ha, by rw [e2]; exact P1 b hb', by rw [mul_one]⟩

theorem enum3 (hb : Binds 4060 12 PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 3 BP) {c : G}
    (hc : c ∈ products ((List.range 3).map (levList 4060 S base))) :
    ∃ i < rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2), ∃ g₀ g₁ g₂ : G,
      PRep 4060 12 (TR (roff 4060 48720 (LR 0) + i / rcnt (LR 2) / rcnt (LR 1))) g₀ ∧
      PRep 4060 12 (TR (roff 4060 48720 (LR 1) + i / rcnt (LR 2) % rcnt (LR 1))) g₁ ∧
      PRep 4060 12 (TR (roff 4060 48720 (LR 2) + i % rcnt (LR 2))) g₂ ∧ c = g₀ * g₁ * g₂ := by
  rw [show (List.range 3).map (levList 4060 S base) =
    [levList 4060 S base 0, levList 4060 S base 1, levList 4060 S base 2] from rfl] at hc
  obtain ⟨t0, ht0, r, hr, rfl⟩ := mem_products_cons hc
  obtain ⟨t1, ht1, r', hr', rfl⟩ := mem_products_cons hr
  obtain ⟨t2, ht2, r'', hr'', rfl⟩ := mem_products_cons hr'
  obtain rfl := mem_products_nil hr''
  obtain ⟨a, ha, rfl⟩ := mem_levList ht0
  obtain ⟨b, hb', rfl⟩ := mem_levList ht1
  obtain ⟨d, hd, rfl⟩ := mem_levList ht2
  obtain ⟨s0, P0⟩ := levT_prep hb hp hl (i := 0) (by omega)
  obtain ⟨s1, P1⟩ := levT_prep hb hp hl (i := 1) (by omega)
  obtain ⟨s2, P2⟩ := levT_prep hb hp hl (i := 2) (by omega)
  rw [s0] at ha
  rw [s1] at hb'
  rw [s2] at hd
  obtain ⟨hq, e1, e2⟩ := idx2 ha hb'
  obtain ⟨hi, e3, e4⟩ := idx2 hq hd
  refine ⟨_, hi, _, _, _, by rw [e3, e1]; exact P0 a ha, by rw [e3, e2]; exact P1 b hb',
    by rw [e4]; exact P2 d hd, by rw [mul_one, mul_assoc]⟩

end Enum

theorem scan2_sound {n0 : Nat} {Q : RawSchreierDatum 4060} {O S : Array (Array Nat)}
    {base : Array Nat} {Wd : Array (List ℤ)} {chunks : Nat} (hA : ChainArrays Q O S base Wd)
    (hc0 : 0 < chunks) (hchk : rawChainOK 4060 O S base Wd chunks = true) (hQ : Q.baseCount = 2)
    {PS PSI LR TR TRI : Nat → Nat} {kS BP : Nat} (hb : Binds 4060 12 PS kS 2 BP S base)
    (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
    (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP) {W : Nat → Nat} {H T K cnt : Nat}
    {h τ : G} (hH : PRep 4060 12 H h) (hT : PRep 4060 12 T τ)
    (hK : rcnt (LR 0) * rcnt (LR 1) ≤ K * cnt)
    (hck : ∀ q < K, chk2 LR TR W H T (cnt * q) cnt = true)
    (hbd : ∀ q < K, bndK W (cnt * q) cnt = true) {c : G} (hc : c ∈ Q.originalSubgroup) :
    (∀ e ∈ [125, 7, 13, 29], (h * c) ^ e ≠ 1) ∨
      ∃ j : Nat, τ * ((h * c) ^ j * τ * ((h * c) ^ j)⁻¹) ≠ (h * c) ^ j * τ * ((h * c) ^ j)⁻¹ * τ := by
  have hm := mem_products_of_mem hA hc0 hchk hc
  rw [hQ] at hm
  obtain ⟨i, hi, g₀, g₁, P0, P1, rfl⟩ := enum2 hb hp hl hm
  have hi' : i < K * cnt := lt_of_lt_of_le hi hK
  have hpl : PL [H, TR (roff 4060 48720 (LR 0) + i / rcnt (LR 1)),
      TR (roff 4060 48720 (LR 1) + i % rcnt (LR 1))] [h, g₀, g₁] :=
    .cons hH (.cons P0 (.cons P1 .nil))
  have e : [h, g₀, g₁].prod = h * (g₀ * g₁) := by simp [mul_assoc]
  have := witK_sound hpl hT (bnd_all hbd i hi') (chk2_all hck i hi')
  rwa [e] at this

theorem leaf_facts {M : Type} [Group M] {y τ : M} {q : Nat} (hq : 0 < q) {L : Nat → M}
    (h0 : L 0 = τ) (hs : ∀ j < q, y * L j * y⁻¹ = L ((j + 1) % q)) {cand : List M}
    (hc : ∀ x ∈ cand, x ∈ Subgroup.closure {g | ∃ j < q, L j = g})
    (hL : ∀ j < q, L j ∈ Subgroup.closure {x | x ∈ cand}) :
    (∀ x ∈ cand, x ∈ orbSub y τ) ∧ ∀ x ∈ cand, y * x * y⁻¹ ∈ Subgroup.closure {x | x ∈ cand} := by
  have horb : ∀ j, y ^ j * τ * (y ^ j)⁻¹ = L (j % q) := by
    intro j
    induction j with
    | zero => rw [pow_zero, inv_one, mul_one, one_mul, Nat.zero_mod, h0]
    | succ j ih =>
      calc y ^ (j + 1) * τ * (y ^ (j + 1))⁻¹ = y * (y ^ j * τ * (y ^ j)⁻¹) * y⁻¹ := by group
        _ = L ((j % q + 1) % q) := by rw [ih, hs _ (Nat.mod_lt _ hq)]
        _ = L ((j + 1) % q) := by rw [Nat.mod_add_mod]
  have hle : Subgroup.closure {g | ∃ j < q, L j = g} ≤ orbSub y τ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [← Nat.mod_eq_of_lt hj, ← horb]
    exact conj_mem_orbSub y τ j
  have heq : Subgroup.closure {g | ∃ j < q, L j = g} = Subgroup.closure {x | x ∈ cand} := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hL j hj
    · rw [Subgroup.closure_le]
      intro x hx
      exact hc x hx
  refine ⟨fun x hx => hle (hc x hx), fun x hx => ?_⟩
  rw [← heq]
  have hconj : Subgroup.closure {g | ∃ j < q, L j = g} ≤
      (Subgroup.closure {g | ∃ j < q, L j = g}).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change y * L j * y⁻¹ ∈ _
    rw [hs j hj]
    exact Subgroup.subset_closure ⟨_, Nat.mod_lt _ hq, rfl⟩
  exact hconj (hc x hx)

theorem period3 {M : Type*} [Group M] {h τ c : M} (hc : c * τ = τ * c)
    (hs : c * (h * τ * h⁻¹) = h * τ * h⁻¹ * c)
    (hu : c * (h * (h * τ * h⁻¹) * h⁻¹) = h * (h * τ * h⁻¹) * h⁻¹ * c)
    (h3 : h * (h * (h * τ * h⁻¹) * h⁻¹) * h⁻¹ = τ) (hs1 : h * τ * h⁻¹ ≠ τ)
    (hu1 : h * (h * τ * h⁻¹) * h⁻¹ ≠ τ) {e : Nat} (he : e % 3 ≠ 0) : (h * c) ^ e ≠ 1 := by
  intro hy
  set s := h * τ * h⁻¹ with hs_def
  set u := h * s * h⁻¹ with hu_def
  set y := h * c with hy_def
  have conj_c : ∀ t : M, c * t = t * c → c * t * c⁻¹ = t := fun t ht => by
    rw [ht, mul_inv_cancel_right]
  have f1 : y * τ * y⁻¹ = s := by
    calc y * τ * y⁻¹ = h * (c * τ * c⁻¹) * h⁻¹ := by rw [hy_def]; group
      _ = s := by rw [conj_c τ hc]
  have f2 : y * s * y⁻¹ = u := by
    calc y * s * y⁻¹ = h * (c * s * c⁻¹) * h⁻¹ := by rw [hy_def]; group
      _ = u := by rw [conj_c s hs]
  have f3 : y * u * y⁻¹ = τ := by
    calc y * u * y⁻¹ = h * (c * u * c⁻¹) * h⁻¹ := by rw [hy_def]; group
      _ = τ := by rw [conj_c u hu, h3]
  have g3 : y ^ 3 * τ * (y ^ 3)⁻¹ = τ := by
    calc y ^ 3 * τ * (y ^ 3)⁻¹ = y * (y * (y * τ * y⁻¹) * y⁻¹) * y⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      _ = τ := by rw [f1, f2, f3]
  have gm : ∀ m : Nat, y ^ (3 * m) * τ * (y ^ (3 * m))⁻¹ = τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y ^ (3 * (m + 1)) * τ * (y ^ (3 * (m + 1)))⁻¹ =
          y ^ (3 * m) * (y ^ 3 * τ * (y ^ 3)⁻¹) * (y ^ (3 * m))⁻¹ := by
            rw [show 3 * (m + 1) = 3 * m + 3 by ring, pow_add]
            group
        _ = τ := by rw [g3, ih]
  have key : y ^ (e % 3) * τ * (y ^ (e % 3))⁻¹ = τ := by
    calc y ^ (e % 3) * τ * (y ^ (e % 3))⁻¹ =
        y ^ (e % 3) * (y ^ (3 * (e / 3)) * τ * (y ^ (3 * (e / 3)))⁻¹) * (y ^ (e % 3))⁻¹ := by
          rw [gm]
      _ = y ^ (e % 3 + 3 * (e / 3)) * τ * (y ^ (e % 3 + 3 * (e / 3)))⁻¹ := by
          rw [pow_add]
          group
      _ = τ := by rw [Nat.mod_add_div, hy]; group
  rcases (by omega : e % 3 = 1 ∨ e % 3 = 2) with hr | hr
  · rw [hr, pow_one, f1] at key
    exact hs1 key
  · have : y ^ 2 * τ * (y ^ 2)⁻¹ = u := by
      calc y ^ 2 * τ * (y ^ 2)⁻¹ = y * (y * τ * y⁻¹) * y⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = u := by rw [f1, f2]
    rw [hr, this] at key
    exact hu1 key

theorem cjF_eq {H HI : Nat} {h : G} (hH : PRep 4060 12 H h) (hHI : PRep 4060 12 HI h⁻¹)
    {f : Nat → Nat} {σ : G} (hf : ∀ x : Fin 4060, f x = (σ x : Nat)) (x : Fin 4060) :
    cjF H HI f x = ((h * σ * h⁻¹) x : Nat) := by
  unfold cjF
  rw [apP_eq hHI, hf, apP_eq hH]
  rfl

theorem commP_sound {f : Nat → Nat} {σ : G} (hf : ∀ x : Fin 4060, f x = (σ x : Nat)) {P : Nat}
    {g : G} (hP : PRep 4060 12 P g) (h : commP f P = true) : g * σ = σ * g := by
  refine Equiv.ext fun x => Fin.ext ?_
  have := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h x x.2)
  rw [apP_eq hP x, hf, hf, apP_eq hP] at this
  exact this.symm

theorem eqF_sound {f g : Nat → Nat} {σ ρ : G} (hf : ∀ x : Fin 4060, f x = (σ x : Nat))
    (hg : ∀ x : Fin 4060, g x = (ρ x : Nat)) : eqF f g = true ↔ σ = ρ := by
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := Nat.eq_of_beq_eq_true (RuBase.allN_iff.1 h x x.2)
    rwa [hf, hg] at this
  · rintro rfl
    refine RuBase.allN_iff.2 fun x hx => ?_
    have e1 := hf ⟨x, hx⟩
    have e2 := hg ⟨x, hx⟩
    exact Nat.beq_eq.mpr (e1.trans e2.symm)

theorem p3K_sound {H T : Nat} {Ls : Nat → Nat} {k : Nat} {h τ : G} {gens : Nat → G}
    (hH : PRep 4060 12 H h) (hT : PRep 4060 12 T τ) (hL : ∀ l < k, PRep 4060 12 (Ls l) (gens l))
    (hc : p3K H T Ls k = true) :
    (∀ l < k, gens l * (h * τ * h⁻¹) = h * τ * h⁻¹ * gens l ∧
      gens l * (h * (h * τ * h⁻¹) * h⁻¹) = h * (h * τ * h⁻¹) * h⁻¹ * gens l) ∧
    h * (h * (h * τ * h⁻¹) * h⁻¹) * h⁻¹ = τ ∧ h * τ * h⁻¹ ≠ τ ∧ h * (h * τ * h⁻¹) * h⁻¹ ≠ τ := by
  unfold p3K at hc
  rw [strictB_eq] at hc
  simp only [bAnd_eq', Bool.and_eq_true] at hc
  obtain ⟨hcomm, h3, hs, hu⟩ := hc
  have hHI := prep_invP hH
  have fT : ∀ x : Fin 4060, apP T x = (τ x : Nat) := apP_eq hT
  have fS := cjF_eq hH hHI fT
  have fU := cjF_eq hH hHI fS
  have fW := cjF_eq hH hHI fU
  refine ⟨fun l hl => ?_, (eqF_sound fW fT).1 h3, fun e => ?_, fun e => ?_⟩
  · have := RuBase.allN_iff.1 hcomm l hl
    simp only [bAnd_eq', Bool.and_eq_true] at this
    exact ⟨commP_sound fS (hL l hl) this.1, commP_sound fU (hL l hl) this.2⟩
  · rw [(eqF_sound fS fT).2 e] at hs
    exact Bool.false_ne_true hs
  · rw [(eqF_sound fU fT).2 e] at hu
    exact Bool.false_ne_true hu

theorem p3_ne_one {H T : Nat} {Ls : Nat → Nat} {k : Nat} {h τ : G} {gens : Nat → G}
    (hH : PRep 4060 12 H h) (hT : PRep 4060 12 T τ) (hL : ∀ l < k, PRep 4060 12 (Ls l) (gens l))
    (hc : p3K H T Ls k = true)
    (hK : ∀ c ∈ Subgroup.closure {g | ∃ l < k, gens l = g}, c * τ = τ * c) :
    ∀ c ∈ Subgroup.closure {g | ∃ l < k, gens l = g}, ∀ e : Nat, e % 3 ≠ 0 → (h * c) ^ e ≠ 1 := by
  obtain ⟨hcomm, h3, hs1, hu1⟩ := p3K_sound hH hT hL hc
  have hcen : ∀ z : G, (∀ l < k, gens l * z = z * gens l) →
      ∀ c ∈ Subgroup.closure {g | ∃ l < k, gens l = g}, c * z = z * c := by
    intro z hz c hcK
    have hle : Subgroup.closure {g | ∃ l < k, gens l = g} ≤ Subgroup.centralizer {z} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hz l hl)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hcK)
  intro c hcK e he
  exact period3 (hK c hcK) (hcen _ (fun l hl => (hcomm l hl).1) c hcK)
    (hcen _ (fun l hl => (hcomm l hl).2) c hcK) h3 hs1 hu1 he

end CFSG.KC.Misc.RuScan

end
