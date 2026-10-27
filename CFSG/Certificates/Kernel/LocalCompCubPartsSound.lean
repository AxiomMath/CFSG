module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.LocalCompSqReplaySnd
import all CFSG.Certificates.Kernel.LocalQT.Steps
import all Certificates.Data.Kernel.LocalComp.CubParts

public section

namespace CFSG.KC.LocalComp.CubParts

open CFSG.KC.LQT CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native CFSG.KS.Ord CFSG.KC.Ord
open CFSG.KC.LocalComp.ElemParts CFSG.KC.OpsLayK CFSG.KC.OpsLayK.Snd
open CFSG.KC.LocalComp.Ops3Snd

private theorem ksCP_powIs_spec {P : Nat → Nat} {N a t e : Nat} (h : powIs P N a t e = true) :
    t < N ∧ e < expoFail ∧ expoK P a 64 t = e := by
  unfold powIs at h
  obtain ⟨ht, h⟩ := SecS.andT h
  obtain ⟨he, hk⟩ := SecS.andT h
  exact ⟨Nat.blt_eq.mp ht, Nat.blt_eq.mp he, Nat.eq_of_beq_eq_true hk⟩

private theorem ksCP_stepIs_spec {P : Nat → Nat} {N t a b : Nat}
    (h : stepIs P N t a b = true) :
    3 ≤ t ∧ t < N ∧ P t = a + 1048576 * b := by
  unfold stepIs at h
  obtain ⟨h1, h⟩ := SecS.andT h
  obtain ⟨h2, h3⟩ := SecS.andT h
  refine ⟨Nat.ble_eq.mp h1, Nat.blt_eq.mp h2, ?_⟩
  have := Nat.eq_of_beq_eq_true h3
  rw [this]
  change a + (b <<< 20) = a + 1048576 * b
  rw [Nat.shiftLeft_eq]
  omega

private theorem ksCP_stepIs_val {c : Lay} {V P : Nat → Nat} {N : Nat} (hN : N ≤ 1048576)
    (hs : StepsTo (stepOK c V P) N) {t a b : Nat} (h : stepIs P N t a b = true) (ha : a < N) :
    V t = c.mul (V a) (V b) := by
  obtain ⟨h3, htN, hP⟩ := ksCP_stepIs_spec h
  have hs' : ∀ n, 3 ≤ n → n < N → stepOK c V P n = true := hs
  exact (stepOK_of_pair (hs' t h3 htN) hP (by omega)).2.2

private theorem ksCP_lrel_pow {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {X : Array FV} {x t e : Nat} (hX : LRel c X x) (ht : Canon c.p c.d c.w t)
    (hm : mat3 c t = mat3 c x ^ e) : LRel c ((ops3 c.d).pow X e) t := by
  have h := CFSG.KC.LocalComp.SqReplaySnd.rel_lpow hc hp hX e
  refine ⟨ht, h.2.1, ?_⟩
  rw [h.2.2, (CFSG.KC.LocalComp.SqReplaySnd.mat3_pow hc hp hX.1 e).2]
  exact hm.symm

private theorem ksCP_powIs_lrel {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {X : Array FV} {a t e : Nat} (hX : LRel c X (V a)) (h : powIs P N a t e = true) :
    LRel c ((ops3 c.d).pow X e) (V t) := by
  obtain ⟨htN, hef, heK⟩ := ksCP_powIs_spec h
  have hcan : Canon c.p c.d c.w (V t) := hV.canon t (Or.inl htN)
  have hm : mat3 c (V t) = mat3 c (V a) ^ e := by
    rw [← heK]
    exact expoK_spec hV a 64 t (Or.inl htN) (by rw [heK]; exact hef)
  exact ksCP_lrel_pow hV.hc hV.hp hX hcan hm

private theorem ksCP_stepIs_lrel {c : Lay} {V P : Nat → Nat} {N : Nat} (hV : Vals c V P N)
    {X Y : Array FV} {a b t : Nat} (hX : LRel c X (V a)) (hY : LRel c Y (V b))
    (h : stepIs P N t a b = true) (ha : a < N) : LRel c ((ops3 c.d).mul X Y) (V t) := by
  obtain ⟨-, htN, -⟩ := ksCP_stepIs_spec h
  have hcan : Canon c.p c.d c.w (V t) := hV.canon t (Or.inl htN)
  have he := ksCP_stepIs_val hV.hN hV.step h ha
  have hrel := rel_mul hV.hc hV.hp hX hY
  refine ⟨hcan, hrel.2.1, ?_⟩
  rw [hrel.2.2, ← he]

private theorem ksCP_appBaseK_zero (c : Lay) (b : Nat) (xs : List Nat) (v : Nat) :
    appBaseK c b xs 0 v = v := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih =>
    change appBaseK c b xs (0 / b) (c.vpow x v (0 % b)) = v
    rw [Nat.zero_div, Nat.zero_mod]
    change appBaseK c b xs 0 v = v
    exact ih v

private theorem ksCP_digApp_eq_appBaseK (c : Lay) (b : Nat) (X : Nat → Nat) :
    ∀ (m i n v : Nat), digApp c b X m i n v =
      appBaseK c b ((List.range m).map fun q => X (i + q)) n v
  | 0, i, n, v => rfl
  | m + 1, i, n, v => by
    change digApp c b X m (i + 1) (n / b) (c.vpow (X i) v (n % b)) = _
    rw [ksCP_digApp_eq_appBaseK c b X m (i + 1) (n / b) (c.vpow (X i) v (n % b))]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons]
    simp only [List.map_map]
    have hlist : List.map ((fun q => X (i + q)) ∘ Nat.succ) (List.range m) =
        List.map (fun q => X (i + 1 + q)) (List.range m) := by
      apply List.map_congr_left
      intro q hq
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [hlist]
    simp only [Nat.add_zero]
    rfl

private theorem ksCP_digApp_zero (c : Lay) (b : Nat) (X : Nat → Nat)
    (m i v : Nat) : digApp c b X m i 0 v = v := by
  rw [ksCP_digApp_eq_appBaseK]
  exact ksCP_appBaseK_zero c b _ v

private theorem ksCP_sub_pow_div {b h n : Nat} (hb : 0 < b) (hh : 0 < h) (hn : b ^ h ≤ n) :
    (n - b ^ h) / b = n / b - b ^ (h - 1) ∧ (n - b ^ h) % b = n % b := by
  have hpow : b ^ h = b * b ^ (h - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hc : b ^ (h - 1) ≤ n / b := by
    rw [Nat.le_div_iff_mul_le hb]
    calc b ^ (h - 1) * b = b ^ h := by rw [Nat.mul_comm, ← hpow]
      _ ≤ n := hn
  have hbc : b * b ^ (h - 1) ≤ b * (n / b) := Nat.mul_le_mul_left b hc
  have hdecomp : n - b ^ h = b * (n / b - b ^ (h - 1)) + n % b := by
    conv_lhs => rw [← Nat.div_add_mod n b]
    rw [hpow, Nat.sub_add_comm hbc, Nat.mul_sub_left_distrib]
  refine ⟨?_, ?_⟩
  · rw [hdecomp, Nat.mul_add_div hb, Nat.div_eq_of_lt (Nat.mod_lt n hb), Nat.add_zero]
  · rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt n hb)]

private theorem ksCP_appBaseK_step {c : Lay} {b : Nat} (hb : 0 < b) (xs : List Nat) :
    ∀ {h n v : Nat}, h < xs.length → b ^ h ≤ n → n < b ^ h * b →
      appBaseK c b xs n v = c.vpow (xs.getD h 0) (appBaseK c b xs (n - b ^ h) v) 1 := by
  induction xs with
  | nil => intro h n v hh; simp at hh
  | cons x xs ih =>
    intro h n v hh hq hn
    cases h with
    | zero =>
      have hq1 : 1 ≤ n := by simpa using hq
      have hnpos : 0 < n := by omega
      have hn' : n < b := by simpa using hn
      have h1 : n / b = 0 := Nat.div_eq_of_lt hn'
      have h2 : n % b = n := Nat.mod_eq_of_lt hn'
      have h3 : (n - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
      have h4 : (n - 1) % b = n - 1 := Nat.mod_eq_of_lt (by omega)
      change appBaseK c b xs (n / b) (c.vpow x v (n % b)) =
        c.vpow x (appBaseK c b xs ((n - 1) / b) (c.vpow x v ((n - 1) % b))) 1
      rw [h1, h2, h3, h4, ksCP_appBaseK_zero, ksCP_appBaseK_zero]
      rw [show n = n - 1 + 1 by omega]
      rfl
    | succ h' =>
      have hq' : b ^ h' ≤ n / b := by
        rw [Nat.le_div_iff_mul_le hb]
        simpa [Nat.pow_succ] using hq
      have hn' : n / b < b ^ h' * b := by
        rw [Nat.div_lt_iff_lt_mul hb]
        simpa [Nat.pow_succ] using hn
      have ih' := ih (h := h') (n := n / b) (v := c.vpow x v (n % b))
        (by simpa using hh) hq' hn'
      have hdiv := (ksCP_sub_pow_div hb (Nat.succ_pos h') hq).1
      have hmod := (ksCP_sub_pow_div hb (Nat.succ_pos h') hq).2
      change appBaseK c b xs (n / b) (c.vpow x v (n % b)) =
        c.vpow (xs.getD h' 0)
          (appBaseK c b xs ((n - b ^ (h' + 1)) / b)
            (c.vpow x v ((n - b ^ (h' + 1)) % b))) 1
      rw [hdiv, hmod]
      simpa [Nat.add_sub_cancel] using ih'

private theorem ksCP_digApp_step {c : Lay} {b : Nat} {X : Nat → Nat} {m h n v : Nat}
    (hb : 0 < b) (hh : h < m)
    (hq : b ^ h ≤ n) (hn : n < b ^ h * b) :
    digApp c b X m 0 n v = c.vpow (X h) (digApp c b X m 0 (n - b ^ h) v) 1 := by
  rw [ksCP_digApp_eq_appBaseK c b X m 0 n v,
    ksCP_digApp_eq_appBaseK c b X m 0 (n - b ^ h) v]
  have hget : ((List.range m).map fun q => X (0 + q)).getD h 0 = X h := by
    rw [List.getD_eq_getElem _ _ (by simpa using hh)]
    simp
  rw [← hget]
  exact ksCP_appBaseK_step hb ((List.range m).map fun q => X (0 + q)) (by simpa using hh) hq hn

private theorem ksCP_vtabK_spec {c : Lay} {b : Nat} {X : Nat → Nat} {m : Nat}
    {U HI : Nat → Nat} {lo cnt : Nat}
    (h : vtabK c b X m U HI lo cnt = true) :
    ∀ j, j < cnt → ∀ n, n = lo + j + 1 → n < b ^ m →
      ∃ hh, hh = HI n ∧ hh < m ∧ b ^ hh ≤ n ∧ n < b ^ hh * b ∧
        U n = c.vec (U (n - b ^ hh)) (X hh) := by
  intro j hj n hn hnm
  subst n
  unfold vtabK at h
  have hj' := SecS.allLt_spec h j hj
  simp only [SecS.strictB_eq] at hj'
  have h := hj'
  have hcond : ((lo + j + 1).blt (b ^ m)) = true := Nat.blt_eq.mpr hnm
  have hbody : (strictB (HI (lo + j + 1)) fun hh => strictB (b ^ hh) fun q =>
      andB (Nat.blt hh m) (andB (Nat.ble q (lo + j + 1)) (andB
        (Nat.blt (lo + j + 1) (Nat.mul q b))
        (Nat.beq (U (lo + j + 1)) (c.vec (U (lo + j + 1 - q)) (X hh)))))) = true := by
    simp only [Nat.succ_eq_add_one] at h
    have hcond' : ((lo.add j + 1).blt (b.pow m)) = true := by simpa using hcond
    rw [hcond'] at h
    simp only [SecS.strictB_eq]
    exact h
  simp only [SecS.strictB_eq] at hbody
  obtain ⟨hh', hbody⟩ := SecS.andT hbody
  obtain ⟨hq, hbody⟩ := SecS.andT hbody
  obtain ⟨hnb, hU⟩ := SecS.andT hbody
  exact ⟨HI (lo + j + 1), rfl, Nat.blt_eq.mp hh', Nat.ble_eq.mp hq,
    Nat.blt_eq.mp hnb, Nat.eq_of_beq_eq_true hU⟩

private theorem ksCP_U_step {c : Lay} {b : Nat} {X : Nat → Nat} {m : Nat}
    {U HI : Nat → Nat} {NS CH : Nat}
    (hv : ChunksTo (fun s => vtabK c b X m U HI (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow b m) 1 ≤ Nat.mul NS CH) {n : Nat} (hn1 : 1 ≤ n)
    (hnm : n < b ^ m) :
    ∃ h, h < m ∧ b ^ h ≤ n ∧ n < b ^ h * b ∧ U n = c.vec (U (n - b ^ h)) (X h) := by
  have hnm' : n < Nat.pow b m := by simpa using hnm
  have hbm : 2 ≤ Nat.pow b m := Nat.succ_le_of_lt (lt_of_le_of_lt hn1 hnm')
  have hCH : 0 < CH := by
    apply Nat.pos_of_mul_pos_left (a := NS)
    have h1 : 0 < Nat.sub (Nat.pow b m) 1 := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hbm)
    exact lt_of_lt_of_le h1 hNS
  have hlt : Nat.sub n 1 < Nat.mul NS CH := by
    have h1 : Nat.sub n 1 < Nat.sub (Nat.pow b m) 1 :=
      (Nat.sub_lt_sub_iff_right hn1).2 hnm'
    exact lt_of_lt_of_le h1 hNS
  have hs : Nat.div (Nat.sub n 1) CH < NS := (Nat.div_lt_iff_lt_mul hCH).2 hlt
  have hj : Nat.mod (Nat.sub n 1) CH < CH := Nat.mod_lt _ hCH
  have hn : n = CH * ((n - 1) / CH) + (n - 1) % CH + 1 := by
    have hpos : 0 < n := by omega
    have hdiv := Nat.div_add_mod (n - 1) CH
    omega
  obtain ⟨h, -, hh, hq, hnb, hU⟩ :=
    ksCP_vtabK_spec (hv (Nat.div (Nat.sub n 1) CH) hs) _ hj n hn hnm
  exact ⟨h, hh, hq, hnb, hU⟩

private theorem ksCP_U_digApp {c : Lay} {b : Nat} (hb : 0 < b) {X : Nat → Nat} {m : Nat}
    {U HI : Nat → Nat} {NS CH : Nat}
    (hv : ChunksTo (fun s => vtabK c b X m U HI (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow b m) 1 ≤ Nat.mul NS CH) {v : Nat} (hU0 : U 0 = v) :
    ∀ n, n < b ^ m → U n = digApp c b X m 0 n v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnm
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hU0]
      exact (ksCP_digApp_zero c b X m 0 v).symm
    · obtain ⟨h, hh, hq, hnb, hstep⟩ :=
        ksCP_U_step hv hNS (Nat.succ_le_of_lt hpos) hnm
      have hqpos : 0 < b ^ h := by positivity
      rw [hstep, ih (n - b ^ h) (by omega) (by omega)]
      exact (ksCP_digApp_step hb hh hq hnb).symm

private theorem ksCP_ne_of_notB {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := by
  intro hab
  subst hab
  simp [CFSG.KC.Ord.notB, Nat.beq_refl] at h

private theorem ksCP_cub_pows {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {X Y H : Array FV} (hV : Vals c V P N)
    (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1))) (hH : LRel c H (V (O 2)))
    (hq : cubPartsOK c V P N (O 0) (O 1) (O 2) I D.r D.oh D.a D.b D.c D.d D.k D.l D.μ D.t
      = true) :
    N ≤ 1048576 ∧ O 0 < N ∧ O 1 < N ∧ O 2 < N ∧ 0 < D.r ∧ 0 < D.oh ∧ D.t < c.d ∧
      (ops3 c.d).eq ((ops3 c.d).pow X D.r) (ops3 c.d).one = true ∧
      (ops3 c.d).eq ((ops3 c.d).pow Y D.r) (ops3 c.d).one = true ∧
      (ops3 c.d).eq ((ops3 c.d).pow H D.oh) (ops3 c.d).one = true := by
  obtain ⟨hNle, hq⟩ := SecS.andT hq
  obtain ⟨hix, hq⟩ := SecS.andT hq
  obtain ⟨hiy, hq⟩ := SecS.andT hq
  obtain ⟨hih, hq⟩ := SecS.andT hq
  obtain ⟨hr0, hq⟩ := SecS.andT hq
  obtain ⟨hoh0, hq⟩ := SecS.andT hq
  obtain ⟨ht, hq⟩ := SecS.andT hq
  obtain ⟨hpowX, hq⟩ := SecS.andT hq
  obtain ⟨hVX, hq⟩ := SecS.andT hq
  obtain ⟨hpowY, hq⟩ := SecS.andT hq
  obtain ⟨hVY, hq⟩ := SecS.andT hq
  obtain ⟨hpowH, hq⟩ := SecS.andT hq
  obtain ⟨hVH, -⟩ := SecS.andT hq
  refine ⟨Nat.ble_eq.mp hNle, Nat.blt_eq.mp hix, Nat.blt_eq.mp hiy, Nat.blt_eq.mp hih,
    Nat.blt_eq.mp hr0, Nat.blt_eq.mp hoh0, Nat.blt_eq.mp ht, ?_, ?_, ?_⟩
  · exact eq_of_rel (ksCP_powIs_lrel hV hX hpowX) (rel_one hV.hc hV.hp) hVX
  · exact eq_of_rel (ksCP_powIs_lrel hV hY hpowY) (rel_one hV.hc hV.hp) hVY
  · exact eq_of_rel (ksCP_powIs_lrel hV hH hpowH) (rel_one hV.hc hV.hp) hVH

private theorem ksCP_cub_Z {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {X Y : Array FV} (hV : Vals c V P N)
    (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1)))
    (hq : cubPartsOK c V P N (O 0) (O 1) (O 2) I D.r D.oh D.a D.b D.c D.d D.k D.l D.μ D.t
      = true) :
    LRel c ((ops3 c.d).commM D.r X Y) (V (I 7)) := by
  obtain ⟨hix, hq⟩ := SecS.andT (SecS.andT hq).2
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hI3, hq⟩ := SecS.andT hq
  obtain ⟨hI4, hq⟩ := SecS.andT hq
  obtain ⟨hI5, hq⟩ := SecS.andT hq
  obtain ⟨hI6, hq⟩ := SecS.andT hq
  obtain ⟨hI7, -⟩ := SecS.andT hq
  have h3 := ksCP_stepIs_lrel hV hX hY hI3 (Nat.blt_eq.mp hix)
  have h4 := ksCP_powIs_lrel hV hX hI4
  have h5 := ksCP_powIs_lrel hV hY hI5
  have h6 := ksCP_stepIs_lrel hV h3 h4 hI6 (ksCP_stepIs_spec hI3).2.1
  have h7 := ksCP_stepIs_lrel hV h6 h5 hI7 (ksCP_stepIs_spec hI6).2.1
  exact h7

private theorem ksCP_cub_zfacts {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {X Y Z : Array FV} (hc : c.ok = true) (hp : c.p = 3)
    (hV : Vals c V P N) (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1)))
    (hZ : LRel c Z (V (I 7)))
    (hq : cubPartsOK c V P N (O 0) (O 1) (O 2) I D.r D.oh D.a D.b D.c D.d D.k D.l D.μ D.t
      = true) :
    (ops3 c.d).vne ((ops3 c.d).vmul ((ops3 c.d).unit D.t) Z) ((ops3 c.d).unit D.t) = true ∧
      (ops3 c.d).eq ((ops3 c.d).mul Z X) ((ops3 c.d).mul X Z) = true ∧
      (ops3 c.d).eq ((ops3 c.d).mul Z Y) ((ops3 c.d).mul Y Z) = true := by
  obtain ⟨hix, hq⟩ := SecS.andT (SecS.andT hq).2
  obtain ⟨hiy, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨ht, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hI3, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hI6, hq⟩ := SecS.andT hq
  obtain ⟨hI7, hq⟩ := SecS.andT hq
  obtain ⟨hZt, hq⟩ := SecS.andT hq
  obtain ⟨hI8, hq⟩ := SecS.andT hq
  obtain ⟨hI9, hq⟩ := SecS.andT hq
  obtain ⟨hbeqX, hq⟩ := SecS.andT hq
  obtain ⟨hI10, hq⟩ := SecS.andT hq
  obtain ⟨hI11, hq⟩ := SecS.andT hq
  obtain ⟨hbeqY, -⟩ := SecS.andT hq
  have hI7N := (ksCP_stepIs_spec hI7).2.1
  have hI6N := (ksCP_stepIs_spec hI6).2.1
  have h8 := ksCP_stepIs_lrel hV hZ hX hI8 hI7N
  have h9 := ksCP_stepIs_lrel hV hX hZ hI9 (Nat.blt_eq.mp hix)
  have h10 := ksCP_stepIs_lrel hV hZ hY hI10 hI7N
  have h11 := ksCP_stepIs_lrel hV hY hZ hI11 (Nat.blt_eq.mp hiy)
  have hu := vrel_unit hc hp (Nat.blt_eq.mp ht)
  refine ⟨vne_of_vrel hc hp (vrel_vmul hc hp hu hZ) hu (ksCP_ne_of_notB hZt),
    eq_of_rel h8 h9 hbeqX, eq_of_rel h10 h11 hbeqY⟩

private noncomputable def ksCP_cub_tailZ (V P : Nat → Nat) (N : Nat)
    (D : CubData) (O I : Nat → Nat) : Bool :=
  andB (stepIs P N (I 26) (O 2) (I 7))
    (andB (powIs P N (I 7) (I 27) D.μ)
      (andB (stepIs P N (I 28) (I 27) (O 2))
        (Nat.beq (V (I 26)) (V (I 28)))))

private noncomputable def ksCP_cub_tailY (V P : Nat → Nat) (N : Nat)
    (D : CubData) (O I : Nat → Nat) : Bool :=
  andB (stepIs P N (I 19) (O 2) (O 1))
    (andB (powIs P N (O 0) (I 20) D.c)
      (andB (powIs P N (O 1) (I 21) D.d)
        (andB (powIs P N (I 7) (I 22) D.l)
          (andB (stepIs P N (I 23) (I 20) (I 21))
            (andB (stepIs P N (I 24) (I 23) (I 22))
              (andB (stepIs P N (I 25) (I 24) (O 2))
                (andB (Nat.beq (V (I 19)) (V (I 25)))
                  (ksCP_cub_tailZ V P N D O I))))))))

private noncomputable def ksCP_cub_tailX (V P : Nat → Nat) (N : Nat)
    (D : CubData) (O I : Nat → Nat) : Bool :=
  andB (stepIs P N (I 12) (O 2) (O 0))
    (andB (powIs P N (O 0) (I 13) D.a)
      (andB (powIs P N (O 1) (I 14) D.b)
        (andB (powIs P N (I 7) (I 15) D.k)
          (andB (stepIs P N (I 16) (I 13) (I 14))
            (andB (stepIs P N (I 17) (I 16) (I 15))
              (andB (stepIs P N (I 18) (I 17) (O 2))
                (andB (Nat.beq (V (I 12)) (V (I 18)))
                  (ksCP_cub_tailY V P N D O I))))))))

private theorem ksCP_cub_toX {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat}
    (hq : cubPartsOK c V P N (O 0) (O 1) (O 2) I D.r D.oh D.a D.b D.c D.d D.k D.l D.μ D.t
      = true) : ksCP_cub_tailX V P N D O I = true := by
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  exact hq

private theorem ksCP_cub_toY {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} (hq : ksCP_cub_tailX V P N D O I = true) :
    ksCP_cub_tailY V P N D O I = true := by
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  exact hq

private theorem ksCP_cub_toZ {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} (hq : ksCP_cub_tailY V P N D O I = true) :
    ksCP_cub_tailZ V P N D O I = true := by
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  exact hq

private theorem ksCP_cub_conjX {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {X Y H Z : Array FV} (hc : c.ok = true) (hp : c.p = 3)
    (hV : Vals c V P N) (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1)))
    (hH : LRel c H (V (O 2))) (hZ : LRel c Z (V (I 7)))
    (hq : ksCP_cub_tailX V P N D O I = true) (hih : O 2 < N) :
    (ops3 c.d).conjOK H X
      ((ops3 c.d).mul ((ops3 c.d).mul ((ops3 c.d).pow X D.a) ((ops3 c.d).pow Y D.b))
        ((ops3 c.d).pow Z D.k)) = true := by
  obtain ⟨hI12, hq⟩ := SecS.andT hq
  obtain ⟨hI13, hq⟩ := SecS.andT hq
  obtain ⟨hI14, hq⟩ := SecS.andT hq
  obtain ⟨hI15, hq⟩ := SecS.andT hq
  obtain ⟨hI16, hq⟩ := SecS.andT hq
  obtain ⟨hI17, hq⟩ := SecS.andT hq
  obtain ⟨hI18, hq⟩ := SecS.andT hq
  obtain ⟨hbeq, -⟩ := SecS.andT hq
  have h13 := ksCP_powIs_lrel hV hX hI13
  have h14 := ksCP_powIs_lrel hV hY hI14
  have h15 := ksCP_powIs_lrel hV hZ hI15
  have h16 := ksCP_stepIs_lrel hV h13 h14 hI16 (ksCP_powIs_spec hI13).1
  have h17 := ksCP_stepIs_lrel hV h16 h15 hI17 (ksCP_stepIs_spec hI16).2.1
  have h12 := ksCP_stepIs_lrel hV hH hX hI12 hih
  have h18 := ksCP_stepIs_lrel hV h17 hH hI18 (ksCP_stepIs_spec hI17).2.1
  have hk : Nat.beq (c.mul (V (O 2)) (V (O 0))) (c.mul (V (I 17)) (V (O 2))) = true := by
    have e12 := ksCP_stepIs_val hV.hN hV.step hI12 hih
    have e18 := ksCP_stepIs_val hV.hN hV.step hI18 (ksCP_stepIs_spec hI17).2.1
    rw [← e12, ← e18]
    exact hbeq
  exact conjOK_of hc hp hH hX h17 hk

private theorem ksCP_cub_conjY {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {X Y H Z : Array FV} (hc : c.ok = true) (hp : c.p = 3)
    (hV : Vals c V P N) (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1)))
    (hH : LRel c H (V (O 2))) (hZ : LRel c Z (V (I 7)))
    (hq : ksCP_cub_tailY V P N D O I = true) (hih : O 2 < N) :
    (ops3 c.d).conjOK H Y
      ((ops3 c.d).mul ((ops3 c.d).mul ((ops3 c.d).pow X D.c) ((ops3 c.d).pow Y D.d))
        ((ops3 c.d).pow Z D.l)) = true := by
  obtain ⟨hI19, hq⟩ := SecS.andT hq
  obtain ⟨hI20, hq⟩ := SecS.andT hq
  obtain ⟨hI21, hq⟩ := SecS.andT hq
  obtain ⟨hI22, hq⟩ := SecS.andT hq
  obtain ⟨hI23, hq⟩ := SecS.andT hq
  obtain ⟨hI24, hq⟩ := SecS.andT hq
  obtain ⟨hI25, hq⟩ := SecS.andT hq
  obtain ⟨hbeq, -⟩ := SecS.andT hq
  have h20 := ksCP_powIs_lrel hV hX hI20
  have h21 := ksCP_powIs_lrel hV hY hI21
  have h22 := ksCP_powIs_lrel hV hZ hI22
  have h23 := ksCP_stepIs_lrel hV h20 h21 hI23 (ksCP_powIs_spec hI20).1
  have h24 := ksCP_stepIs_lrel hV h23 h22 hI24 (ksCP_stepIs_spec hI23).2.1
  have h19 := ksCP_stepIs_lrel hV hH hY hI19 hih
  have h25 := ksCP_stepIs_lrel hV h24 hH hI25 (ksCP_stepIs_spec hI24).2.1
  have hk : Nat.beq (c.mul (V (O 2)) (V (O 1))) (c.mul (V (I 24)) (V (O 2))) = true := by
    have e19 := ksCP_stepIs_val hV.hN hV.step hI19 hih
    have e25 := ksCP_stepIs_val hV.hN hV.step hI25 (ksCP_stepIs_spec hI24).2.1
    rw [← e19, ← e25]
    exact hbeq
  exact conjOK_of hc hp hH hY h24 hk

private theorem ksCP_cub_conjZ {c : Lay} {V P : Nat → Nat} {N : Nat} {D : CubData}
    {O I : Nat → Nat} {H Z : Array FV} (hc : c.ok = true) (hp : c.p = 3)
    (hV : Vals c V P N) (hH : LRel c H (V (O 2))) (hZ : LRel c Z (V (I 7)))
    (hq : ksCP_cub_tailZ V P N D O I = true) (hih : O 2 < N) :
    (ops3 c.d).conjOK H Z ((ops3 c.d).pow Z D.μ) = true := by
  obtain ⟨hI26, hq⟩ := SecS.andT hq
  obtain ⟨hI27, hq⟩ := SecS.andT hq
  obtain ⟨hI28, hq⟩ := SecS.andT hq
  have hbeq := hq
  have h27 := ksCP_powIs_lrel hV hZ hI27
  have h26 := ksCP_stepIs_lrel hV hH hZ hI26 hih
  have h28 := ksCP_stepIs_lrel hV h27 hH hI28 (ksCP_powIs_spec hI27).1
  have hk : Nat.beq (c.mul (V (O 2)) (V (I 7))) (c.mul (V (I 27)) (V (O 2))) = true := by
    have e26 := ksCP_stepIs_val hV.hN hV.step hI26 hih
    have e28 := ksCP_stepIs_val hV.hN hV.step hI28 (ksCP_powIs_spec hI27).1
    rw [← e26, ← e28]
    exact hbeq
  exact conjOK_of hc hp hH hZ h27 hk

private theorem ksCP_appBaseK_three (c : Lay) (b x y z n v : Nat) :
    appBaseK c b [x, y, z] n v = digApp c b (sel3 x y z) 3 0 n v := by
  rw [ksCP_digApp_eq_appBaseK]
  rfl

private theorem ksCP_cub_normal {c : Lay} {V : Nat → Nat} {D : CubData}
    {O I U HI : Nat → Nat} {σ : List Nat} {NS CH : Nat} {X Y Z : Array FV}
    (hc : c.ok = true) (hp : c.p = 3)
    (hX : LRel c X (V (O 0))) (hY : LRel c Y (V (O 1))) (hZ : LRel c Z (V (I 7)))
    (hr0 : 0 < D.r) (h0 : vt0 c D.t U = true)
    (hv : ChunksTo (fun s => vtabK c D.r (sel3 (V (O 0)) (V (O 1)) (V (I 7))) 3 U HI
      (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow D.r 3) 1 ≤ Nat.mul NS CH)
    (hsort : sortRun (Nat.pow D.r 3) U σ 0 0 = true) :
    (ops3 c.d).normalFormOK D.r [X, Y, Z] D.t = true := by
  obtain ⟨ht0, hU0eq⟩ := SecS.andT h0
  have ht : D.t < c.d := Nat.blt_eq.mp ht0
  have hU0 : U 0 = c.unit D.t := Nat.eq_of_beq_eq_true hU0eq
  have hU := ksCP_U_digApp hr0 hv hNS hU0
  refine CFSG.KC.LocalComp.SqReplaySnd.normalFormOK_of_inj hc hp D.r
    (Xs := [X, Y, Z]) (xs := [V (O 0), V (O 1), V (I 7)]) ?_ ht ?_
  · exact List.Forall₂.cons hX (List.Forall₂.cons hY (List.Forall₂.cons hZ List.Forall₂.nil))
  · intro i hi j hj heq
    have hi' : i < Nat.pow D.r 3 := by simpa using hi
    have hj' : j < Nat.pow D.r 3 := by omega
    have hUij : U i = U j := by
      rw [hU i hi', hU j hj']
      rw [← ksCP_appBaseK_three c D.r (V (O 0)) (V (O 1)) (V (I 7)) i (c.unit D.t),
        ← ksCP_appBaseK_three c D.r (V (O 0)) (V (O 1)) (V (I 7)) j (c.unit D.t)]
      exact heq
    have hij := SecS.sortRun_inj hsort hi' hj' hUij
    omega

private theorem ksCP_not_beq_of_ne {a b : Nat} (h : a ≠ b) : (!Nat.beq a b) = true := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem ksCP_map_range_get {α β : Type} (l : List α) (f : α → β) (d : α) :
    l.map f = (List.range l.length).map (fun i => f (l.getD i d)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]

private theorem ksCP_commsModK_of {c : Lay} {T : Nat} {xs : List Nat}
    (h : ∀ i j, i < xs.length → i < j → j < xs.length →
      (Nat.beq (c.mul (xs.getD i 0) (xs.getD j 0))
          (c.mul (xs.getD j 0) (xs.getD i 0)) ||
        Nat.beq (c.mul (xs.getD i 0) (xs.getD j 0))
          (c.mul T (c.mul (xs.getD j 0) (xs.getD i 0)))) = true) :
    commsModK c T xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (xs.all (fun Y => Nat.beq (c.mul x Y) (c.mul Y x) ||
      Nat.beq (c.mul x Y) (c.mul T (c.mul Y x))) && commsModK c T xs) = true
    rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      have hh := h 0 (j + 1) (by simp) (by simp) (by simpa using hj)
      simpa [List.getD_eq_getElem, hj] using hh
    · apply ih
      intro i j hi hij hjl
      have hh := h (i + 1) (j + 1) (by simpa using hi) (by omega) (by simpa using hjl)
      simpa [List.getD_eq_getElem, hi, hjl] using hh

private theorem ksCP_orB_eq {a b : Bool} :
    CFSG.KC.Ord.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [CFSG.KC.Ord.orB]

private theorem ksCP_sec_hTT {c : Lay} {V P : Nat → Nat} {N : Nat} {O J : Nat → Nat}
    {r : Nat} (hV : Vals c V P N) (hq : secPartsOK c V P N O r J = true) :
    Nat.beq (c.mul (V (O r)) (V (O r))) c.ONE = true := by
  unfold secPartsOK at hq
  simp only [SecS.strictB_eq] at hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hiT, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hJ0, hq⟩ := SecS.andT hq
  obtain ⟨hV0, -⟩ := SecS.andT hq
  have e := ksCP_stepIs_val hV.hN hV.step hJ0 (Nat.blt_eq.mp hiT)
  rw [← e]
  exact hV0

private theorem ksCP_sec_hall {c : Lay} {V P : Nat → Nat} {N : Nat} {O J : Nat → Nat}
    {r : Nat} (hV : Vals c V P N) (hq : secPartsOK c V P N O r J = true) :
    ((List.range r).map fun i => V (O i)).all (fun X =>
      Nat.beq (c.mul X (V (O r))) (c.mul (V (O r)) X) &&
        (Nat.beq (c.mul X X) c.ONE || Nat.beq (c.mul X X) (V (O r)))) = true := by
  unfold secPartsOK at hq
  simp only [SecS.strictB_eq] at hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hiT, hq⟩ := SecS.andT hq
  obtain ⟨hallO, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hall, -⟩ := SecS.andT hq
  rw [List.all_map, List.all_eq_true]
  intro i hi
  simp only [Function.comp_apply]
  have hi' : i < r := List.mem_range.1 hi
  obtain ⟨h1, h⟩ := SecS.andT (SecS.allLt_spec hall i hi')
  obtain ⟨h2, h⟩ := SecS.andT h
  obtain ⟨hbeq, h⟩ := SecS.andT h
  obtain ⟨h3, hor⟩ := SecS.andT h
  have hOi : O i < N := Nat.blt_eq.mp (SecS.allLt_spec hallO i hi')
  have hiTN : O r < N := Nat.blt_eq.mp hiT
  have e1 := ksCP_stepIs_val hV.hN hV.step h1 hOi
  have e2 := ksCP_stepIs_val hV.hN hV.step h2 hiTN
  have e3 := ksCP_stepIs_val hV.hN hV.step h3 hOi
  have hbeq' := Nat.eq_of_beq_eq_true hbeq
  have hor' := (ksCP_orB_eq).1 hor
  rw [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨?_, ?_⟩
  · rw [← e1, ← e2, hbeq']
    exact Nat.beq_refl _
  · rcases hor' with hor' | hor'
    · left
      rw [← e3]
      exact hor'
    · right
      rw [← e3]
      exact hor'

private theorem ksCP_sec_hcomm {c : Lay} {V P : Nat → Nat} {N : Nat} {O J : Nat → Nat}
    {r : Nat} (hV : Vals c V P N) (hq : secPartsOK c V P N O r J = true) :
    commsModK c (V (O r)) ((List.range r).map fun i => V (O i)) = true := by
  unfold secPartsOK at hq
  simp only [SecS.strictB_eq] at hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨hiT, hq⟩ := SecS.andT hq
  obtain ⟨hallO, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  obtain ⟨-, hq⟩ := SecS.andT hq
  apply ksCP_commsModK_of
  intro i j hi hij hj
  have hi' : i < r := by simpa using hi
  have hj' : j < r := by simpa using hj
  have hbody := SecS.allLt_spec (SecS.allLt_spec hq i hi') j hj'
  rw [Nat.blt_eq.mpr hij] at hbody
  simp only at hbody
  obtain ⟨h1, hbody⟩ := SecS.andT hbody
  obtain ⟨h2, hbody⟩ := SecS.andT hbody
  obtain ⟨h3, hor⟩ := SecS.andT hbody
  have hOi : O i < N := Nat.blt_eq.mp (SecS.allLt_spec hallO i hi')
  have hOj : O j < N := Nat.blt_eq.mp (SecS.allLt_spec hallO j hj')
  have hiTN : O r < N := Nat.blt_eq.mp hiT
  have e1 := ksCP_stepIs_val hV.hN hV.step h1 hOi
  have e2 := ksCP_stepIs_val hV.hN hV.step h2 hOj
  have e3 := ksCP_stepIs_val hV.hN hV.step h3 hiTN
  have hxi : ((List.range r).map fun i => V (O i)).getD i 0 = V (O i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi')]
    simp
  have hxj : ((List.range r).map fun i => V (O i)).getD j 0 = V (O j) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj')]
    simp
  have hor' := (ksCP_orB_eq).1 hor
  rw [hxi, hxj, Bool.or_eq_true]
  rcases hor' with hor' | hor'
  · left
    rw [← e1, ← e2]
    exact hor'
  · right
    rw [← e1, ← e2, ← e3]
    exact hor'

private theorem ksCP_sec_hker {c : Lay} {V : Nat → Nat} {O : Nat → Nat}
    {r t NS CH : Nat} {U HI : Nat → Nat}
    (h0 : vt0 c t U = true)
    (hv : ChunksTo (fun s => vtabK c 2 (fun i => V (O i)) r U HI (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow 2 r) 1 ≤ Nat.mul NS CH)
    (hk : kmodK c U (V (O r)) t r = true) :
    (List.range (2 ^ r - 1)).all (fun n =>
      !Nat.beq (appBaseK c 2 ((List.range r).map fun i => V (O i)) (n + 1) (c.unit t))
        (c.unit t) &&
      !Nat.beq (appBaseK c 2 ((List.range r).map fun i => V (O i)) (n + 1) (c.unit t))
        (c.vec (c.unit t) (V (O r)))) = true := by
  unfold kmodK at hk
  simp only [SecS.strictB_eq] at hk
  have hU0 : U 0 = c.unit t := Nat.eq_of_beq_eq_true (SecS.andT h0).2
  have hU := ksCP_U_digApp (c := c) (b := 2) (X := fun i => V (O i)) (m := r)
    (U := U) (HI := HI) (NS := NS) (CH := CH) (v := c.unit t) (by norm_num) hv hNS hU0
  rw [List.all_eq_true]
  intro n hn
  have hn' : n < 2 ^ r - 1 := List.mem_range.1 hn
  have hkn := SecS.allLt_spec hk n hn'
  have hkn' : (andB (notB (Nat.beq (U (n + 1)) (c.unit t)))
      (notB (Nat.beq (U (n + 1)) (c.vec (c.unit t) (V (O r)))))) = true := by
    simpa using hkn
  obtain ⟨h1, h2⟩ := SecS.andT hkn'
  have hUn : U (n + 1) = appBaseK c 2 ((List.range r).map fun i => V (O i))
      (n + 1) (c.unit t) := by
    rw [hU (n + 1) (by omega), ksCP_digApp_eq_appBaseK]
    simp
  have hne1 : appBaseK c 2 ((List.range r).map fun i => V (O i))
      (n + 1) (c.unit t) ≠ c.unit t := by
    rw [← hUn]
    exact ksCP_ne_of_notB h1
  have hne2 : appBaseK c 2 ((List.range r).map fun i => V (O i))
      (n + 1) (c.unit t) ≠ c.vec (c.unit t) (V (O r)) := by
    rw [← hUn]
    exact ksCP_ne_of_notB h2
  rw [Bool.and_eq_true]
  exact ⟨ksCP_not_beq_of_ne hne1, ksCP_not_beq_of_ne hne2⟩

private theorem ksCP_kerModOK_of {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {T : Array FV} {tT tt : Nat} {Xs : List (Array FV)} {xs : List Nat} {tests : List Nat}
    (hT : LRel c T tT) (h : List.Forall₂ (LRel c) Xs xs) (ht : tt < c.d)
    (hmem : tt ∈ tests)
    (hk : ((List.range (2 ^ xs.length - 1)).all fun n =>
      !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit tt)) (c.unit tt) &&
      !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit tt)) (c.vec (c.unit tt) tT)) = true) :
    (ops3 c.d).kerModOK T Xs tests = true := by
  unfold Ops.kerModOK
  rw [Snd.forall₂_length h]
  rw [List.all_eq_true]
  intro n hn
  have hkn := List.all_eq_true.1 hk n hn
  rw [Bool.and_eq_true] at hkn
  simp only [Ops.outsideN, Bool.and_eq_true]
  have hu := Snd.vrel_unit hc hp ht
  constructor
  · refine List.any_eq_true.2 ⟨tt, hmem, ?_⟩
    exact Snd.vne_of_vrel hc hp (Snd.vrel_appBase hc hp 2 h (n + 1) hu) hu
      (Snd.ne_of_not_beq hkn.1)
  · refine List.any_eq_true.2 ⟨tt, hmem, ?_⟩
    exact Snd.vne_of_vrel hc hp (Snd.vrel_appBase hc hp 2 h (n + 1) hu)
      (Snd.vrel_vmul hc hp hu hT) (Snd.ne_of_not_beq hkn.2)

private theorem ksCP_sec_forall {c : Lay} {V P T O : Nat → Nat} {N : Nat} {D : SecData}
    {LA LB : List Char} {R2 : List Nat} {Rn : Array (Array FV)}
    (hc : c.ok = true) (hp : c.p = 3) (hsA : D.seedA = String.ofList LA)
    (hsB : D.seedB = String.ofList LB) (hA : decOK c (V 0) LA = true)
    (hB : decOK c (V 1) LB = true) (hV2 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hN : N ≤ 1048576)
    (hprog : D.prog.all (Op.lt D.nregs) = true)
    (hrep : (replayK c V P T N D.prog 0
      ((List.range D.nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)).1
      = true)
    (hR2 : R2 = (replayK c V P T N D.prog 0
      ((List.range D.nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)).2)
    (hRn : Rn = (ops3 c.d).regsOf D.seedA D.seedB D.nregs D.prog)
    (hOeq : ∀ i < D.outs.length, O i = R2.getD (D.outs.getD i 0) 0)
    (houts : ∀ reg ∈ D.outs, reg < D.nregs) :
    List.Forall₂ (LRel c) (D.outs.map fun reg => Rn[reg]!)
      ((List.range D.outs.length).map fun i => V (O i)) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i hi1 hi2
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  have hi : i < D.outs.length := by simpa using hi1
  have hreg : D.outs.getD i 0 < D.nregs := by
    rw [List.getD_eq_getElem _ _ hi]
    exact houts _ (List.getElem_mem hi)
  have hrel := CFSG.KC.LocalComp.SqReplaySnd.replay_rel hc hp hsA hsB hA hB hV2 hs hN
    hprog hrep hreg
  rw [← hRn, ← hR2] at hrel
  rw [← hOeq i hi] at hrel
  rw [List.getD_eq_getElem _ _ hi] at hrel
  exact hrel

private theorem ksCP_sec_ok {c : Lay} (hc : c.ok = true) (hp : c.p = 3)
    {T : Array FV} {tT tt : Nat} {Xs : List (Array FV)} {xs : List Nat}
    {tests : List Nat} (hT : LRel c T tT) (hfar : List.Forall₂ (LRel c) Xs xs)
    (ht : tt < c.d) (hmem : tt ∈ tests)
    (hTT : Nat.beq (c.mul tT tT) c.ONE = true)
    (hall : xs.all (fun X => Nat.beq (c.mul X tT) (c.mul tT X) &&
      (Nat.beq (c.mul X X) c.ONE || Nat.beq (c.mul X X) tT)) = true)
    (hcomm : commsModK c tT xs = true)
    (hker : ((List.range (2 ^ xs.length - 1)).all fun n =>
      !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit tt)) (c.unit tt) &&
      !Nat.beq (appBaseK c 2 xs (n + 1) (c.unit tt)) (c.vec (c.unit tt) tT)) = true) :
    (ops3 c.d).secOK T Xs tests = true := by
  have hallOK : Xs.all (fun X => (ops3 c.d).eq ((ops3 c.d).mul X T) ((ops3 c.d).mul T X) &&
      (ops3 c.d).inN T ((ops3 c.d).mul X X)) = true := by
    refine Snd.all_of_forall₂ (R := LRel c)
      (P := fun X => (ops3 c.d).eq ((ops3 c.d).mul X T) ((ops3 c.d).mul T X) &&
        (ops3 c.d).inN T ((ops3 c.d).mul X X))
      (p := fun x => Nat.beq (c.mul x tT) (c.mul tT x) &&
        (Nat.beq (c.mul x x) c.ONE || Nat.beq (c.mul x x) tT)) ?_ hfar hall
    intro X x hX hx
    rw [Bool.and_eq_true] at hx ⊢
    rw [Bool.or_eq_true] at hx
    refine ⟨Snd.eq_of_rel (Snd.rel_mul hc hp hX hT) (Snd.rel_mul hc hp hT hX) hx.1, ?_⟩
    rw [Ops.inN, Bool.or_eq_true]
    rcases hx.2 with h1 | h1
    · exact Or.inl (Snd.eq_of_rel (Snd.rel_mul hc hp hX hX) (Snd.rel_one hc hp) h1)
    · exact Or.inr (Snd.eq_of_rel (Snd.rel_mul hc hp hX hX) hT h1)
  have hTT' := Snd.eq_of_rel (Snd.rel_mul hc hp hT hT) (Snd.rel_one hc hp) hTT
  have hcommOK := Snd.commsModOK_of hc hp hT hfar hcomm
  have hkerOK := ksCP_kerModOK_of hc hp hT hfar ht hmem hker
  unfold Ops.secOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hTT', hallOK⟩, hcommOK⟩, hkerOK⟩

theorem cubicCheck_of_parts {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {V P T O I U HI : Nat → Nat} {N NS CH : Nat} {D : CubData}
    {σ : List Nat}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : replayOK c V P T N D.asData O (fun _ => D.t) = true)
    (hq : cubPartsOK c V P N (O 0) (O 1) (O 2) I D.r D.oh D.a D.b D.c D.d D.k D.l D.μ D.t = true)
    (h0 : vt0 c D.t U = true)
    (hv : ChunksTo (fun s => vtabK c D.r (sel3 (V (O 0)) (V (O 1)) (V (I 7))) 3 U HI
      (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow D.r 3) 1 ≤ Nat.mul NS CH)
    (hsort : sortRun (Nat.pow D.r 3) U σ 0 0 = true) :
    (ops3 d).cubicCheck D = true := by
  subst hd
  unfold replayOK at hr
  simp only [CubData.asData, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hN, h2⟩, hprog⟩, houts⟩, hrep⟩, hOut⟩, -⟩ := hr
  have hN' : N ≤ 1048576 := of_decide_eq_true hN
  have hlt : ∀ x ∈ [D.rx, D.ry, D.rh], x < D.nregs := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 houts x hx)
  have hO := List.all_eq_true.1 hOut
  have hO0 := Nat.eq_of_beq_eq_true (hO 0 (by simp))
  have hO1 := Nat.eq_of_beq_eq_true (hO 1 (by simp))
  have hO2 := Nat.eq_of_beq_eq_true (hO 2 (by simp))
  have hX := CFSG.KC.LocalComp.SqReplaySnd.replay_rel hc hp hsA hsB hA hB h1 hs hN'
    hprog hrep (hlt D.rx (by simp))
  have hY := CFSG.KC.LocalComp.SqReplaySnd.replay_rel hc hp hsA hsB hA hB h1 hs hN'
    hprog hrep (hlt D.ry (by simp))
  have hH := CFSG.KC.LocalComp.SqReplaySnd.replay_rel hc hp hsA hsB hA hB h1 hs hN'
    hprog hrep (hlt D.rh (by simp))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hO0 hO1 hO2
  rw [← hO0] at hX
  rw [← hO1] at hY
  rw [← hO2] at hH
  have hV : Vals c V P N := vals_of hc hp hN' hA hB h1 hs
  obtain ⟨-, hix, hiy, hih, hr0, hoh0, -, heqX, heqY, heqH⟩ :=
    ksCP_cub_pows hV hX hY hH hq
  have hZ := ksCP_cub_Z hV hX hY hq
  have hXZ := ksCP_cub_toX hq
  have hYZ := ksCP_cub_toY hXZ
  have hZZ := ksCP_cub_toZ hYZ
  obtain ⟨hZt, hZX, hZY⟩ := ksCP_cub_zfacts hc hp hV hX hY hZ hq
  have hCX := ksCP_cub_conjX hc hp hV hX hY hH hZ hXZ hih
  have hCY := ksCP_cub_conjY hc hp hV hX hY hH hZ hYZ hih
  have hCZ := ksCP_cub_conjZ hc hp hV hH hZ hZZ hih
  have hNF := ksCP_cub_normal hc hp hX hY hZ hr0 h0 hv hNS hsort
  unfold Ops.cubicCheck Ops.regsOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨of_decide_eq_true h2, hprog, hlt D.rx (by simp), hlt D.ry (by simp),
    hlt D.rh (by simp), hr0, hoh0, heqX, heqY, heqH, hZt, hZX, hZY, hCX, hCY, hCZ, hNF⟩
private theorem ksCP_sec_setup {c : Lay} {V P T O : Nat → Nat} {N : Nat} {D : SecData}
    {LA LB : List Char} {t r : Nat} (hc : c.ok = true) (hp : c.p = 3)
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hlen : D.outs.length = r)
    (hr : replayOK c V P T N D.asData O (fun _ => t) = true) :
    List.Forall₂ (LRel c)
        (D.outs.map fun reg => ((ops3 c.d).regsOf D.seedA D.seedB D.nregs D.prog)[reg]!)
        ((List.range r).map fun i => V (O i)) ∧
      LRel c ((ops3 c.d).regsOf D.seedA D.seedB D.nregs D.prog)[D.tReg]! (V (O r)) := by
  unfold replayOK at hr
  simp only [SecData.asData, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hN, -⟩, hprog⟩, houts⟩, hrep⟩, hOut⟩, -⟩ := hr
  have hN' : N ≤ 1048576 := of_decide_eq_true hN
  have hlt : ∀ x ∈ D.outs ++ [D.tReg], x < D.nregs := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 houts x hx)
  have hO := List.all_eq_true.1 hOut
  set R2 : List Nat := (replayK c V P T N D.prog 0
    ((List.range D.nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)).2
    with hR2
  set Rn' : Array (Array FV) :=
    (ops3 c.d).regsOf D.seedA D.seedB D.nregs D.prog with hRn
  have hOeq : ∀ i < D.outs.length, O i = R2.getD (D.outs.getD i 0) 0 := by
    intro i hi
    rw [hR2]
    have hi' : i < (D.outs ++ [D.tReg]).length := by simp [hlen]; omega
    have h := hO i (List.mem_range.2 hi')
    rw [List.getD_append D.outs [D.tReg] 0 i hi] at h
    exact Nat.eq_of_beq_eq_true h
  have hOT : O r = R2.getD D.tReg 0 := by
    rw [hR2]
    have hi' : r < (D.outs ++ [D.tReg]).length := by simp [hlen]
    have h := hO r (List.mem_range.2 hi')
    rw [List.getD_append_right D.outs [D.tReg] 0 r (by omega)] at h
    simpa [hlen] using h
  have hfar := ksCP_sec_forall hc hp hsA hsB hA hB h1 hs hN' hprog hrep hR2 hRn hOeq
    (fun reg hreg => hlt reg (List.mem_append_left _ hreg))
  have hfar' : List.Forall₂ (LRel c) (D.outs.map fun reg => Rn'[reg]!)
      ((List.range r).map fun i => V (O i)) := by
    simpa [hlen] using hfar
  have hTrel := CFSG.KC.LocalComp.SqReplaySnd.replay_rel hc hp hsA hsB hA hB h1 hs hN'
    hprog hrep (hlt D.tReg (by simp))
  have hT : LRel c Rn'[D.tReg]! (V (O r)) := by
    rw [← hRn, ← hR2, ← hOT] at hTrel
    exact hTrel
  refine ⟨?_, ?_⟩
  · simpa [hRn] using hfar'
  · simpa [hRn] using hT

theorem secCheck_of_parts {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {V P T O J U HI : Nat → Nat} {N NS CH r t : Nat} {D : SecData}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hlen : D.outs.length = r)
    (hr : replayOK c V P T N D.asData O (fun _ => t) = true)
    (hq : secPartsOK c V P N O r J = true)
    (h0 : vt0 c t U = true)
    (hv : ChunksTo (fun s => vtabK c 2 (fun i => V (O i)) r U HI (Nat.mul CH s) CH) NS)
    (hNS : Nat.sub (Nat.pow 2 r) 1 ≤ Nat.mul NS CH)
    (hk : kmodK c U (V (O r)) t r = true) :
    (ops3 d).secCheck D = true := by
  subst hd
  have hr' := hr
  unfold replayOK at hr
  simp only [SecData.asData, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hN, h2⟩, hprog⟩, houts⟩, -⟩, -⟩, hTests⟩ := hr
  have hN' : N ≤ 1048576 := of_decide_eq_true hN
  have hV : Vals c V P N := vals_of hc hp hN' hA hB h1 hs
  have ht : t < c.d := Nat.blt_eq.mp (SecS.andT h0).1
  have htest : t ∈ D.tests := by
    have hn0 : 0 < 3 ^ (D.outs ++ [D.tReg]).length - 1 := by simp [hlen]
    have h := List.all_eq_true.1 hTests 0 (List.mem_range.2 hn0)
    exact List.mem_of_elem_eq_true h
  obtain ⟨hfar', hT⟩ := ksCP_sec_setup hc hp hsA hsB hA hB h1 hs hlen hr'
  have hsec := ksCP_sec_ok hc hp hT hfar' ht htest (ksCP_sec_hTT hV hq)
    (ksCP_sec_hall hV hq) (ksCP_sec_hcomm hV hq)
    (by simpa using ksCP_sec_hker h0 hv hNS hk)
  have houtsD : D.outs.all (decide <| · < D.nregs) = true := by
    rw [List.all_eq_true]
    intro x hx
    exact List.all_eq_true.1 houts x (List.mem_append_left _ hx)
  have hTregLt : D.tReg < D.nregs :=
    of_decide_eq_true (List.all_eq_true.1 houts D.tReg (by simp))
  unfold Ops.secCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨of_decide_eq_true h2, hprog, houtsD, hTregLt, hsec⟩

end CFSG.KC.LocalComp.CubParts

end
