module

public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Certificates.Kernel.BabyMonster.Native.Dyadic
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.BenesW

open CFSG.KC.Benes CFSG.KC.MonsterConv.Perm

@[expose] def fw (W x f : Nat) : Nat := x / 2 ^ (W * f) % 2 ^ W

theorem testBit_fw (W x f i : Nat) :
    (fw W x f).testBit i = (decide (i < W) && x.testBit (W * f + i)) := by
  unfold fw
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]

@[expose] def Aligned (W M : Nat) : Prop := ∀ f i, i < W → M.testBit (W * f + i) = M.testBit (W * f)

@[expose] def tauW (W d M f : Nat) : Nat :=
  if M.testBit (W * f) = true then f + d
  else if d ≤ f ∧ M.testBit (W * (f - d)) = true then f - d else f

theorem mul_sub' (W f d : Nat) : W * f - W * d = W * (f - d) := (Nat.mul_sub W f d).symm

theorem swp_aligned {W d M : Nat} (hal : Aligned W M) (f : Nat) {i : Nat} (hi : i < W) :
    swp (W * d) M (W * f + i) = W * tauW W d M f + i := by
  have hA := hal f i hi
  unfold swp tauW
  rw [hA]
  by_cases h1 : M.testBit (W * f) = true
  · rw [if_pos h1, if_pos h1, Nat.mul_add]
    omega
  · rw [if_neg h1, if_neg h1]
    by_cases hd : d ≤ f
    · have hle : W * d ≤ W * f := Nat.mul_le_mul_left W hd
      have e : W * f + i - W * d = W * (f - d) + i := by
        rw [← mul_sub']
        omega
      rw [e, hal (f - d) i hi]
      by_cases h3 : M.testBit (W * (f - d)) = true
      · rw [if_pos ⟨by omega, h3⟩, if_pos ⟨hd, h3⟩]
      · rw [if_neg (fun h => h3 h.2), if_neg (fun h => h3 h.2)]
    · have hlt : W * f + i < W * d := by
        have : W * (f + 1) ≤ W * d := Nat.mul_le_mul_left W (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => hd h.1)]

theorem fw_dsw {W S d M : Nat} (hal : Aligned W M) (hv : ValidIn S (W * d) M) (x f : Nat) :
    fw W (dsw (W * d) M x) f = fw W x (tauW W d M f) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fw, testBit_fw]
  by_cases hi : i < W
  · rw [testBit_dsw (validIn_disj hv), swp_aligned hal f hi]
  · simp [hi]

theorem tauW_tauW {W S d M : Nat} (hW : 0 < W) (hal : Aligned W M) (hv : ValidIn S (W * d) M)
    (f : Nat) : tauW W d M (tauW W d M f) = f := by
  have h := swp_swp (validIn_disj hv) (W * f)
  have e1 := swp_aligned (d := d) hal f (i := 0) hW
  have e2 := swp_aligned (d := d) hal (tauW W d M f) (i := 0) hW
  simp only [Nat.add_zero] at e1 e2
  rw [e1, e2] at h
  exact Nat.eq_of_mul_eq_mul_left hW h

theorem tauW_lt {W d M S n : Nat} (hS : S = W * n) (hv : ValidIn S (W * d) M) {f : Nat}
    (hf : f < n) : tauW W d M f < n := by
  unfold tauW
  split
  · rename_i h
    have h1 := (hv _ h).1
    rw [hS, ← Nat.mul_add] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  · split <;> omega

theorem tauW_hi {W d M S n : Nat} (hS : S = W * n) (hv : ValidIn S (W * d) M) {f : Nat}
    (hf : n ≤ f) : tauW W d M f = f := by
  have hWf : W * n ≤ W * f := Nat.mul_le_mul_left W hf
  unfold tauW
  split
  · rename_i h
    have h1 := (hv _ h).1
    rw [hS] at h1
    have : W * f ≤ W * f + W * d := Nat.le_add_right _ _
    omega
  · split
    · rename_i h
      obtain ⟨hd, h3⟩ := h
      have h1 := (hv _ h3).1
      rw [hS, ← Nat.mul_add, Nat.sub_add_cancel hd] at h1
      omega
    · rfl

@[expose] def NetV (W S : Nat) : List Nat → List Nat → Prop
  | M :: Ms, D :: Ds => Aligned W M ∧ (∃ d, D = W * d) ∧ ValidIn S D M ∧ NetV W S Ms Ds
  | _, _ => True

theorem forceB_eq (v : Nat) (k : Nat → Nat) : CFSG.KC.BM.forceB v k = k v := by
  unfold CFSG.KC.BM.forceB
  cases Nat.beq v 0 <;> rfl

theorem benes_cons (M D : Nat) (Ms Ds : List Nat) (x : Nat) :
    CFSG.KC.BM.benes (M :: Ms) (D :: Ds) x = CFSG.KC.BM.benes Ms Ds (dsw D M x) := by
  change CFSG.KC.BM.forceB (Nat.land (Nat.xor (Nat.shiftRight x D) x) M) (fun t =>
    CFSG.KC.BM.forceB (Nat.xor x (Nat.xor t (Nat.shiftLeft t D)))
      (fun x' => CFSG.KC.BM.benes Ms Ds x')) = _
  simp only [forceB_eq]
  rfl

theorem benes_fw {W S n : Nat} (hW : 0 < W) (hS : S = W * n) : ∀ (Ms Ds : List Nat),
    NetV W S Ms Ds → ∃ P : Nat → Nat, (∀ x f, fw W (CFSG.KC.BM.benes Ms Ds x) f = fw W x (P f)) ∧
      (∀ f, f < n → P f < n) ∧ (∀ f, n ≤ f → P f = f)
  | [], _, _ => ⟨id, fun _ _ => rfl, fun _ h => h, fun _ _ => rfl⟩
  | _ :: _, [], _ => ⟨id, fun _ _ => rfl, fun _ h => h, fun _ _ => rfl⟩
  | M :: Ms, D :: Ds, h => by
    obtain ⟨hM, ⟨d, hd⟩, hv, hst⟩ :
      Aligned W M ∧ (∃ d, D = W * d) ∧ ValidIn S D M ∧ NetV W S Ms Ds := h
    subst hd
    obtain ⟨P, hP, h3, h4⟩ := benes_fw hW hS Ms Ds hst
    refine ⟨fun f => tauW W d M (P f), fun x f => ?_, fun f hf => tauW_lt hS hv (h3 f hf),
      fun f hf => ?_⟩
    · rw [benes_cons, hP, fw_dsw hM hv]
    · simp only
      rw [h4 f hf, tauW_hi hS hv hf]

@[expose] noncomputable def dbl (a x : Nat) : Nat := Nat.lor x (Nat.shiftLeft x a)

@[expose] noncomputable def wid (c : Nat) : Nat :=
  (fun x2 => Nat.lor (dbl (nat_lit 8) (dbl (nat_lit 4) (dbl (nat_lit 2) x2)))
    (Nat.shiftLeft x2 (nat_lit 16))) (dbl (nat_lit 1) c)

@[expose] def Spr (c a y : Nat) : Prop :=
  ∀ q, y.testBit q = true ↔ ∃ j, j < a ∧ j ≤ q ∧ c.testBit (q - j) = true

theorem spr_one (c : Nat) : Spr c 1 c := fun q => by
  constructor
  · intro h
    exact ⟨0, by omega, by omega, by rwa [Nat.sub_zero]⟩
  · rintro ⟨j, hj, -, h⟩
    obtain rfl : j = 0 := by omega
    rwa [Nat.sub_zero] at h

theorem testBit_shl' (x a q : Nat) :
    (Nat.shiftLeft x a).testBit q = (decide (a ≤ q) && x.testBit (q - a)) := by
  rw [show Nat.shiftLeft x a = x <<< a from rfl, Nat.testBit_shiftLeft]

theorem spr_or {c a b y z : Nat} (hy : Spr c a y) (hz : Spr c b z) :
    Spr c (a + b) (Nat.lor y (Nat.shiftLeft z a)) := fun q => by
  rw [show Nat.lor y (Nat.shiftLeft z a) = y ||| Nat.shiftLeft z a from rfl, Nat.testBit_or,
    testBit_shl', Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, hy q]
  constructor
  · rintro (⟨j, hj, hq, h⟩ | ⟨ha, h⟩)
    · exact ⟨j, by omega, hq, h⟩
    · obtain ⟨j, hj, hq, h⟩ := (hz _).1 h
      exact ⟨j + a, by omega, by omega, by rwa [show q - (j + a) = q - a - j by omega]⟩
  · rintro ⟨j, hj, hq, h⟩
    by_cases hja : j < a
    · exact Or.inl ⟨j, hja, hq, h⟩
    · refine Or.inr ⟨by omega, (hz _).2 ⟨j - a, by omega, by omega, ?_⟩⟩
      rwa [show q - a - (j - a) = q - j by omega]

theorem spr_wid (c : Nat) : Spr c 18 (wid c) := by
  have h2 : Spr c 2 (dbl 1 c) := spr_or (spr_one c) (spr_one c)
  have h4 : Spr c 4 (dbl 2 (dbl 1 c)) := spr_or h2 h2
  have h8 : Spr c 8 (dbl 4 (dbl 2 (dbl 1 c))) := spr_or h4 h4
  have h16 : Spr c 16 (dbl 8 (dbl 4 (dbl 2 (dbl 1 c)))) := spr_or h8 h8
  exact spr_or h16 h2

theorem aligned_wid {c : Nat} (hc : ∀ q, c.testBit q = true → q % 18 = 0) : Aligned 18 (wid c) := by
  intro f i hi
  have key : ∀ i, i < 18 → ((wid c).testBit (18 * f + i) = true ↔ c.testBit (18 * f) = true) := by
    intro i hi
    rw [spr_wid c (18 * f + i)]
    constructor
    · rintro ⟨j, hj, hq, h⟩
      have := hc _ h
      obtain rfl : j = i := by omega
      rwa [show 18 * f + j - j = 18 * f by omega] at h
    · intro h
      exact ⟨i, hi, by omega, by rwa [show 18 * f + i - i = 18 * f by omega]⟩
  have k0 := key 0 (by decide)
  rw [Nat.add_zero] at k0
  have ki := key i hi
  rw [Bool.eq_iff_iff, ki, k0]

@[expose] noncomputable def forceL (L : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun a _ ih k => Nat.rec (motive := fun _ => Bool) (ih fun r => k (List.cons (nat_lit 0) r))
      (fun n _ => ih fun r => k (List.cons (Nat.succ n) r)) a) L k

theorem forceL_eq : ∀ (L : List Nat) (k : List Nat → Bool), forceL L k = k L
  | [], _ => rfl
  | a :: L, k => by
    change Nat.rec (motive := fun _ => Bool) (forceL L fun r => k (List.cons 0 r))
      (fun n _ => forceL L fun r => k (List.cons (Nat.succ n) r)) a = _
    simp only [forceL_eq L]
    cases a <;> rfl

@[expose] noncomputable def forceN (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem forceN_eq (y : Nat) (k : Nat → Bool) : forceN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def wordG (net : Nat → List Nat) (Ds : List Nat) (Wd L x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => CFSG.KC.Loop.strictN
      (CFSG.KC.BM.benes (net (Nat.land (Nat.shiftRight Wd (Nat.mul 4 i)) 15)) Ds x) fun y => ih y)
    L x

@[expose] def traceG (G : Nat → Nat → Nat) (Wd : Nat) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | L + 1, k, v => traceG G Wd L (k + 1) (G ((Wd >>> (4 * k)) &&& 15) v)

theorem traceG_snoc (G : Nat → Nat → Nat) (Wd : Nat) : ∀ L k v,
    traceG G Wd (L + 1) k v = G ((Wd >>> (4 * (k + L))) &&& 15) (traceG G Wd L k v)
  | 0, k, v => rfl
  | L + 1, k, v => by
    rw [traceG, traceG_snoc G Wd L (k + 1), traceG, show k + 1 + L = k + (L + 1) by omega]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem wordG_fw {W m : Nat} {net : Nat → List Nat} {Ds : List Nat} {G : Nat → Nat → Nat}
    (hG : ∀ c < 16, ∀ x, ∀ f < m, fw W (CFSG.KC.BM.benes (net c) Ds x) f = fw W x (G c f))
    (hm : ∀ c < 16, ∀ f < m, G c f < m) (Wd : Nat) : ∀ L x f, f < m →
      fw W (wordG net Ds Wd L x) f = fw W x (traceG G Wd L 0 f) ∧ traceG G Wd L 0 f < m
  | 0, x, f, hf => ⟨rfl, hf⟩
  | L + 1, x, f, hf => by
    have hc : (Wd >>> (4 * L)) &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have e : wordG net Ds Wd (L + 1) x =
        wordG net Ds Wd L (CFSG.KC.BM.benes (net ((Wd >>> (4 * L)) &&& 15)) Ds x) := by
      change CFSG.KC.Loop.strictN _ (fun y => wordG net Ds Wd L y) = _
      rw [strictN_eq]
      rfl
    obtain ⟨h1, h2⟩ := wordG_fw hG hm Wd L
      (CFSG.KC.BM.benes (net ((Wd >>> (4 * L)) &&& 15)) Ds x) f hf
    rw [e, h1, hG _ hc x _ h2, traceG_snoc, Nat.zero_add]
    exact ⟨rfl, hm _ hc _ h2⟩

end CFSG.KC.BenesW

end
