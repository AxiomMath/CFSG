module

public import Certificates.Data.Kernel.U34Orb
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LieType.SeitzGeneration.HeisSmallCheck
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.U34Orb

open Certificates.U34Orb CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall MulAction

abbrev T3 := GF16 × GF16 × GF16

@[expose] def eV (v : T3) : V := (v.1.toNat, v.2.1.toNat, v.2.2.toNat)

@[expose] def eM (A : M3 GF16) : List Nat :=
  [A.a00.toNat, A.a01.toNat, A.a02.toNat, A.a10.toNat, A.a11.toNat, A.a12.toNat, A.a20.toNat,
    A.a21.toNat, A.a22.toNat]

@[expose] def dK (k : Nat) : T3 :=
  (GF16.ofNat' (k / 256 % 16), GF16.ofNat' (k / 16 % 16), GF16.ofNat' (k % 16))

@[expose] def mvG (A : M3 GF16) (v : T3) : T3 :=
  (A.a00 * v.1 + A.a01 * v.2.1 + A.a02 * v.2.2, A.a10 * v.1 + A.a11 * v.2.1 + A.a12 * v.2.2,
    A.a20 * v.1 + A.a21 * v.2.1 + A.a22 * v.2.2)

@[expose] def scG (c : GF16) (v : T3) : T3 := (c * v.1, c * v.2.1, c * v.2.2)

@[expose] def lead (v : T3) : GF16 :=
  if v.1.toNat != 0 then v.1 else if v.2.1.toNat != 0 then v.2.1 else v.2.2

@[expose] def nzG (v : T3) : T3 := scG (lead v)⁻¹ v

abbrev N := {v : T3 // nzG v = v}

theorem toNat_lt (x : GF16) : x.toNat < 16 := x.val.isLt

theorem ofNat'_toNat : ∀ x : GF16, GF16.ofNat' x.toNat = x := by decide +kernel

theorem toNat_inj {x y : GF16} (h : x.toNat = y.toNat) : x = y := by
  rw [← ofNat'_toNat x, h, ofNat'_toNat y]

theorem toNat_ofNat' (a : Nat) : (GF16.ofNat' a).toNat = a % 16 := rfl

theorem gm_toNat : ∀ x y : GF16, gm x.toNat y.toNat = (x * y).toNat := by decide +kernel

theorem xor_toNat : ∀ x y : GF16, x.toNat ^^^ y.toNat = (x + y).toNat := by decide +kernel

theorem ginv_toNat : ∀ x : GF16, ginv x.toNat = x⁻¹.toNat := by decide +kernel

theorem bne_iff : ∀ x : GF16, (x.toNat != 0) = true ↔ x ≠ 0 := by decide +kernel

theorem bne_mul : ∀ c x : GF16, c ≠ 0 → ((c * x).toNat != 0) = (x.toNat != 0) := by
  decide +kernel

theorem bne_mul' {c : GF16} (hc : c ≠ 0) (x : GF16) :
    ((c * x).toNat != 0) = (x.toNat != 0) :=
  bne_mul c x hc

theorem mv_eM (A : M3 GF16) (v : T3) : mv (eM A) (eV v) = eV (mvG A v) := by
  simp only [mv, eM, eV, mvG, gm_toNat, xor_toNat]

theorem mm_eM (A B : M3 GF16) : mm (eM A) (eM B) = eM (A * B) := by
  simp only [mm, eM, M3.mul_def, gm_toNat, xor_toNat]

theorem eM_one : eM 1 = mI := rfl

theorem sc_eV (c : GF16) (v : T3) : sc (ginv c.toNat) (eV v) = eV (scG c⁻¹ v) := by
  simp only [sc, eV, scG, ginv_toNat, gm_toNat]

theorem nz_eV (v : T3) : nz (eV v) = eV (nzG v) := by
  obtain ⟨x, y, z⟩ := v
  change (if x.toNat != 0 then sc (ginv x.toNat) (eV (x, y, z))
      else if y.toNat != 0 then sc (ginv y.toNat) (eV (x, y, z))
      else sc (ginv z.toNat) (eV (x, y, z))) =
    eV (scG (if x.toNat != 0 then x else if y.toNat != 0 then y else z)⁻¹ (x, y, z))
  split_ifs <;> exact sc_eV _ _

theorem eV_inj {v w : T3} (h : eV v = eV w) : v = w := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := w
  simp only [eV, Prod.mk.injEq] at h
  rw [toNat_inj h.1, toNat_inj h.2.1, toNat_inj h.2.2]

theorem eM_inj {A B : M3 GF16} (h : eM A = eM B) : A = B := by
  simp only [eM, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact M3.ext (toNat_inj h1) (toNat_inj h2) (toNat_inj h3) (toNat_inj h4) (toNat_inj h5)
    (toNat_inj h6) (toNat_inj h7) (toNat_inj h8) (toNat_inj h9)

theorem ofKey_key (v : T3) : ofKey (key (eV v)) = eV v := by
  have h1 := toNat_lt v.1
  have h2 := toNat_lt v.2.1
  have h3 := toNat_lt v.2.2
  simp only [ofKey, key, eV, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem key_ofKey {r : Nat} (h : r < 4096) : key (ofKey r) = r := by
  simp only [key, ofKey]
  omega

theorem ofKey_eq (r : Nat) : ofKey r = eV (dK r) := by
  simp only [ofKey, eV, dK, toNat_ofNat', Nat.mod_mod]

theorem exists_eM {M : List Nat} (h : mOK M = true) : ∃ A : M3 GF16, M = eM A := by
  simp only [mOK, Bool.and_eq_true] at h
  obtain ⟨hl, ha⟩ := h
  have hl := Nat.eq_of_beq_eq_true hl
  rcases M with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h', _ | ⟨i, _ |
    ⟨j, M⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> try omega
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq, and_true] at ha
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩ := ha
  refine ⟨⟨.ofNat' a, .ofNat' b, .ofNat' c, .ofNat' d, .ofNat' e, .ofNat' f, .ofNat' g,
    .ofNat' h', .ofNat' i⟩, ?_⟩
  simp only [eM, toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hg,
    Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hi]

theorem lbeq_eq : ∀ (l m : List Nat), lbeq l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [lbeq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, lbeq_eq l m h.2]
  | [], _ :: _, h => by simp [lbeq] at h
  | _ :: _, [], h => by simp [lbeq] at h

theorem lbeq_refl : ∀ l : List Nat, lbeq l l = true
  | [] => rfl
  | a :: l => by simp only [lbeq, Nat.beq_refl, lbeq_refl l, Bool.and_self]

theorem vbeq_eq {v w : V} (h : vbeq v w = true) : v = w := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := w
  simp only [vbeq, Bool.and_eq_true] at h
  rw [Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2]

theorem mem_iff (k : Nat) : ∀ l : List Nat, mem k l = true ↔ k ∈ l
  | [] => by simp [mem]
  | a :: l => by
    rw [mem, Bool.or_eq_true, mem_iff k l, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · subst h
        exact Or.inl (Nat.beq_refl k)
      · exact Or.inr h

theorem lget_cases {α : Type} (d : α) : ∀ (L : List α) (n : Nat), lget d L n ∈ L ∨ lget d L n = d
  | [], _ => Or.inr rfl
  | a :: _, 0 => Or.inl (List.mem_cons.2 (Or.inl rfl))
  | _ :: l, n + 1 => by
    rcases lget_cases d l n with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem m3_mul_assoc (A B C : M3 GF16) : A * B * C = A * (B * C) := by
  simp only [M3.mul_def, M3.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem m3_one_def : (1 : M3 GF16) = ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ := rfl

theorem m3_one_mul (A : M3 GF16) : 1 * A = A := by
  rw [m3_one_def, M3.mul_def]
  cases A
  simp

theorem m3_mul_one (A : M3 GF16) : A * 1 = A := by
  rw [m3_one_def, M3.mul_def]
  cases A
  simp

theorem mvG_mul (A B : M3 GF16) (v : T3) : mvG (A * B) v = mvG A (mvG B v) := by
  obtain ⟨x, y, z⟩ := v
  simp only [mvG, M3.mul_def, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem mvG_one (v : T3) : mvG 1 v = v := by
  obtain ⟨x, y, z⟩ := v
  rw [m3_one_def]
  simp [mvG]

theorem mvG_sc (A : M3 GF16) (c : GF16) (v : T3) : mvG A (scG c v) = scG c (mvG A v) := by
  obtain ⟨x, y, z⟩ := v
  simp only [mvG, scG, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem scG_scG (a b : GF16) (v : T3) : scG a (scG b v) = scG (a * b) v := by
  simp only [scG, mul_assoc]

theorem lead_sc {c : GF16} (hc : c ≠ 0) (v : T3) : lead (scG c v) = c * lead v := by
  obtain ⟨x, y, z⟩ := v
  simp only [lead, scG, bne_mul' hc]
  split_ifs <;> rfl

theorem nzG_sc {c : GF16} (hc : c ≠ 0) (v : T3) : nzG (scG c v) = nzG v := by
  unfold nzG
  rw [lead_sc hc, scG_scG, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem eq_zero_of_lead {v : T3} (h : lead v = 0) : v = (0, 0, 0) := by
  obtain ⟨x, y, z⟩ := v
  simp only [lead] at h
  split_ifs at h with h1 h2
  · exact absurd h ((bne_iff x).1 h1)
  · exact absurd h ((bne_iff y).1 h2)
  · have hx : x = 0 := by
      by_contra hx
      exact h1 ((bne_iff x).2 hx)
    have hy : y = 0 := by
      by_contra hy
      exact h2 ((bne_iff y).2 hy)
    rw [hx, hy, h]

theorem nzG_eq (v : T3) : ∃ c : GF16, c ≠ 0 ∧ nzG v = scG c v := by
  by_cases hl : lead v = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [eq_zero_of_lead hl]
    simp [nzG, scG]
  · exact ⟨(lead v)⁻¹, inv_ne_zero hl, rfl⟩

theorem nzG_nzG (v : T3) : nzG (nzG v) = nzG v := by
  obtain ⟨c, hc, e⟩ := nzG_eq v
  rw [e, nzG_sc hc]
  exact e

theorem nzG_mvG_nzG (A : M3 GF16) (w : T3) : nzG (mvG A (nzG w)) = nzG (mvG A w) := by
  obtain ⟨c, hc, e⟩ := nzG_eq w
  rw [e, mvG_sc, nzG_sc hc]

section Act

variable {G : Type*} [Group G]

@[reducible] def mulActionOf (ρ : G → M3 GF16) (h1 : ρ 1 = 1)
    (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) : MulAction G N where
  smul g x := ⟨nzG (mvG (ρ g) x.1), nzG_nzG _⟩
  one_smul x := Subtype.ext (by
    change nzG (mvG (ρ 1) x.1) = x.1
    rw [h1, mvG_one, x.2])
  mul_smul a b x := Subtype.ext (by
    change nzG (mvG (ρ (a * b)) x.1) = nzG (mvG (ρ a) (nzG (mvG (ρ b) x.1)))
    rw [hm, mvG_mul, nzG_mvG_nzG])

variable (ρ : G → M3 GF16) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b)

include h1 hm in
theorem wprod_sound (H : Subgroup G) (L : List (List Nat))
    (hL : ∀ l, ∃ g ∈ H, lget mI L l = eM (ρ g)) : ∀ w, ∃ g ∈ H, wprod L w = eM (ρ g)
  | [] => ⟨1, H.one_mem, by rw [h1]; rfl⟩
  | l :: w => by
    obtain ⟨a, ha, hA⟩ := hL l
    obtain ⟨b, hb, hB⟩ := wprod_sound H L hL w
    exact ⟨a * b, H.mul_mem ha hb, by rw [wprod, hA, hB, mm_eM, hm]⟩

include h1 hm in
theorem inv_eq (x : G) (D : M3 GF16) (h : ρ x * D = 1) : ρ x⁻¹ = D := by
  calc ρ x⁻¹ = ρ x⁻¹ * (ρ x * D) := by rw [h, m3_mul_one]
    _ = ρ x⁻¹ * ρ x * D := (m3_mul_assoc _ _ _).symm
    _ = D := by rw [← hm, inv_mul_cancel, h1, m3_one_mul]

include h1 hm in
theorem letters_sound (H : Subgroup G) (L : List (List Nat)) (a b : G) (ha : a ∈ H) (hb : b ∈ H)
    (hL0 : lget mI L 0 = eM (ρ a)) (hL1 : lget mI L 1 = eM (ρ b)) (h : lettersOK L = true) :
    ∀ l, ∃ g ∈ H, lget mI L l = eM (ρ g) := by
  simp only [lettersOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlen, hall⟩, hc⟩, hd⟩ := h
  have hlen := Nat.eq_of_beq_eq_true hlen
  rcases L with _ | ⟨A, _ | ⟨B, _ | ⟨C, _ | ⟨D, _ | ⟨E, L⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  have hA : A = eM (ρ a) := hL0
  have hB : B = eM (ρ b) := hL1
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hall
  obtain ⟨C', rfl⟩ := exists_eM hall.2.2.1
  obtain ⟨D', rfl⟩ := exists_eM hall.2.2.2
  have hc : ρ a * C' = 1 := by
    have := lbeq_eq _ _ hc
    change mm A (eM C') = mI at this
    rw [hA, mm_eM, ← eM_one] at this
    exact eM_inj this
  have hd : ρ b * D' = 1 := by
    have := lbeq_eq _ _ hd
    change mm B (eM D') = mI at this
    rw [hB, mm_eM, ← eM_one] at this
    exact eM_inj this
  intro l
  rcases l with _ | _ | _ | _ | l
  · exact ⟨a, ha, hL0⟩
  · exact ⟨b, hb, hL1⟩
  · exact ⟨a⁻¹, H.inv_mem ha, by rw [inv_eq ρ h1 hm a C' hc]; rfl⟩
  · exact ⟨b⁻¹, H.inv_mem hb, by rw [inv_eq ρ h1 hm b D' hd]; rfl⟩
  · exact ⟨1, H.one_mem, by rw [h1]; rfl⟩

variable [MulAction G N] (hsmul : ∀ (g : G) (x : N), (g • x).1 = nzG (mvG (ρ g) x.1))

include hsmul in
theorem act_eM (g : G) (x : N) : act (eM (ρ g)) (eV x.1) = eV (g • x).1 := by
  rw [act, mv_eM, nz_eV, hsmul]

include hsmul in
theorem treeAux_sound (S : Subgroup G) (p : N) (Ms : List (List Nat))
    (hMs : ∀ l, ∃ g ∈ S, lget mI Ms l = eM (ρ g)) (n : Nat) :
    ∀ (T : List (Nat × Nat × Nat)) (seen : List Nat), seen.Nodup →
      (∀ k ∈ seen, ∃ x ∈ orbit S p, key (eV x.1) = k) → treeAux Ms n seen T = true →
      ∃ s : List Nat, s.Nodup ∧ s.length = n ∧ ∀ k ∈ s, ∃ x ∈ orbit S p, key (eV x.1) = k
  | [], seen, hnd, hs, h => ⟨seen, hnd, Nat.eq_of_beq_eq_true h, hs⟩
  | (l, k, k') :: T, seen, hnd, hs, h => by
    simp only [treeAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hk, hk'⟩, hkey⟩, hT⟩ := h
    rw [mem_iff] at hk
    have hk'' : k' ∉ seen := fun hc => by
      rw [(mem_iff k' seen).2 hc] at hk'
      cases hk'
    obtain ⟨x, hx, rfl⟩ := hs k hk
    obtain ⟨g, hg, hgM⟩ := hMs l
    have hkey' : k' = key (eV (g • x).1) := by
      rw [Nat.eq_of_beq_eq_true hkey, hgM, ofKey_key, act_eM ρ hsmul]
    refine treeAux_sound S p Ms hMs n T (k' :: seen) (List.nodup_cons.2 ⟨hk'', hnd⟩) ?_ hT
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · obtain ⟨s, rfl⟩ := hx
      refine ⟨g • s • p, ⟨⟨g, hg⟩ * s, ?_⟩, hkey'.symm⟩
      change (⟨g, hg⟩ * s) • p = g • s • p
      rw [mul_smul]
      rfl
    · exact hs j hj

theorem le_card_orbit (S : Subgroup G) (p : N) (s : List Nat) (hnd : s.Nodup)
    (hs : ∀ k ∈ s, ∃ x ∈ orbit S p, key (eV x.1) = k) : s.length ≤ Nat.card (orbit S p) := by
  classical
  have hs' : ∀ k : s.toFinset, ∃ x : orbit S p, key (eV x.1.1) = k.1 := fun k => by
    obtain ⟨x, hx, hk⟩ := hs k.1 (List.mem_toFinset.1 k.2)
    exact ⟨⟨x, hx⟩, hk⟩
  choose f hf using hs'
  have hinj : Function.Injective f := fun a b hab => Subtype.ext (by rw [← hf a, ← hf b, hab])
  have hle := Nat.card_le_card_of_injective f hinj
  have hc : Nat.card s.toFinset = s.length := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]
  omega

theorem root_sound {r : Nat} (h : rootOK r = true) : ∃ x : N, ofKey r = eV x.1 ∧ key (eV x.1) = r := by
  simp only [rootOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, -⟩, hv⟩ := h
  have hv := vbeq_eq hv
  rw [ofKey_eq, nz_eV] at hv
  refine ⟨⟨dK r, eV_inj hv⟩, ofKey_eq r, ?_⟩
  change key (eV (dK r)) = r
  rw [← ofKey_eq, key_ofKey hr]

include hsmul in
theorem tree_sound (S : Subgroup G) (Ms : List (List Nat))
    (hMs : ∀ l, ∃ g ∈ S, lget mI Ms l = eM (ρ g)) {r : Nat} {T : List (Nat × Nat × Nat)} {n : Nat}
    (h : treeOK Ms r T n = true) : ∃ x : N, ofKey r = eV x.1 ∧ n ≤ Nat.card (orbit S x) := by
  simp only [treeOK, Bool.and_eq_true] at h
  obtain ⟨x, hx, hk⟩ := root_sound h.1
  refine ⟨x, hx, ?_⟩
  obtain ⟨s, hnd, hlen, hs⟩ := treeAux_sound ρ hsmul S x Ms hMs n T [r] (List.nodup_singleton r)
    (fun k hk' => ⟨x, mem_orbit_self x, by rw [List.mem_singleton.1 hk', hk]⟩) h.2
  rw [← hlen]
  exact le_card_orbit S x s hnd hs

include h1 hm hsmul in
theorem stab_sound (H : Subgroup G) (L : List (List Nat))
    (hL : ∀ l, ∃ g ∈ H, lget mI L l = eM (ρ g)) {p : Nat} {x : N} (hp : ofKey p = eV x.1)
    {M w : List Nat} (h : stabOK L p M w = true) : ∃ g ∈ H, g • x = x ∧ M = eM (ρ g) := by
  simp only [stabOK, Bool.and_eq_true] at h
  obtain ⟨⟨-, hw⟩, hfix⟩ := h
  obtain ⟨g, hg, hgw⟩ := wprod_sound ρ h1 hm H L hL w
  have hM : M = eM (ρ g) := (lbeq_eq _ _ hw).trans hgw
  refine ⟨g, hg, ?_, hM⟩
  have := vbeq_eq hfix
  rw [hM, hp, act_eM ρ hsmul] at this
  exact Subtype.ext (eV_inj this)

theorem mul_le_card (S : Subgroup G) (p : N) {a b : Nat} (ha : a ≤ Nat.card (orbit S p))
    (hb : b ≤ Nat.card ↥(S ⊓ stabilizer G p)) : a * b ≤ Nat.card S := by
  have e : stabilizer S p ≃ ↥(S ⊓ stabilizer G p) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, mem_stabilizer_iff.2
        (mem_stabilizer_iff.1 x.2)⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, mem_stabilizer_iff.2
        (mem_stabilizer_iff.1 (Subgroup.mem_inf.1 y.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Subgroup.card_mul_index (stabilizer S p)
  rw [index_stabilizer, ← Nat.card_coe_set_eq, Nat.card_congr e] at h
  calc a * b ≤ Nat.card (orbit S p) * Nat.card ↥(S ⊓ stabilizer G p) := Nat.mul_le_mul ha hb
    _ = Nat.card S := by rw [mul_comm]; exact h

theorem fifteen_le [Finite G] (K : Subgroup G) {w : G} (hw : w ∈ K) (h15 : w ^ 15 = 1)
    (h5 : w ^ 5 ≠ 1) (h3 : w ^ 3 ≠ 1) : 15 ≤ Nat.card K := by
  have hd := Subgroup.orderOf_dvd_natCard K hw
  have ho : orderOf w = 15 := by
    have hd15 := orderOf_dvd_of_pow_eq_one h15
    have hn5 : ¬ orderOf w ∣ 5 := fun h => h5 (orderOf_dvd_iff_pow_eq_one.1 h)
    have hn3 : ¬ orderOf w ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.1 h)
    have hle := Nat.le_of_dvd (by norm_num) hd15
    generalize orderOf w = n at hd15 hn5 hn3 hle ⊢
    interval_cases n <;> first | rfl | (exfalso; revert hd15 hn5 hn3; decide)
  rw [ho] at hd
  exact Nat.le_of_dvd Nat.card_pos hd

end Act

theorem orbOK_sound {G : Type*} [Group G] [Finite G] (ρ : G → M3 GF16) (h1 : ρ 1 = 1)
    (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) (hinj : Function.Injective ρ) (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) (L : List (List Nat)) (p : Nat) (T1 : List (Nat × Nat × Nat))
    (S : List (List Nat × List Nat)) (q : Nat) (T2 : List (Nat × Nat × Nat))
    (W : List Nat × List Nat) (hL0 : lget mI L 0 = eM (ρ a)) (hL1 : lget mI L 1 = eM (ρ b))
    (h : orbOK L p T1 S q T2 W = true) : 62400 ≤ Nat.card H := by
  let inst : MulAction G N := mulActionOf ρ h1 hm
  have hsmul : ∀ (g : G) (x : N), (g • x).1 = nzG (mvG (ρ g) x.1) := fun _ _ => rfl
  simp only [orbOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hlet, ht1⟩, hsch⟩, ht2⟩, hw⟩ := h
  have hL := letters_sound ρ h1 hm H L a b ha hb hL0 hL1 hlet
  obtain ⟨p', hp', hc1⟩ := tree_sound ρ hsmul H L hL ht1
  let K : Subgroup G := H ⊓ stabilizer G p'
  have hS : ∀ s ∈ S, ∃ g ∈ K, s.1 = eM (ρ g) := by
    intro s hs
    have hsch' : S.all (fun s => stabOK L p s.1 s.2) = true := hsch
    have hst : stabOK L p s.1 s.2 = true := List.all_eq_true.1 hsch' s hs
    obtain ⟨g, hg, hfix, hM⟩ := stab_sound ρ h1 hm hsmul H L hL hp' hst
    exact ⟨g, Subgroup.mem_inf.2 ⟨hg, mem_stabilizer_iff.2 hfix⟩, hM⟩
  have hMs : ∀ l, ∃ g ∈ K, lget mI (S.map (·.1)) l = eM (ρ g) := by
    intro l
    rcases lget_cases mI (S.map (·.1)) l with hl | hl
    · obtain ⟨s, hs, hs1⟩ := List.mem_map.1 hl
      obtain ⟨g, hg, hM⟩ := hS s hs
      exact ⟨g, hg, by rw [← hs1, hM]⟩
    · exact ⟨1, K.one_mem, by rw [hl, h1]; rfl⟩
  obtain ⟨q', hq', hc2⟩ := tree_sound ρ hsmul K _ hMs ht2
  simp only [wOK, Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨⟨hwp, hwq⟩, hw15⟩, hw5⟩, hw3⟩ := hw
  obtain ⟨w, hwH, hfp, hW⟩ := stab_sound ρ h1 hm hsmul H L hL hp' hwp
  obtain ⟨w', -, hfq, hW'⟩ := stab_sound ρ h1 hm hsmul H L hL hq' hwq
  have hww : w' = w := hinj (eM_inj (hW'.symm.trans hW))
  rw [hww] at hfq
  have e2 : mm (eM (ρ w)) (eM (ρ w)) = eM (ρ (w ^ 2)) := by rw [mm_eM, ← hm, ← pow_two]
  have e3 : mm (eM (ρ w)) (eM (ρ (w ^ 2))) = eM (ρ (w ^ 3)) := by
    rw [mm_eM, ← hm, ← pow_succ']
  have e5 : mm (eM (ρ (w ^ 3))) (eM (ρ (w ^ 2))) = eM (ρ (w ^ 5)) := by
    rw [mm_eM, ← hm, ← pow_add]
  have e10 : mm (eM (ρ (w ^ 5))) (eM (ρ (w ^ 5))) = eM (ρ (w ^ 10)) := by
    rw [mm_eM, ← hm, ← pow_add]
  have e15 : mm (eM (ρ (w ^ 5))) (eM (ρ (w ^ 10))) = eM (ρ (w ^ 15)) := by
    rw [mm_eM, ← hm, ← pow_add]
  rw [hW, e2, e3, e5, e10, e15] at hw15
  rw [hW, e2, e3, e5] at hw5
  rw [hW, e2, e3] at hw3
  have h15 : w ^ 15 = 1 := by
    have := lbeq_eq _ _ hw15
    rw [← eM_one, ← h1] at this
    exact hinj (eM_inj this)
  have hne : ∀ k, lbeq (eM (ρ (w ^ k))) mI = false → w ^ k ≠ 1 := by
    intro k hk he
    rw [he, h1, eM_one, lbeq_refl] at hk
    cases hk
  have hK2 : w ∈ K ⊓ stabilizer G q' :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hwH, mem_stabilizer_iff.2 hfp⟩,
      mem_stabilizer_iff.2 hfq⟩
  have hc3 := fifteen_le (K ⊓ stabilizer G q') hK2 h15 (hne 5 hw5) (hne 3 hw3)
  have hK := mul_le_card K q' hc2 hc3
  have hH := mul_le_card H p' hc1 hK
  omega

end CFSG.KS.U34Orb
