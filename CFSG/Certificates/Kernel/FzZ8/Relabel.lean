module

public import CFSG.Certificates.Kernel.FzUT.FusionT
public import Certificates.Data.FzR10A

public section

namespace CFSG.KC.FzZ8

open Certificates.FzR10A CFSG.OddStandard.SmallF3.FritzII

namespace Rl

theorem ap_lt (m : Mat) (p : ℕ) : m.ap p < 64 := by
  unfold Mat.ap
  generalize m.a * (p % 8) + m.b * (p / 8 % 8) = A
  generalize m.c * (p % 8) + m.d * (p / 8 % 8) = B
  omega

theorem ap_lo (m : Mat) (p : ℕ) : m.ap p % 8 = (m.a * (p % 8) + m.b * (p / 8 % 8)) % 8 := by
  unfold Mat.ap
  generalize m.a * (p % 8) + m.b * (p / 8 % 8) = A
  generalize m.c * (p % 8) + m.d * (p / 8 % 8) = B
  omega

theorem ap_hi (m : Mat) (p : ℕ) : m.ap p / 8 % 8 = (m.c * (p % 8) + m.d * (p / 8 % 8)) % 8 := by
  unfold Mat.ap
  generalize m.a * (p % 8) + m.b * (p / 8 % 8) = A
  generalize m.c * (p % 8) + m.d * (p / 8 % 8) = B
  omega

theorem ap_zero (m : Mat) : m.ap 0 = 0 := by
  simp [Mat.ap]

theorem one_ap {p : ℕ} (hp : p < 64) : Mat.one.ap p = p := by
  simp only [Mat.ap, Mat.one, one_mul, zero_mul, add_zero, zero_add]
  omega

theorem eq_of_digits {p q : ℕ} (hp : p < 64) (hq : q < 64) (h1 : p % 8 = q % 8)
    (h2 : p / 8 % 8 = q / 8 % 8) : p = q := by
  omega

theorem mod8 {a b : ℕ} (h : (a : ZMod 8) = b) : a % 8 = b % 8 :=
  (ZMod.natCast_eq_natCast_iff' a b 8).mp h

theorem mul_ap (m n : Mat) (p : ℕ) : (m.mul n).ap p = m.ap (n.ap p) := by
  apply eq_of_digits (ap_lt _ _) (ap_lt _ _)
  · simp only [ap_lo, ap_hi]
    apply mod8
    simp only [Mat.mul, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
    ring
  · simp only [ap_lo, ap_hi]
    apply mod8
    simp only [Mat.mul, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
    ring

theorem addP_lt (p q : ℕ) : addP p q < 64 := by
  unfold addP
  omega

theorem addP_lo (p q : ℕ) : addP p q % 8 = (p % 8 + q % 8) % 8 := by
  unfold addP
  omega

theorem addP_hi (p q : ℕ) : addP p q / 8 % 8 = (p / 8 % 8 + q / 8 % 8) % 8 := by
  unfold addP
  omega

theorem ap_addP (m : Mat) (p q : ℕ) : m.ap (addP p q) = addP (m.ap p) (m.ap q) := by
  apply eq_of_digits (ap_lt _ _) (addP_lt _ _)
  · simp only [ap_lo, ap_hi, addP_lo, addP_hi]
    apply mod8
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
    ring
  · simp only [ap_lo, ap_hi, addP_lo, addP_hi]
    apply mod8
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
    ring

theorem inZ_iff {p : ℕ} (hp : p < 64) : inZ p = true ↔ addP p p = 0 := by
  unfold inZ addP
  simp only [Bool.and_eq_true, beq_iff_eq]
  omega

theorem comm_ap {g t t' : Mat} (h : g.mul t = t'.mul g) (p : ℕ) : g.ap (t.ap p) = t'.ap (g.ap p) := by
  rw [← mul_ap, h, mul_ap]

theorem ap_inj {g gi : Mat} (h1 : gi.mul g = Mat.one) {p q : ℕ} (hp : p < 64) (hq : q < 64)
    (h : g.ap p = g.ap q) : p = q := by
  rw [← one_ap hp, ← one_ap hq, ← h1, mul_ap, mul_ap, h]

theorem fix_eq {g gi t : Mat} (h1 : gi.mul g = Mat.one) (hgt : g.mul t = t.mul g) {p : ℕ}
    (hp : p < 64) : (t.ap (g.ap p) == g.ap p) = (t.ap p == p) := by
  rw [← comm_ap hgt]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨ap_inj h1 (ap_lt _ _) hp, fun h => by rw [h]⟩

theorem inZ_ap {g gi : Mat} (h1 : gi.mul g = Mat.one) {p : ℕ} (hp : p < 64) :
    inZ (g.ap p) = inZ p := by
  apply Bool.eq_iff_iff.mpr
  rw [inZ_iff (ap_lt _ _), inZ_iff hp, ← ap_addP]
  constructor
  · intro h
    rw [← ap_zero g] at h
    exact ap_inj h1 (addP_lt _ _) (by norm_num) h
  · intro h
    rw [h, ap_zero]

theorem ap_vAct {g t s l l' : Mat} (hgt : g.mul t = t.mul g) (hgs : g.mul s = s.mul g)
    (hgl : g.mul l' = l.mul g) (v q : ℕ) : g.ap (vAct t s l' v q) = vAct t s l v (g.ap q) := by
  simp only [vAct]
  split_ifs <;> simp only [comm_ap hgt, comm_ap hgs, comm_ap hgl]

@[expose] def phi (g : Mat) (x : ℕ) : ℕ := g.ap (x % 64) + 64 * (x / 64)

theorem phi_mod (g : Mat) (x : ℕ) : phi g x % 64 = g.ap (x % 64) := by
  have := ap_lt g (x % 64)
  unfold phi
  omega

theorem phi_div (g : Mat) (x : ℕ) : phi g x / 64 = x / 64 := by
  have := ap_lt g (x % 64)
  unfold phi
  omega

theorem phi_lt (g : Mat) {x : ℕ} (hx : x < 512) : phi g x < 512 := by
  have := ap_lt g (x % 64)
  unfold phi
  omega

theorem phi_add (g : Mat) {a : ℕ} (ha : a < 64) (v : ℕ) : phi g (a + 64 * v) = g.ap a + 64 * v := by
  unfold phi
  have e1 : (a + 64 * v) % 64 = a := by omega
  have e2 : (a + 64 * v) / 64 = v := by omega
  rw [e1, e2]

theorem phi_phi {g gi : Mat} (h1 : gi.mul g = Mat.one) (x : ℕ) : phi gi (phi g x) = x := by
  change gi.ap (phi g x % 64) + 64 * (phi g x / 64) = x
  rw [phi_mod, phi_div, ← mul_ap, h1, one_ap (Nat.mod_lt _ (by norm_num))]
  omega

theorem emA_lt (t s l : Mat) (x y : ℕ) : emA t s l x y < 512 := by
  have h1 := addP_lt (x % 64) (vAct t s l (x / 64 % 8) (y % 64))
  have h2 : x / 64 % 8 ^^^ y / 64 % 8 < 2 ^ 3 :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  simp only [emA]
  omega

theorem phi_emA {g t s l l' : Mat} (hgt : g.mul t = t.mul g) (hgs : g.mul s = s.mul g)
    (hgl : g.mul l' = l.mul g) (x y : ℕ) :
    phi g (emA t s l' x y) = emA t s l (phi g x) (phi g y) := by
  simp only [emA]
  rw [phi_add g (addP_lt _ _), phi_mod, phi_div, phi_mod, phi_div, ap_addP, ap_vAct hgt hgs hgl]

end Rl

open Rl

theorem relabelA {t s l l' g gi : Mat} (h1 : gi.mul g = Mat.one) (h2 : g.mul gi = Mat.one)
    (hgt : g.mul t = t.mul g) (hgs : g.mul s = s.mul g) (hgl : g.mul l' = l.mul g)
    (hgr : g.mul rho0 = rho0.mul g)
    (h : ¬ ∃ θ : ℕ → Prop, FzRules (parOfA t s l') θ) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parOfA t s l) θ := by
  rintro ⟨θ, hθ⟩
  have hd : ∀ x : ℕ, x % 64 < 64 := fun _ => Nat.mod_lt _ (by norm_num)
  refine h ⟨_, CFSG.KC.FzUT.rules_map (P := parOfA t s l) (P' := parOfA t s l')
    (φ := phi g) (ψ := phi gi) (fun x hx => phi_lt g hx) (fun x hx => phi_lt gi hx)
    (fun x _ => phi_phi h1 x) (fun x _ => phi_phi h2 x)
    (fun x y _ _ => phi_emA hgt hgs hgl x y) (fun x y _ _ => emA_lt t s l' x y) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ hθ⟩
  · change g.ap (0 % 64) + 64 * (0 / 64) = 0
    simp [ap_zero]
  · change (64 : ℕ) < 512
    norm_num
  · change (128 : ℕ) < 512
    norm_num
  · change g.ap (64 % 64) + 64 * (64 / 64) = 64
    simp [ap_zero]
  · change g.ap (128 % 64) + 64 * (128 / 64) = 128
    simp [ap_zero]
  · change ∀ x ∈ (#[1, 8, 64, 128, 256] : Array ℕ).toList, x < 512
    decide
  · intro x hx
    have hr := ap_lt rho0 (x % 64)
    have hg := ap_lt g (x % 64)
    refine ⟨?_, ?_, ?_⟩
    · change rho0.ap (x % 64) + 64 * (x / 64) < 512
      omega
    · unfold phi
      omega
    · change phi g (rho0.ap (x % 64) + 64 * (x / 64)) =
        rho0.ap (phi g x % 64) + 64 * (phi g x / 64)
      rw [phi_add g hr, phi_mod, phi_div, comm_ap hgr]
  · intro x _
    simp only [parOfA]
    rw [phi_mod, phi_div, fix_eq h1 hgt (hd x)]
  · intro x _
    simp only [parOfA]
    rw [phi_mod, phi_div, fix_eq h1 hgt (hd x)]
  · intro x _
    simp only [parOfA]
    rw [phi_mod, phi_div, inZ_ap h1 (hd x)]

@[expose] def rlMeq (m n : Mat) : Bool := m.a == n.a && m.b == n.b && m.c == n.c && m.d == n.d

theorem eq_of_rlMeq {m n : Mat} (h : rlMeq m n = true) : m = n := by
  cases m
  cases n
  simp only [rlMeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

theorem relabel_by {t s l l' : Mat} (g gi : Mat)
    (hc : (rlMeq (gi.mul g) Mat.one && rlMeq (g.mul gi) Mat.one && rlMeq (g.mul t) (t.mul g) &&
      rlMeq (g.mul s) (s.mul g) && rlMeq (g.mul l') (l.mul g) && rlMeq (g.mul rho0) (rho0.mul g)) = true)
    (h : ¬ ∃ θ : ℕ → Prop, FzRules (parOfA t s l') θ) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parOfA t s l) θ := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact relabelA (eq_of_rlMeq c1) (eq_of_rlMeq c2) (eq_of_rlMeq c3) (eq_of_rlMeq c4) (eq_of_rlMeq c5)
    (eq_of_rlMeq c6) h

theorem relabel_lsA {s l : Mat} (hs : s = ⟨3, 0, 0, 3⟩ ∨ s = ⟨7, 0, 0, 7⟩)
    (hl : l ∈ [⟨0,1,1,0⟩, ⟨0,3,3,0⟩, ⟨0,5,5,0⟩, ⟨0,7,7,0⟩, ⟨1,0,1,7⟩, ⟨1,7,0,7⟩,
      ⟨3,0,3,5⟩, ⟨3,5,0,5⟩, ⟨5,0,5,3⟩, ⟨5,3,0,3⟩, ⟨7,0,7,1⟩, ⟨7,1,0,1⟩])
    (h : ¬ ∃ θ : ℕ → Prop, FzRules (parOfA ⟨5, 0, 0, 5⟩ s ⟨0, 1, 1, 0⟩) θ) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parOfA ⟨5, 0, 0, 5⟩ s l) θ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact relabel_by ⟨1, 0, 0, 1⟩ ⟨1, 0, 0, 1⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 2, 6, 3⟩ ⟨5, 2, 6, 7⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 4, 4, 5⟩ ⟨1, 4, 4, 5⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 6, 2, 7⟩ ⟨5, 6, 2, 3⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 1, 7, 2⟩ ⟨6, 5, 3, 3⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨0, 1, 7, 1⟩ ⟨1, 7, 1, 0⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 3, 5, 4⟩ ⟨4, 1, 7, 5⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨2, 1, 7, 3⟩ ⟨5, 1, 7, 6⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 5, 3, 6⟩ ⟨2, 5, 3, 7⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨4, 1, 7, 5⟩ ⟨1, 3, 5, 4⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨1, 7, 1, 0⟩ ⟨0, 1, 7, 1⟩ (by rcases hs with rfl | rfl <;> decide) h
  · exact relabel_by ⟨2, 3, 5, 5⟩ ⟨7, 7, 1, 6⟩ (by rcases hs with rfl | rfl <;> decide) h

end CFSG.KC.FzZ8
