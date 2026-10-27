module

public import Certificates.Data.Kernel.TS8WrK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrRep

public section

namespace CFSG.KC.TS8WrK

open CFSG.EvenSporadicStandard.Fin76b.TS8Wr CFSG.QuasithinUnique.A6Facts

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem allN_eq_true {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

@[expose] def dec (k : Nat) : Nat × Nat × Bool := (k / 64, k / 2 % 32, k % 2 == 1)

@[expose] noncomputable def rk (k : Nat) : Pt := rep (dec k)

theorem valid_dec {k : Nat} (hk : k < 2048) : Valid (dec k) := by
  refine ⟨?_, ?_⟩
  · change k / 64 < 32
    omega
  · change k / 2 % 32 < 32
    omega

theorem dec_mk {A B e : Nat} (hA : A < 32) (hB : B < 32) (he : e < 2) :
    64 * A + (2 * B + e) < 2048 ∧ dec (64 * A + (2 * B + e)) = (A, B, e == 1) := by
  refine ⟨by omega, ?_⟩
  simp only [dec, Prod.mk.injEq]
  refine ⟨by omega, by omega, ?_⟩
  congr 1
  omega

theorem dec_inj {k k' : Nat} (hk : k < 2048) (hk' : k' < 2048) (h : dec k = dec k') : k = k' := by
  simp only [dec, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h4 : k % 2 = k' % 2 := by
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one k' with h' | h' <;> simp_all
  omega

theorem mulK_even (TB : Nat) {x : Nat} (y : Nat) (hx : x % 2 = 0) :
    mulK TB x y = 64 * tK TB (x / 64) (y / 64) + (2 * tK TB (x / 2 % 32) (y / 2 % 32) + y % 2) := by
  have hx' : Nat.mod x 2 = 0 := hx
  unfold mulK ifN
  rw [hx']
  rfl

theorem mulK_odd (TB : Nat) {x : Nat} (y : Nat) (hx : x % 2 = 1) :
    mulK TB x y =
      64 * tK TB (x / 64) (y / 2 % 32) + (2 * tK TB (x / 2 % 32) (y / 64) + (1 - y % 2)) := by
  have hx' : Nat.mod x 2 = 1 := hx
  unfold mulK ifN
  rw [hx']
  rfl

theorem tK_eq {TB one : Nat} (h : tbOK TB one = true) {a b : Nat} (ha : a < 32) (hb : b < 32) :
    tK TB a b = t0 a b := by
  unfold tbOK at h
  rw [andB_eq_true, allN_eq_true] at h
  have h1 := h.1 a ha
  rw [allN_eq_true] at h1
  exact Nat.eq_of_beq_eq_true (h1 b hb)

theorem one_eq {TB one : Nat} (h : tbOK TB one = true) : one = 66 * i0 := by
  unfold tbOK at h
  rw [andB_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem mulK_spec {TB one : Nat} (hT : tbOK TB one = true)
    (hcl : ∀ a < 32, ∀ b < 32, Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit) {x y : Nat}
    (hx : x < 2048) (hy : y < 2048) :
    mulK TB x y < 2048 ∧ dec (mulK TB x y) = mulI (mtab ()) (dec x) (dec y) := by
  have h1 : x / 64 < 32 := by omega
  have h2 : x / 2 % 32 < 32 := by omega
  have h3 : y / 64 < 32 := by omega
  have h4 : y / 2 % 32 < 32 := by omega
  have hy2 : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hdy : dec y = (y / 64, y / 2 % 32, y % 2 == 1) := rfl
  rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
  · have hdx : dec x = (x / 64, x / 2 % 32, false) := by simp [dec, hx2]
    rw [mulK_even TB y hx2, tK_eq hT h1 h3, tK_eq hT h2 h4, hdx, hdy, mulI_false, mtab_get h1 h3,
      mtab_get h2 h4]
    exact dec_mk (t0_lt (hcl _ h1 _ h3)) (t0_lt (hcl _ h2 _ h4)) hy2
  · have hdx : dec x = (x / 64, x / 2 % 32, true) := by simp [dec, hx2]
    rw [mulK_odd TB y hx2, tK_eq hT h1 h4, tK_eq hT h2 h3, hdx, hdy, mulI_true, mtab_get h1 h4,
      mtab_get h2 h3]
    obtain ⟨hb, hd⟩ := dec_mk (t0_lt (hcl _ h1 _ h4)) (t0_lt (hcl _ h2 _ h3))
      (by omega : 1 - y % 2 < 2)
    refine ⟨hb, ?_⟩
    rw [hd]
    rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]

theorem mulK_lt {TB one : Nat} (hT : tbOK TB one = true) (hp : p0Ok () = true) {x y : Nat}
    (hx : x < 2048) (hy : y < 2048) : mulK TB x y < 2048 :=
  (mulK_spec hT (p0Ok_spec hp).1 hx hy).1

theorem rk_mulK {TB one : Nat} (hT : tbOK TB one = true) (hp : p0Ok () = true) {x y : Nat}
    (hx : x < 2048) (hy : y < 2048) : rk (mulK TB x y) = rk x * rk y := by
  have hcl := (p0Ok_spec hp).1
  unfold rk
  rw [(mulK_spec hT hcl hx hy).2]
  exact rep_mulI hcl (valid_dec hx) (valid_dec hy)

theorem rk_inj {x y : Nat} (hx : x < 2048) (hy : y < 2048) (h : rk x = rk y) : x = y :=
  dec_inj hx hy (rep_inj (valid_dec hx) (valid_dec hy) h)

theorem rk_surj {g : Pt} (hg : g ∈ Sig) : ∃ k < 2048, rk k = g := by
  obtain ⟨⟨a, b, e⟩, ⟨ha, hb⟩, rfl⟩ := rep_surj hg
  have he : (if e then 1 else 0) < 2 := by cases e <;> decide
  obtain ⟨hk, hd⟩ := dec_mk ha hb he
  refine ⟨_, hk, ?_⟩
  unfold rk
  rw [hd]
  cases e <;> rfl

theorem rk_mem {k : Nat} (hk : k < 2048) : rk k ∈ Sig := by
  obtain ⟨ha, hb⟩ := valid_dec hk
  refine ⟨e0 (dec k).1, e0_mem ha, e0 (dec k).2.1, e0_mem hb, ?_⟩
  unfold rk rep
  cases (dec k).2.2
  · left
    simp
  · right
    simp

theorem rk_one {TB one : Nat} (hT : tbOK TB one = true) (hp : p0Ok () = true) :
    one < 2048 ∧ rk one = 1 := by
  obtain ⟨_, hcid, hci⟩ := p0Ok_spec hp
  have hi := i0_lt hcid
  have h66 : one = 64 * i0 + (2 * i0 + 0) := by rw [one_eq hT]; omega
  obtain ⟨hk, hd⟩ := dec_mk hi hi (by norm_num : 0 < 2)
  refine ⟨by rw [h66]; exact hk, ?_⟩
  unfold rk
  rw [h66, hd]
  exact rep_one hcid hci

end CFSG.KC.TS8WrK
