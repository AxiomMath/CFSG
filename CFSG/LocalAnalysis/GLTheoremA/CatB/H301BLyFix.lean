module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem inv_apply' (f : Perm X) (x : X) : f⁻¹ (f x) = x := f.symm_apply_apply x

theorem card_eq_orbit_mul (T : Subgroup (Perm X)) (x : X) :
    Nat.card T =
      Nat.card (orbit T x) * Nat.card (T ⊓ stabilizer (Perm X) x : Subgroup (Perm X)) := by
  rw [Nat.card_congr (orbitProdStabilizerEquivGroup T x).symm, Nat.card_prod]
  congr 1
  exact Nat.card_congr
    { toFun := fun w => ⟨(w.1 : Perm X), w.1.2, w.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_card_orbit_eq {T : Subgroup (Perm X)} (hT : IsPGroup 2 T) (x : X) :
    ∃ k, Nat.card (orbit T x) = 2 ^ k := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (⟨_, hn.symm.trans (card_eq_orbit_mul T x)⟩ : Nat.card (orbit T x) ∣ 2 ^ n)
  exact ⟨k, hk⟩

theorem exists_comm_of_conj_invariant {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {F : Subgroup G} (hF : IsPGroup p F) (S : Set G) (hS : ∀ f ∈ F, ∀ s ∈ S, f * s * f⁻¹ ∈ S)
    (hcard : ¬ p ∣ Nat.card S) : ∃ s ∈ S, ∀ f ∈ F, f * s = s * f := by
  letI : MulAction F S :=
    { smul := fun f s => ⟨f * s * f⁻¹, hS f f.2 s s.2⟩
      one_smul := fun s => Subtype.ext (by
        show (1 : F).1 * s.1 * (1 : F).1⁻¹ = s.1
        simp)
      mul_smul := fun f g s => Subtype.ext (by
        show (f * g).1 * s.1 * (f * g).1⁻¹ = f.1 * (g.1 * s.1 * g.1⁻¹) * f.1⁻¹
        simp [mul_assoc]) }
  obtain ⟨s, hs⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  refine ⟨s, s.2, fun f hf => ?_⟩
  have h := congrArg Subtype.val (mem_fixedPoints.1 hs ⟨f, hf⟩)
  exact mul_inv_eq_iff_eq_mul.1 h

theorem not_three_dvd_fiber {W : Subgroup (Perm X)} (hW : IsPGroup 2 W) {x y : X}
    (h : ∃ w ∈ W, w x = y) : ¬ 3 ∣ Nat.card {w : Perm X | w ∈ W ∧ w x = y} := by
  obtain ⟨w1, hw1, h1⟩ := h
  have hcard : Nat.card {w : Perm X | w ∈ W ∧ w x = y} =
      Nat.card (W ⊓ stabilizer (Perm X) x : Subgroup (Perm X)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w1⁻¹ * w.1, W.mul_mem (W.inv_mem hw1) w.2.1, ?_⟩
        invFun := fun u => ⟨w1 * u.1, W.mul_mem hw1 u.2.1, ?_⟩
        left_inv := fun w => Subtype.ext (mul_inv_cancel_left w1 w.1)
        right_inv := fun u => Subtype.ext (inv_mul_cancel_left w1 u.1) }
    · show (w1⁻¹ * w.1) x = x
      rw [Perm.mul_apply, w.2.2, ← h1]
      exact inv_apply' w1 x
    · have hu : u.1 x = x := u.2.2
      show (w1 * u.1) x = y
      rw [Perm.mul_apply, hu, h1]
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hd : Nat.card (W ⊓ stabilizer (Perm X) x : Subgroup (Perm X)) ∣ 2 ^ n :=
    hn ▸ Subgroup.card_dvd_of_le inf_le_left
  intro h3
  rw [hcard] at h3
  exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3.trans hd)) (by norm_num)

theorem exists_comm_elt {E W : Subgroup (Perm X)} (hE : IsPGroup 3 E) (hW : IsPGroup 2 W)
    (hEW : E ≤ normalizer W) {x y : X} (h : ∃ w ∈ W, w x = y) :
    ∃ w ∈ W, w x = y ∧ ∀ e ∈ E, e x = x → e y = y → e * w = w * e := by
  let F : Subgroup (Perm X) := E ⊓ stabilizer (Perm X) x ⊓ stabilizer (Perm X) y
  have hF : IsPGroup 3 F := hE.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨s, ⟨hsW, hsx⟩, hs⟩ := exists_comm_of_conj_invariant hF
    {w : Perm X | w ∈ W ∧ w x = y} (fun f hf s hs => by
      obtain ⟨⟨hfE, hfx⟩, hfy⟩ := hf
      have hfx' : f x = x := hfx
      have hfy' : f y = y := hfy
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hEW hfE) s).1 hs.1, ?_⟩
      have hfi : f⁻¹ x = x := Equiv.Perm.inv_eq_iff_eq.2 hfx'.symm
      show f (s (f⁻¹ x)) = y
      rw [hfi, hs.2, hfy'])
    (not_three_dvd_fiber hW h)
  exact ⟨s, hsW, hsx, fun e he hex hey => hs e ⟨⟨he, hex⟩, hey⟩⟩

private theorem pow_apply_eq {w a : Perm X} (hc : w * a = a * w) {z : X} {m : ℕ}
    (h : w z = (a ^ m) z) (k : ℕ) : (w ^ k) z = (a ^ (m * k)) z := by
  have hcm : Commute w a := hc
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := (hcm.pow_right (m * k)).eq
    calc (w ^ (k + 1)) z = w ((w ^ k) z) := by rw [pow_succ', Perm.mul_apply]
      _ = w ((a ^ (m * k)) z) := by rw [ih]
      _ = (a ^ (m * k)) (w z) := by
        rw [← Perm.mul_apply, hk, Perm.mul_apply]
      _ = (a ^ (m * (k + 1))) z := by
        rw [h, ← Perm.mul_apply, ← pow_add, mul_add, mul_one]

theorem support_eq_of_three {a : Perm X} (h3 : a ^ 3 = 1) (hs : a.support.card = 3) {z : X}
    (hz : a z ≠ z) : a.support = {z, a z, a (a z)} := by
  have h1 : a (a z) ≠ a z := fun h => hz (a.injective h)
  have h2 : a (a z) ≠ z := by
    intro h
    have h' : a (a (a z)) = z := by
      have := congrArg (fun g : Perm X => g z) h3
      simpa [pow_succ] using this
    exact hz ((congrArg a h).symm.trans h')
  symm
  have hc3 : ({z, a z, a (a z)} : Finset X).card = 3 :=
    Finset.card_eq_three.2 ⟨z, a z, a (a z), hz.symm, h2.symm, h1.symm, rfl⟩
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [hs, hc3])
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact mem_support.2 hz
  · exact mem_support.2 h1
  · exact mem_support.2 (fun h => h1 (a.injective h))

theorem fix_of_comm {W : Subgroup (Perm X)} (hW : IsPGroup 2 W) {w a : Perm X} (hw : w ∈ W)
    (h3 : a ^ 3 = 1) (hs : a.support.card = 3) (hc : w * a = a * w) {z : X} (hz : a z ≠ z) :
    w z = z := by
  obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
  have hwn : w ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have h1 : a (a z) ≠ a z := fun h => hz (a.injective h)
  have h2 : a (a z) ≠ z := by
    intro h
    have h' : a (a (a z)) = z := by
      have := congrArg (fun g : Perm X => g z) h3
      simpa [pow_succ] using this
    exact hz ((congrArg a h).symm.trans h')
  have hsup := support_eq_of_three h3 hs hz
  have hwz : w z ∈ a.support := by
    rw [mem_support]
    intro h
    have : a (w z) = w (a z) := by
      rw [← Perm.mul_apply, ← hc, Perm.mul_apply]
    rw [this] at h
    exact hz (w.injective h)
  obtain ⟨m, hm3, hm⟩ : ∃ m : ℕ, m < 3 ∧ w z = (a ^ m) z := by
    rw [hsup] at hwz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwz
    rcases hwz with h | h | h
    · exact ⟨0, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨2, by norm_num, by simp [pow_two, h]⟩
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using hm
  exfalso
  have hk := pow_apply_eq hc hm (2 ^ n)
  rw [hwn, Perm.one_apply, pow_eq_pow_mod _ h3] at hk
  have hnd : ¬ 3 ∣ m * 2 ^ n := by
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h | h
    · exact absurd (Nat.le_of_dvd hpos h) (by omega)
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hr : (m * 2 ^ n) % 3 = 1 ∨ (m * 2 ^ n) % 3 = 2 := by omega
  rcases hr with hr | hr <;> rw [hr] at hk
  · exact hz (by simpa using hk.symm)
  · exact h2 (by simpa [pow_two] using hk.symm)

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
