module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.Generic.QuaternionCentral

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open QuaternionGroup

theorem quat_inv_facts (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    (a (N : ZMod (2 * N)) : QuaternionGroup N) * a (N : ZMod (2 * N)) = 1 ∧
    (a (N : ZMod (2 * N)) : QuaternionGroup N) ≠ 1 ∧
    (∀ g : QuaternionGroup N, g * a (N : ZMod (2 * N)) = a (N : ZMod (2 * N)) * g) ∧
    (∀ g : QuaternionGroup N, g * g = 1 → g = 1 ∨ g = a (N : ZMod (2 * N))) := by
  have h2N : ((N : ZMod (2 * N)) + (N : ZMod (2 * N))) = 0 := by
    have : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
    push_cast at this
    rw [← two_mul]; exact this
  have hNne : (N : ZMod (2 * N)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff N (2 * N)).1 h
    have := Nat.le_of_dvd (by omega) this
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [a_mul_a, h2N]
  · intro h
    have : (a (N : ZMod (2 * N)) : QuaternionGroup N) = a 0 := h
    exact hNne (a.inj this)
  · intro g
    rcases g with i | i
    · simp [a_mul_a, add_comm]
    · simp only [a_mul_xa, xa_mul_a]
      congr 1
      have : (N : ZMod (2 * N)) = -(N : ZMod (2 * N)) := by
        rw [eq_neg_iff_add_eq_zero]; exact h2N
      rw [sub_eq_add_neg, ← this, add_comm]
  · intro g hg
    rcases g with i | i
    · have h1 : i + i = 0 := by
        have : (a (i + i) : QuaternionGroup N) = 1 := by rw [← a_mul_a]; exact hg
        exact a.inj this
      have hm : (2 * N) ∣ (i.val + i.val) := by
        have : ((i.val + i.val : ℕ) : ZMod (2 * N)) = 0 := by
          push_cast; rw [ZMod.natCast_zmod_val]; exact h1
        exact (ZMod.natCast_eq_zero_iff _ _).1 this
      have hdvd : N ∣ i.val := by
        have h' : 2 * N ∣ 2 * i.val := by rwa [← two_mul] at hm
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
      obtain ⟨k, hk⟩ := hdvd
      have hlt := ZMod.val_lt i
      have hk2 : k < 2 := by
        by_contra hk2
        push Not at hk2
        have : N * 2 ≤ N * k := Nat.mul_le_mul_left N hk2
        omega
      have hi : i = ((i.val : ℕ) : ZMod (2 * N)) := (ZMod.natCast_zmod_val i).symm
      interval_cases k
      · left
        rw [hi, hk]; simp
      · right
        rw [hi, hk]; simp
    · exfalso
      have h6 : (a (N : ZMod (2 * N)) : QuaternionGroup N) = 1 := by
        rw [← hg]; simp [xa_mul_xa]
      have h5 : (a (N : ZMod (2 * N)) : QuaternionGroup N) ≠ 1 := by
        intro h
        have : (a (N : ZMod (2 * N)) : QuaternionGroup N) = a 0 := h
        exact hNne (a.inj this)
      exact h5 h6

theorem quat_data {G : Type} [Group G] {P : Subgroup G} (hP : ∃ n, IVK.IsQuaternionTwoGroup ↥P n) :
    ∃ (z : G) (ψ : QuaternionGroup 2 →* G),
      z ∈ P ∧ z * z = 1 ∧ z ≠ 1 ∧ (∀ g ∈ P, g * z = z * g) ∧ (∀ g ∈ P, g * g = 1 → g = 1 ∨ g = z) ∧
      Function.Injective ψ ∧ (∀ g, ψ g ∈ P) ∧ ψ (QuaternionGroup.a 2) = z ∧
      ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨n, hn3, ⟨ι⟩⟩ := hP
  have hNz : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨e, he, hez⟩ := CFSG.GH74.Generic.exists_q8_embedding (j := n - 2) (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := quat_inv_facts (2 ^ (n - 2)) hN2
  set N := 2 ^ (n - 2) with hN
  let ι' : QuaternionGroup N →* G := P.subtype.comp ι.symm.toMonoidHom
  have hι' : Function.Injective ι' := Subtype.val_injective.comp ι.symm.injective
  have hzz : CFSG.GH74.Generic.Qgen.z (n - 2) = a (N : ZMod (2 * N)) := rfl
  refine ⟨ι' (a (N : ZMod (2 * N))), ι'.comp e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ι.symm (a (N : ZMod (2 * N)))).2
  · rw [← map_mul, h1, map_one]
  · intro h
    exact h2 (hι' (h.trans (map_one ι').symm))
  · intro g hg
    have := h3 (ι ⟨g, hg⟩)
    have h' := congrArg ι' this
    rw [map_mul, map_mul] at h'
    have e' : ι' (ι ⟨g, hg⟩) = g := by simp [ι']
    rwa [e'] at h'
  · intro g hg hgg
    have hgg' : ι ⟨g, hg⟩ * ι ⟨g, hg⟩ = 1 := by
      rw [← map_mul]
      have : (⟨g, hg⟩ : ↥P) * ⟨g, hg⟩ = 1 := Subtype.ext hgg
      rw [this, map_one]
    rcases h4 _ hgg' with h | h
    · left
      have := congrArg ι' h
      rw [map_one] at this
      have e' : ι' (ι ⟨g, hg⟩) = g := by simp [ι']
      rwa [e'] at this
    · right
      have := congrArg ι' h
      have e' : ι' (ι ⟨g, hg⟩) = g := by simp [ι']
      rwa [e'] at this
  · exact hι'.comp he
  · intro g
    exact (ι.symm (e g)).2
  · show ι' (e (a 2)) = _
    rw [hez, hzz]
  · intro hcomm
    have hx := hcomm (ι' (e (QuaternionGroup.a 1))) ((ι.symm (e (QuaternionGroup.a 1))).2)
      (ι' (e (QuaternionGroup.xa 0))) ((ι.symm (e (QuaternionGroup.xa 0))).2)
    have hx' : (ι'.comp e) (QuaternionGroup.a 1) * (ι'.comp e) (QuaternionGroup.xa 0) =
        (ι'.comp e) (QuaternionGroup.xa 0) * (ι'.comp e) (QuaternionGroup.a 1) := hx
    rw [← map_mul, ← map_mul] at hx'
    have := (hι'.comp he) hx'
    revert this
    decide

theorem quat_center_sq (N : ℕ) [NeZero N] (hN : 2 ≤ N) (g : QuaternionGroup N)
    (hg : ∀ h : QuaternionGroup N, g * h = h * g) : g * g = 1 := by
  rcases g with i | i
  · have h1 := hg (xa 0)
    simp only [a_mul_xa, xa_mul_a] at h1
    have h2 : (0 - i) = (0 + i) := xa.inj h1
    have h3 : i + i = 0 := by
      have h2' : -i = i := by simpa using h2
      calc i + i = -i + i := by rw [h2']
        _ = 0 := neg_add_cancel i
    rw [a_mul_a, h3]; rfl
  · exfalso
    have h1 := hg (a 1)
    simp only [a_mul_xa, xa_mul_a] at h1
    have h2 : i + 1 = i - 1 := xa.inj h1
    have h3 : (2 : ZMod (2 * N)) = 0 := by
      have : i + 1 - (i - 1) = 0 := by rw [h2]; ring
      have e : i + 1 - (i - 1) = 2 := by ring
      rw [e] at this
      exact this
    have h4 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by exact_mod_cast h3
    have h5 := (ZMod.natCast_eq_zero_iff _ _).1 h4
    have := Nat.le_of_dvd (by norm_num) h5
    omega

theorem quat_data_center {G : Type} [Group G] {P : Subgroup G}
    (hP : ∃ n, IVK.IsQuaternionTwoGroup ↥P n) :
    ∀ g ∈ P, (∀ h ∈ P, g * h = h * g) → g * g = 1 := by
  obtain ⟨n, hn3, ⟨ι⟩⟩ := hP
  have hNz : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro g hg hc
  have h1 : ι ⟨g, hg⟩ * ι ⟨g, hg⟩ = 1 := by
    apply quat_center_sq (2 ^ (n - 2)) hN2
    intro h'
    have hh : (ι.symm h' : ↥P) = ⟨(ι.symm h' : G), (ι.symm h').2⟩ := rfl
    have := hc (ι.symm h' : G) (ι.symm h').2
    have h3 : (⟨g, hg⟩ : ↥P) * ι.symm h' = ι.symm h' * ⟨g, hg⟩ := Subtype.ext this
    have h4 := congrArg ι h3
    simpa using h4
  have h2 : (⟨g, hg⟩ : ↥P) * ⟨g, hg⟩ = 1 := by
    apply ι.injective
    rw [map_mul, map_one]
    exact h1
  exact congrArg Subtype.val h2

end CFSG.GH74.GLS.Bg.Iii2
