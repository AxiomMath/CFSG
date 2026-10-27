module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229Chk
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229

open CFSG.GH74.KGroups

@[expose] def N16 (a : GF16) : GF16 := a * a ^ 4

@[expose] def ev (t0 t1 t2 t3 : GF16) (a : GF16) : GF16 :=
  (if a.toNat &&& 1 = 0 then 0 else t0) + (if a.toNat &&& 2 = 0 then 0 else t1) +
    (if a.toNat &&& 4 = 0 then 0 else t2) + (if a.toNat &&& 8 = 0 then 0 else t3)

@[expose] def e0 : GF16 := GF16.ofNat' 1

@[expose] def e1 : GF16 := GF16.ofNat' 2

@[expose] def e2 : GF16 := GF16.ofNat' 4

@[expose] def e3 : GF16 := GF16.ofNat' 8

theorem decomp (a : GF16) :
    a = (if a.toNat &&& 1 = 0 then 0 else e0) + (if a.toNat &&& 2 = 0 then 0 else e1) +
      (if a.toNat &&& 4 = 0 then 0 else e2) + (if a.toNat &&& 8 = 0 then 0 else e3) := by
  revert a
  decide +kernel

theorem eq_ev (f : GF16 → GF16) (hf : ∀ a b, f (a + b) = f a + f b) (a : GF16) :
    f a = ev (f e0) (f e1) (f e2) (f e3) a := by
  have h0 : f 0 = 0 := by
    have := hf 0 0
    simpa using this
  conv_lhs => rw [decomp a]
  rw [hf, hf, hf]
  unfold ev
  have key : ∀ (c : Prop) [Decidable c] (x : GF16),
      f (if c then 0 else x) = if c then 0 else f x := by
    intro c _ x
    by_cases h : c <;> simp [h, h0]
  rw [key, key, key, key]

theorem toNat_lt (a : GF16) : a.toNat < 16 := a.val.isLt

theorem toNat_ofNat' (k : Nat) (h : k < 16) : (GF16.ofNat' k).toNat = k := Nat.mod_eq_of_lt h

theorem toNat_inj {a b : GF16} (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b => exact congrArg GF16.mk (Fin.ext h)

theorem toNat_add (a b : GF16) : (a + b).toNat = a.toNat ^^^ b.toNat := by
  revert a b
  decide +kernel

theorem toNat_zero : (0 : GF16).toNat = 0 := rfl

theorem toNat_N16 (a : GF16) : (N16 a).toNat = Nt a.toNat := by
  revert a
  decide +kernel

theorem toNat_ev (t0 t1 t2 t3 a : GF16) :
    (ev t0 t1 t2 t3 a).toNat = evN t0.toNat t1.toNat t2.toNat t3.toNat a.toNat := by
  unfold ev evN
  simp only [toNat_add, apply_ite GF16.toNat, toNat_zero]

theorem gf16_no_pair (f₁ f₂ : GF16 → GF16) (hf₁ : ∀ a b, f₁ (a + b) = f₁ a + f₁ b)
    (hf₂ : ∀ a b, f₂ (a + b) = f₂ a + f₂ b)
    (hg₁ : ∀ a b, a * a ^ 4 = b * b ^ 4 → f₁ a * f₁ a ^ 4 = f₁ b * f₁ b ^ 4)
    (hg₂ : ∀ a b, a * a ^ 4 = b * b ^ 4 → f₂ a * f₂ a ^ 4 = f₂ b * f₂ b ^ 4)
    (hne : ∃ a, f₁ a ≠ a) (ho₁ : ∀ a, f₁ (f₁ (f₁ a)) = a) (ho₂ : ∀ a, f₂ (f₂ a) = a)
    (hrel : ∀ a, f₁ (f₂ (f₁ a)) = f₂ a) : False := by
  obtain ⟨t0, ht0⟩ : ∃ t, t = (f₁ e0).toNat := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ : ∃ t, t = (f₁ e1).toNat := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t, t = (f₁ e2).toNat := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ t, t = (f₁ e3).toNat := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ t, t = (f₂ e0).toNat := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ t, t = (f₂ e1).toNat := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ t, t = (f₂ e2).toNat := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ t, t = (f₂ e3).toNat := ⟨_, rfl⟩
  have hv₁ : ∀ a, (f₁ a).toNat = evN t0 t1 t2 t3 a.toNat := fun a => by
    rw [eq_ev f₁ hf₁ a, toNat_ev, ht0, ht1, ht2, ht3]
  have hv₂ : ∀ a, (f₂ a).toNat = evN s0 s1 s2 s3 a.toNat := fun a => by
    rw [eq_ev f₂ hf₂ a, toNat_ev, hs0, hs1, hs2, hs3]
  refine natfin16 t0 t1 t2 t3 (ht0 ▸ toNat_lt _) (ht1 ▸ toNat_lt _) (ht2 ▸ toNat_lt _)
    (ht3 ▸ toNat_lt _) ?_ ?_ ?_ s0 s1 s2 s3 (hs0 ▸ toNat_lt _) (hs1 ▸ toNat_lt _)
    (hs2 ▸ toNat_lt _) (hs3 ▸ toNat_lt _) ?_ ?_ ?_
  · intro a ha
    have h := congrArg GF16.toNat (ho₁ (GF16.ofNat' a))
    rw [hv₁, hv₁, hv₁, toNat_ofNat' a ha] at h
    exact h
  · obtain ⟨a, ha⟩ := hne
    refine ⟨a.toNat, toNat_lt a, fun h => ha (toNat_inj ?_)⟩
    rw [hv₁ a]
    exact h
  · intro a ha b hb hab
    have hAB : N16 (GF16.ofNat' a) = N16 (GF16.ofNat' b) :=
      toNat_inj (by rw [toNat_N16, toNat_N16, toNat_ofNat' a ha, toNat_ofNat' b hb]; exact hab)
    have h := congrArg GF16.toNat (hg₁ _ _ hAB)
    change (N16 (f₁ (GF16.ofNat' a))).toNat = (N16 (f₁ (GF16.ofNat' b))).toNat at h
    rw [toNat_N16, toNat_N16, hv₁, hv₁, toNat_ofNat' a ha, toNat_ofNat' b hb] at h
    exact h
  · intro a ha
    have h := congrArg GF16.toNat (ho₂ (GF16.ofNat' a))
    rw [hv₂, hv₂, toNat_ofNat' a ha] at h
    exact h
  · intro a ha b hb hab
    have hAB : N16 (GF16.ofNat' a) = N16 (GF16.ofNat' b) :=
      toNat_inj (by rw [toNat_N16, toNat_N16, toNat_ofNat' a ha, toNat_ofNat' b hb]; exact hab)
    have h := congrArg GF16.toNat (hg₂ _ _ hAB)
    change (N16 (f₂ (GF16.ofNat' a))).toNat = (N16 (f₂ (GF16.ofNat' b))).toNat at h
    rw [toNat_N16, toNat_N16, hv₂, hv₂, toNat_ofNat' a ha, toNat_ofNat' b hb] at h
    exact h
  · intro a ha
    have h := congrArg GF16.toNat (hrel (GF16.ofNat' a))
    rw [hv₁, hv₂, hv₁, hv₂, toNat_ofNat' a ha] at h
    exact h

theorem gf16_trace_surj : ∀ a : GF16, ∃ b : GF16, b + b ^ 4 + a * a ^ 4 = 0 := by
  decide +kernel

theorem gf16_norm_surj : ∀ b : GF16, b + b ^ 4 = 0 → ∃ a : GF16, a * a ^ 4 = b := by
  decide +kernel

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229
