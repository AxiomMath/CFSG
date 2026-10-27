
module

public import CFSG.Certificates.Kernel.ThDemp.Action
public import CFSG.Certificates.Kernel.ThDemp.Batches
public import CFSG.Certificates.Kernel.ThDemp.SoundBase
public import CFSG.Certificates.Kernel.ThDemp.Sound
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace CFSG.Certificates.ThDemp.Unfold

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes

theorem andB_split {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> simp_all [andB]

theorem notB_true {a : Bool} (h : BigS.notB a = true) : a = false := by
  cases a <;> simp_all [BigS.notB]

theorem notMemB_sound {x : ℕ} : ∀ {l : List ℕ}, notMemB x l = true → x ∉ l
  | [], _ => by simp
  | y :: t, h => by
    obtain ⟨h1, h2⟩ := andB_split h
    have hne : x ≠ y := fun e => by
      rw [e] at h1
      simp [BigS.notB, Nat.beq_refl] at h1
    simp only [List.mem_cons, not_or]
    exact ⟨hne, notMemB_sound h2⟩

theorem nodupB_sound : ∀ {l : List ℕ}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | y :: t, h => by
    obtain ⟨h1, h2⟩ := andB_split h
    exact List.nodup_cons.mpr ⟨notMemB_sound h1, nodupB_sound h2⟩

theorem recB_spec {g : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true →
      ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_split h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact recB_spec n h2 k hk
    · exact h1

theorem allBelow_spec' {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  intro i him hih
  have hq : i / 64 < hi := by omega
  have h1 := recB_spec hi h (i / 64) hq
  have h2 := recB_spec (g := fun l => Bool.rec (motive := fun _ => Bool) true
    (f (Nat.add (Nat.shiftLeft (i / 64) 6) l)) (Nat.blt (Nat.add (Nat.shiftLeft (i / 64) 6) l) m))
    64 h1 (i % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  simp only [e, Nat.blt_eq.mpr him] at h2
  exact h2

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true :=
  fun i him => allBelow_spec' h i him (by omega)

theorem natRec_add_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_sum F k, Finset.sum_range_succ, Nat.add_comm]

theorem sumBelow_g (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_sum, sumBelow_g m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

theorem sumBelow_spec {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_g]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact Finset.mem_range.mp hi
  rw [hb]

theorem card_filter_of_sumBelow {m hi : ℕ} (hm : m ≤ 64 * hi) (g : ℕ → Bool) :
    sumBelow m hi (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (g i)) =
      ((Finset.range m).filter (fun i => g i = true)).card := by
  rw [sumBelow_spec _ hm, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases g i <;> rfl

variable {D : DempData} {O : OrbData}

variable (hF : DempFacts D)
include hF

theorem pkMat_wordM : ∀ (w : List ℕ) (X : ℕ),
    pkMat (wordR D D.c X w) = pkMat X * (w.map fun r => pkMat (D.RB r)).prod
  | [], X => by
    change pkMat X = pkMat X * 1
    rw [Matrix.mul_one]
  | r :: w, X => by
    have hk := hF.consts
    have e : wordR D D.c X (r :: w) = wordR D D.c (mulB D.c D.rm X (D.RB r)) w := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e, pkMat_wordM w, pkMat_mulB hk, List.map_cons, List.prod_cons, Matrix.mul_assoc]

end CFSG.Certificates.ThDemp.Unfold

end
