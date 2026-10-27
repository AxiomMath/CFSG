module

public import CFSG.Certificates.Kernel.Fi22Omega.Sound

public section

namespace CFSG.KC.Fi22Omega

open Equiv CFSG.KC.Benes
open scoped Pointwise

variable {T NT RT : Nat → Nat}

theorem msk_lt (hN : ∀ i < 61776, nodeOK T NT RT i = true) {i : Nat} (hi : i < 61776) :
    msk (recAt T i) < 2 ^ 3510 :=
  (nodeOK_sound (hN i hi)).1

theorem forest_orbit (hN : ∀ i < 61776, nodeOK T NT RT i = true)
    {H : Subgroup (Perm (Fin 3510))} {σ : Nat → Perm (Fin 3510)} (hσ : ∀ l < 2, σ l ∈ H)
    (hnet : ∀ l < 2, StagesValid 12 (NT l) ∧
      ∀ p : Fin 3510, benesPerm 12 (NT l) p = ((σ l)⁻¹ p : Nat)) :
    ∀ i < 61776, ∃ h ∈ H, maskSet (msk (recAt T i)) =
      h • maskSet (msk (recAt T (RT (blkF (recAt T i))))) := by
  suffices key : ∀ d, ∀ i < 61776, depF (recAt T i) = d → ∃ h ∈ H, maskSet (msk (recAt T i)) =
      h • maskSet (msk (recAt T (RT (blkF (recAt T i))))) from
    fun i hi => key _ i hi rfl
  intro d
  induction d with
  | zero =>
    intro i hi hd
    have e := (nodeOK_sound (hN i hi)).2.2.2.1 hd
    refine ⟨1, H.one_mem, ?_⟩
    rw [one_smul, ← e]
  | succ d ih =>
    intro i hi hd
    obtain ⟨hp, hl, hdp, hbp, himg⟩ := (nodeOK_sound (hN i hi)).2.2.2.2 (by omega)
    obtain ⟨h, hH, e⟩ := ih _ hp (by omega)
    obtain ⟨hv, hb⟩ := hnet _ hl
    have hs := (img_sound hv hb (msk_lt hN hp)).1
    rw [himg] at hs
    refine ⟨σ (letF (recAt T i)) * h, H.mul_mem (hσ _ hl) hH, ?_⟩
    rw [hs, e, hbp, mul_smul]

theorem key_lt (hN : ∀ i < 61776, nodeOK T NT RT i = true) {i : Nat} :
    ∀ {j : Nat}, i < j → j < 61776 → key (msk (recAt T i)) < key (msk (recAt T j))
  | 0, h, _ => absurd h (Nat.not_lt_zero i)
  | j + 1, h, hj => by
    have hs := (nodeOK_sound (hN j (by omega))).2.1 hj
    rcases Nat.lt_or_ge i j with h2 | h2
    · exact lt_trans (key_lt hN h2 (by omega)) hs
    · have e : i = j := by omega
      subst e
      exact hs

theorem maskSet_inj {M M' : Nat} (h : M < 2 ^ 3510) (h' : M' < 2 ^ 3510)
    (e : maskSet M = maskSet M') : M = M' := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 3510 with hq | hq
  · have := congrArg (fun S => (⟨q, hq⟩ : Fin 3510) ∈ S) e
    simp only [maskSet, Set.mem_setOf_eq, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hq)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h' (Nat.pow_le_pow_right (by decide) hq))]

theorem nodes_inj (hN : ∀ i < 61776, nodeOK T NT RT i = true) {i j : Nat} (hi : i < 61776)
    (hj : j < 61776) (e : maskSet (msk (recAt T i)) = maskSet (msk (recAt T j))) : i = j := by
  have he := maskSet_inj (msk_lt hN hi) (msk_lt hN hj) e
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := key_lt hN h hj
    rw [he] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := key_lt hN h hi
    rw [he] at this
    exact absurd this (lt_irrefl _)

end CFSG.KC.Fi22Omega

end
