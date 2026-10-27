
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain
public import CFSG.Sporadic.SmallOddCore.Assembly

@[expose] public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore
open scoped Pointwise

@[expose] noncomputable def dP : Equiv.Perm (Fin 820) := permOfArr 820 deltaArr

@[expose] noncomputable def fP : Equiv.Perm (Fin 820) := permOfArr 820 phiArr

@[expose] noncomputable def tP (k : ℕ) : Equiv.Perm (Fin 820) := fP ^ (k / 4) * dP ^ (k % 4)

@[expose] noncomputable def rP (j : ℕ) : Equiv.Perm (Fin 820) := permOfArr 820 reps[j]!

theorem tP_zero : tP 0 = 1 := by simp [tP]

theorem tP_one : tP 1 = dP := by simp [tP]

theorem tP_four : tP 4 = fP := by simp [tP]

theorem rep_powA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) (e : ℕ) :
    Rep n (powA n t e) (g ^ e) := by
  induction e with
  | zero => exact rep_idA
  | succ e ih =>
    rw [pow_succ']
    exact rep_compA h ih

section Tables

theorem mem_normalizer_P_of_gens {u : Equiv.Perm (Fin 820)}
    (hx : u * psi xElt * u⁻¹ ∈ P) (hy : u * psi yElt * u⁻¹ ∈ P) :
    u ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) := by
  have hle : P.map (MulAut.conj u).toMonoidHom ≤ P := by
    conv_lhs => rw [P_eq_closure]
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have heq : P.map (MulAut.conj u).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj u).injective])
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨q, hq, hqh⟩ := hh
    have : q = h := by
      have h1 : u * q * u⁻¹ = u * h * u⁻¹ := hqh
      simpa using h1
    rw [← this]
    exact hq

end Tables

end CFSG.EvenSporadicStandard.M24Std.CU43
