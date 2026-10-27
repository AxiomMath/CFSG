module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.NormalSylowDirectProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem derivedSeries_le_of_commutator_top_le {r : ℕ} {S : ℕ → Subgroup G} (htop : S r = ⊤)
    (hcomm : ∀ i, 1 ≤ i → i ≤ r → ⁅(⊤ : Subgroup G), S i⁆ ≤ S (i - 1)) :
    ∀ j ≤ r, derivedSeries G j ≤ S (r - j) := by
  intro j
  induction j with
  | zero => intro _; rw [derivedSeries_zero, Nat.sub_zero, htop]
  | succ j ih =>
    intro hj
    calc derivedSeries G (j + 1) = ⁅derivedSeries G j, derivedSeries G j⁆ := derivedSeries_succ G j
      _ ≤ ⁅(⊤ : Subgroup G), S (r - j)⁆ := Subgroup.commutator_mono le_top (ih (by omega))
      _ ≤ S (r - j - 1) := hcomm (r - j) (by omega) (by omega)
      _ = S (r - (j + 1)) := by rw [show r - j - 1 = r - (j + 1) from by omega]

theorem isSolvable_of_exists_normal_series_commutator_le
    (h : ∃ (r : ℕ) (S : ℕ → Subgroup G), S 0 = ⊥ ∧ S r = ⊤ ∧ (∀ i < r, S i ≤ S (i + 1)) ∧
      (∀ i, (S i).Normal) ∧ ∀ i, 1 ≤ i → i ≤ r → ⁅(⊤ : Subgroup G), S i⁆ ≤ S (i - 1)) :
    Group.IsSolvable G := by
  obtain ⟨r, S, hbot, htop, -, -, hcomm⟩ := h
  refine (Group.isSolvable_def G).2 ⟨r, le_bot_iff.1 ?_⟩
  simpa [hbot] using derivedSeries_le_of_commutator_top_le htop hcomm r le_rfl

theorem isSolvable_of_exists_upperCenterSeries_eq_top
    (h : ∃ (r : ℕ) (Z : ℕ → Subgroup G) (hn : ∀ i, (Z i).Normal), Z 0 = ⊥ ∧
      (∀ i, letI := hn i;
        Z (i + 1) = Subgroup.comap (QuotientGroup.mk' (Z i)) (Subgroup.center (G ⧸ Z i))) ∧
      Z r = ⊤) : Group.IsSolvable G :=
  haveI := (isNilpotent_iff_exists_upperCenterSeries_eq_top G).2 h
  inferInstance

theorem isSolvable_of_exists_normal_sylow_family [Finite G]
    (h : ∃ (P : (Nat.card G).primeFactors → Subgroup G)
      (hcard : ∀ p, Nat.card (P p) = (p : ℕ) ^ (Nat.card G).factorization (p : ℕ))
      (hn : ∀ p, (P p).Normal), Function.Bijective (normalSylowPiHom P hcard hn)) :
    Group.IsSolvable G :=
  haveI := (isNilpotent_iff_exists_normal_sylow_family G).2 h
  inferInstance

end CFSG.FeitThompson

end
