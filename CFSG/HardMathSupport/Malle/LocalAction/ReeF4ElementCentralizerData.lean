module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer
public import CFSG.RankThree.PartOne.KF4.B2Sp

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

@[expose] def planeP (α : Fin ReeTag.F4.tag.rank → ℤ) : ℤ := ∑ i, planeU 0 i * α i

@[expose] def planeQ (α : Fin ReeTag.F4.tag.rank → ℤ) : ℤ := ∑ i, planeU 1 i * α i

@[expose] def kerFin (a b : ℕ) : Finset (Fin ReeTag.F4.tag.rank → ℤ) :=
  (rootFinset ReeTag.F4.tag).filter fun α => (a * planeP α + b * planeQ α) % 25 = 0

theorem kerFin_counts : ∀ a ∈ Finset.range 25, ∀ b ∈ Finset.range 25, 5 ∣ a → 5 ∣ b →
    (a ≠ 0 ∨ b ≠ 0) →
    ((kerFin a b).filter fun α => ReeTag.F4.quadForm α = 4).card = 4 ∧
    ((kerFin a b).filter fun α => ReeTag.F4.quadForm α = 2).card = 4 := by
  decide +kernel

@[expose] def kerLat (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range 25 ×ˢ Finset.range 25).filter fun st =>
    ∀ α ∈ kerFin a b, ((st.1 : ℤ) * planeP α + (st.2 : ℤ) * planeQ α) % 25 = 0

theorem kerLat_card : ∀ a ∈ Finset.range 25, ∀ b ∈ Finset.range 25, 5 ∣ a → 5 ∣ b →
    (a ≠ 0 ∨ b ≠ 0) → (kerLat a b).card = 25 ∧ ∃ st ∈ kerLat a b, (¬ 5 ∣ st.1 ∨ ¬ 5 ∣ st.2) := by
  decide +kernel

section Bridge

variable {L : Type} [Field L]

theorem rootChar_expTuple_pow {ξ : Lˣ} (a b : ℕ) (α : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple (ξ ^ a) (ξ ^ b) planeU) α =
      ξ ^ ((a : ℤ) * planeP α + (b : ℤ) * planeQ α) := by
  rw [rootChar_expTuple, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
  rfl

theorem rootChar_expTuple_pow_eq_one_iff {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 25) (a b : ℕ)
    (α : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple (ξ ^ a) (ξ ^ b) planeU) α = 1 ↔
      ((a : ℤ) * planeP α + (b : ℤ) * planeQ α) % 25 = 0 := by
  rw [rootChar_expTuple_pow, hξ.zpow_eq_one_iff_dvd]
  constructor
  · intro h
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast h)
  · intro h
    exact_mod_cast Int.dvd_of_emod_eq_zero h

theorem rootCharKernel_expTuple_pow {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 25) (a b : ℕ) :
    rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) planeU) = ↑(kerFin a b) := by
  ext α
  simp only [rootCharKernel, kerFin, Set.mem_ofPred_eq, Finset.coe_filter]
  rw [rootChar_expTuple_pow_eq_one_iff hξ]
  exact and_congr_left (fun _ => mem_rootFinset.symm)

end Bridge

end CFSG.HardMathSupport.Malle.LocalAction
