module

public import Certificates.Data.Kernel.Spor.Fi24Form
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KC.Fi24FormS

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Form CFSG.Certificates.LceP
  CFSG.KS.Mat3

private theorem toNat_inj : ∀ b c : Bool, b.toNat = c.toNat → b = c := by decide

theorem transOK_spec {P1 P2 Q1 Q2 lo m hi : ℕ} (h : transOK P1 P2 Q1 Q2 lo m hi = true)
    (hm : m ≤ 64 * hi) : ∀ i, lo ≤ i → i < lo + m → i < 781 → ∀ j < 781,
    P1.testBit (781 * i + j) = Q1.testBit (781 * j + i) ∧
      P2.testBit (781 * i + j) = Q2.testBit (781 * j + i) := by
  intro i hlo him hi j hj
  have h1 := Fi24FixS.allBelow_spec h hm (i - lo) (by omega)
  simp only [letB_eq] at h1
  have e : Nat.add lo (i - lo) = i := by change lo + (i - lo) = i; omega
  rw [e] at h1
  have h2 := Fi24FixS.allBelow_spec h1 (by decide) j hj
  unfold rowP at h2
  rw [andB_iff, Nat.beq_eq, Nat.beq_eq, Fi24FixS.bitAt_eq, Fi24FixS.bitAt_eq, Fi24FixS.bitAt_eq,
    Fi24FixS.bitAt_eq, Fi24FixS.testBit_row _ _ _ hj, Fi24FixS.testBit_row _ _ _ hj,
    Fi24FixS.testBit_row _ _ _ hi, Fi24FixS.testBit_row _ _ _ hi] at h2
  exact ⟨toNat_inj _ _ h2.1, toNat_inj _ _ h2.2⟩

theorem LOF_eq : LOF = 2 ^ 609961 - 1 := pow_sub_one_eq 609961

theorem lof_testBit (X p : ℕ) (hp : p < 609961) : (Nat.land X LOF).testBit p = X.testBit p := by
  change (X &&& LOF).testBit p = _
  rw [Nat.testBit_and, LOF_eq, Nat.testBit_two_pow_sub_one]
  simp [hp]

theorem hif_testBit (X p : ℕ) : (Nat.shiftRight X 609961).testBit p = X.testBit (609961 + p) := by
  change (X >>> 609961).testBit p = _
  rw [Nat.testBit_shiftRight]

theorem transM_spec {X Y : ℕ} (h0 : transM X Y 0 196 4 = true) (h1 : transM X Y 196 196 4 = true)
    (h2 : transM X Y 392 196 4 = true) (h3 : transM X Y 588 193 4 = true) :
    mat3 781 609961 X = (mat3 781 609961 Y).transpose := by
  unfold transM at h0 h1 h2 h3
  have hs : ∀ i < 781, ∀ j < 781,
      (Nat.land X LOF).testBit (781 * i + j) = (Nat.land Y LOF).testBit (781 * j + i) ∧
        (Nat.shiftRight X 609961).testBit (781 * i + j) =
          (Nat.shiftRight Y 609961).testBit (781 * j + i) := by
    intro i hi
    rcases Nat.lt_or_ge i 196 with a | a
    · exact transOK_spec h0 (by decide) i (by omega) (by omega) hi
    rcases Nat.lt_or_ge i 392 with b | b
    · exact transOK_spec h1 (by decide) i a (by omega) hi
    rcases Nat.lt_or_ge i 588 with c | c
    · exact transOK_spec h2 (by decide) i b (by omega) hi
    · exact transOK_spec h3 (by decide) i c (by omega) hi
  ext i j
  rw [Matrix.transpose_apply]
  change bv (X.testBit (781 * i.val + j.val)) (X.testBit (609961 + (781 * i.val + j.val))) =
    bv (Y.testBit (781 * j.val + i.val)) (Y.testBit (609961 + (781 * j.val + i.val)))
  obtain ⟨a, b⟩ := hs i.val i.isLt j.val j.isLt
  rw [lof_testBit _ _ (by omega), lof_testBit _ _ (by omega)] at a
  rw [hif_testBit, hif_testBit] at b
  rw [a, b]

end CFSG.KC.Fi24FormS

end
