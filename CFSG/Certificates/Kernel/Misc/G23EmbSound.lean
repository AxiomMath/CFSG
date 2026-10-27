module

public import Certificates.Data.Kernel.Misc.G23Emb
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.G23Emb

open CFSG.KC.Misc.Spec CFSG.KC.Misc.G24

theorem pkMat_c0K (U A2 : ℕ) : pkMat 54 (c0K U A2) =
    pkMat 54 U * (pkMat 54 A2 * (pkMat 54 U * pkMat 54 U * (pkMat 54 A2 * pkMat 54 A2))) := by
  simp only [c0K, pkMat_mulF2]

theorem pkMat_zero_one {x : ℕ} (h : bit x 1 = 1) : pkMat 54 x 0 1 = 1 := by
  have h1 : (x >>> 1) &&& 1 = 1 := h
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h1
  have hb : x.testBit 1 = true := by
    rw [Nat.testBit_succ, Nat.testBit_zero]
    simpa using h1
  simp [pkMat, hb]

theorem embK_sound {U V A1 A2 : ℕ} (h : embK U V A1 A2 = true) :
    let u := pkMat 54 U
    let v := pkMat 54 V
    let a₁ := pkMat 54 A1
    let a₂ := pkMat 54 A2
    let c := pkMat 54 (c0K U A2)
    a₁ * (a₁ * a₁) = 1 ∧ a₂ * (a₂ * a₂) = 1 ∧ u * (u * u) = 1 ∧ c * (c * c) = 1 ∧
      c * u = u * c ∧ c * v = v * c ∧ c * a₁ = a₁ * c ∧ c * a₂ = a₂ * c ∧
      a₁ * a₂ = a₂ * a₁ ∧ v * a₂ = a₂ * v ∧ u * a₂ = c * (a₂ * u) ∧
      v * a₁ = c * (c * (a₁ * v)) ∧ c 0 1 = 1 := by
  unfold embK at h
  simp only [CFSG.KS.PK.letB_eq, CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have e : ∀ {X Y : ℕ}, X = Y → pkMat 54 X = pkMat 54 Y := fun h => congrArg (pkMat 54) h
  exact ⟨by simpa [pkMat_mulF2, pkMat_oneF2] using e h1,
    by simpa [pkMat_mulF2, pkMat_oneF2] using e h2, by simpa [pkMat_mulF2, pkMat_oneF2] using e h3, by simpa [pkMat_mulF2, pkMat_oneF2] using e h4,
    by simpa [pkMat_mulF2] using e h5, by simpa [pkMat_mulF2] using e h6,
    by simpa [pkMat_mulF2] using e h7, by simpa [pkMat_mulF2] using e h8,
    by simpa [pkMat_mulF2] using e h9, by simpa [pkMat_mulF2] using e h10,
    by simpa [pkMat_mulF2] using e h11, by simpa [pkMat_mulF2] using e h12,
    pkMat_zero_one h13⟩

end CFSG.KC.Misc.G23Emb

end
