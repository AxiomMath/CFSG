module

public import CFSG.CGT.Stroth77.TorusNormalForm
public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type200

theorem uvM_mulVec (x : Fin 3 → ℤ) :
    uvM *ᵥ x = ![-3 * x 0 + x 1 + x 2, -4 * x 0 + x 1 + 2 * x 2, -4 * x 0 + 2 * x 1 + x 2] := by
  funext i
  fin_cases i <;> simp [uvM, uvA, tM, ρM] <;> ring

theorem tM_mulVec (x : Fin 3 → ℤ) :
    tM *ᵥ x = ![x 0 - x 2, 4 * x 0 - x 1 - 2 * x 2, -x 2] := by
  funext i
  fin_cases i <;> simp [uvA, tM, ρM] <;> ring

theorem uM_mulVec (x : Fin 3 → ℤ) : uM *ᵥ x = ![x 0, x 2, x 1] := by
  funext i
  fin_cases i <;> simp [uM, uMat]

theorem ρM_mulVec (x : Fin 3 → ℤ) : ρM *ᵥ x = ![x 0 - x 2, -x 2, x 1 - x 2] := by
  funext i
  fin_cases i <;> simp [ρM] <;> ring

end Type200

namespace Stroth34T200

variable {m : ℕ}

theorem t200_φuv (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φuv (Torus.ofInt _ x) = Torus.ofInt _
      ![-3 * x 0 + x 1 + x 2, -4 * x 0 + x 1 + 2 * x 2, -4 * x 0 + 2 * x 1 + x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t200 m).k) Type200.uvM
    (StrothTypeIndex.t200 m).action.compat_uv x
  rw [Type200.uvM_mulVec] at h
  exact h

theorem t200_φt (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φt (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - x 2, 4 * x 0 - x 1 - 2 * x 2, -x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t200 m).k) Type200.tM
    (StrothTypeIndex.t200 m).action.compat_t x
  rw [Type200.tM_mulVec] at h
  exact h

theorem t200_φu (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ x) = Torus.ofInt _ ![x 0, x 2, x 1] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t200 m).k) Type200.uM
    (StrothTypeIndex.t200 m).action.compat_u x
  rw [Type200.uM_mulVec] at h
  exact h

theorem t200_φρ (x : Fin 3 → ℤ) :
    (StrothTypeIndex.t200 m).action.φρ (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0 - x 2, -x 2, x 1 - x 2] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t200 m).k) Type200.ρM
    (StrothTypeIndex.t200 m).action.compat_ρ x
  rw [Type200.ρM_mulVec] at h
  exact h

theorem t200_k (i : Fin 3) : (StrothTypeIndex.t200 m).k i = ![m, m + 2, m + 2] i := rfl

theorem t200_ofInt_eq_iff (x y : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k x = Torus.ofInt _ y ↔
      (2 : ℤ) ^ m ∣ y 0 - x 0 ∧ (2 : ℤ) ^ (m + 2) ∣ y 1 - x 1 ∧
        (2 : ℤ) ^ (m + 2) ∣ y 2 - x 2 := by
  rw [Torus.ofInt_eq_ofInt_iff]
  constructor
  · intro h
    exact ⟨Int.modEq_iff_dvd.mp (h 0), Int.modEq_iff_dvd.mp (h 1), Int.modEq_iff_dvd.mp (h 2)⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact Int.modEq_iff_dvd.mpr h0
    · exact Int.modEq_iff_dvd.mpr h1
    · exact Int.modEq_iff_dvd.mpr h2

theorem t200_ofInt_eq_zero_iff (x : Fin 3 → ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k x = 0 ↔
      (2 : ℤ) ^ m ∣ x 0 ∧ (2 : ℤ) ^ (m + 2) ∣ x 1 ∧ (2 : ℤ) ^ (m + 2) ∣ x 2 := by
  rw [← Torus.ofInt_zero, t200_ofInt_eq_iff]
  simp

end Stroth34T200

end CFSG.CGT.Stroth77
