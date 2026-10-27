module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModH1

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

@[expose] def Q2cols : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 63422, 0, 41276, 6362, 0,
   0, 0, 0, 0, 33824, 2, 4, 8,
   24, 33796, 78, 63290, 29186, 34384, 30522, 2242]

@[expose] def Q2m : Matrix (Fin 4 × Fin 4) UIdx (ZMod 2) := Matrix.of fun k i =>
  if (Q2cols.getD (uflat i) 0).testBit (4 * (k.1 : ℕ) + (k.2 : ℕ)) then 1 else 0

@[expose] def idVec : Fin 4 × Fin 4 → ZMod 2 := fun k => if k.1 = k.2 then 1 else 0

theorem schur_unit : ∀ i : Fin 4 × Fin 4,
    (Pi.single i (1 : ZMod 2) : Fin 4 × Fin 4 → ZMod 2) +
      (Pi.single i (1 : ZMod 2) : Fin 4 × Fin 4 → ZMod 2) (0, 0) • idVec =
        Q2m *ᵥ pk (cob (mOf (Pi.single i (1 : ZMod 2)))) := by
  decide +kernel

theorem schur_key (v : Fin 4 × Fin 4 → ZMod 2) :
    v + v (0, 0) • idVec = Q2m *ᵥ pk (cob (mOf v)) := by
  let L₁ : (Fin 4 × Fin 4 → ZMod 2) →+ (Fin 4 × Fin 4 → ZMod 2) :=
    AddMonoidHom.mk' (fun v => v + v (0, 0) • idVec) (by
      intro x y
      simp only [Pi.add_apply, add_smul]
      abel)
  let L₂ : (Fin 4 × Fin 4 → ZMod 2) →+ (Fin 4 × Fin 4 → ZMod 2) :=
    AddMonoidHom.mk' (fun v => Q2m *ᵥ pk (cob (mOf v))) (by
      intro x y
      simp only [mOf_add, cob_add, pk_add, Matrix.mulVec_add])
  have hL : L₁ = L₂ := by
    refine AddMonoidHom.functions_ext _ L₁ L₂ (fun i a => ?_)
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · rw [Pi.single_zero, map_zero, map_zero]
    · exact schur_unit i
  exact DFunLike.congr_fun hL v

theorem schur_rho {m : Mat4} (h1 : m * rho sigma = rho sigma * m)
    (h2 : m * rho tau = rho tau * m) : m = 0 ∨ m = 1 := by
  rw [rho_sigma_eq] at h1
  rw [rho_tau_eq] at h2
  have hz : ∀ a b : Mat4, a = b → a + b = 0 := by
    intro a b hab
    subst hab
    ext i j
    exact (by decide : ∀ x : ZMod 2, x + x = 0) _
  have hc : cob m = 0 := by
    refine Prod.ext ?_ ?_
    · exact hz _ _ (by rw [h1])
    · exact hz _ _ (by rw [h2])
  have hk := schur_key (fun k => m k.1 k.2)
  have hm : mOf (fun k : Fin 4 × Fin 4 => m k.1 k.2) = m := by
    ext k l
    rfl
  rw [hm, hc] at hk
  have hpk : pk ((0 : Mat4), (0 : Mat4)) = 0 := by
    ext i
    simp [pk]
  rw [show (0 : Mat4 × Mat4) = ((0 : Mat4), (0 : Mat4)) from rfl, hpk, Matrix.mulVec_zero] at hk
  have hm0 : ∀ k l : Fin 4, m k l = m 0 0 * (if k = l then 1 else 0) := by
    intro k l
    have hi := congrFun hk (k, l)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, idVec] at hi
    have h' : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h' _ _ hi
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (m 0 0) with h0 | h0
  · left
    ext k l
    rw [hm0 k l, h0]
    simp
  · right
    ext k l
    rw [hm0 k l, h0, one_mul]
    by_cases hkl : k = l
    · subst hkl
      simp
    · simp [hkl]

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
