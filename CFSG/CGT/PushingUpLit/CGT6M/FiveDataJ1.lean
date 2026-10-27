module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.J1

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.J1

@[expose] def j1Tau : List (ℕ × Bool) :=
  [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, false)]

set_option maxRecDepth 100000 in
theorem j1_pow_eleven : matWord elevenWord ^ 11 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem j1_eleven_ne_one : matWord elevenWord ≠ 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem j1Tau_pow_five : matWord j1Tau ^ 5 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem j1Tau_conj :
    matWord j1Tau * matWord elevenWord = matWord elevenWord ^ 3 * matWord j1Tau := by
  decide +kernel

noncomputable def j1Y : ↥seedGroup := ⟨wordProd unitGen elevenWord, wordProd_mem_seedGroup _⟩

noncomputable def j1T : ↥seedGroup := ⟨wordProd unitGen j1Tau, wordProd_mem_seedGroup _⟩

theorem val_j1Y : (((j1Y : ↥seedGroup) : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) =
    matWord elevenWord := val_wordProd _

theorem val_j1T : (((j1T : ↥seedGroup) : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11)) =
    matWord j1Tau := val_wordProd _

theorem j1Y_pow : j1Y ^ 11 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, val_j1Y, Subgroup.coe_one, Units.val_one]
  exact j1_pow_eleven

theorem j1Y_ne : j1Y ≠ 1 := by
  intro h
  apply j1_eleven_ne_one
  have := congrArg (fun g : ↥seedGroup =>
    ((g : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) h
  simpa [val_j1Y] using this

theorem j1T_pow : j1T ^ 5 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, val_j1T, Subgroup.coe_one, Units.val_one]
  exact j1Tau_pow_five

theorem j1T_conj : j1T * j1Y * j1T⁻¹ = j1Y ^ 3 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, val_j1Y, val_j1T]
  exact j1Tau_conj

theorem frobData_J1 {Q : Type} [Group Q]
    (hQ : NativeSporadic.IsSporadic Q .J1) : FrobData Q := by
  obtain ⟨e0⟩ := hQ
  let e : Q ≃* NativeSporadic.J1 := e0
  let f : ↥seedGroup ≃* Q := nativeEquiv.symm.trans e.symm
  refine ⟨f j1Y, f j1T, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, j1Y_pow, map_one]
  · exact fun h => j1Y_ne (f.injective (by rw [h, map_one]))
  · rw [← map_pow, j1T_pow, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, j1T_conj, map_pow]
  · have hcard : Nat.card Q = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    rw [hcard]
    norm_num

end CFSG.CGT.PushingUpLit.CGT6M
