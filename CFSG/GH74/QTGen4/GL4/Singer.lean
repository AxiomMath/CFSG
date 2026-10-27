module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34GL
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.QTGen4

open CFSG.Blueprint
open scoped Matrix

def singerMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

theorem singerMat_pow_fifteen : singerMat ^ 15 = 1 := by decide +kernel

theorem singerMat_pow_five : singerMat ^ 5 ≠ 1 := by decide +kernel

theorem singerMat_pow_three : singerMat ^ 3 ≠ 1 := by decide +kernel

theorem singerMat_det : singerMat.det ≠ 0 := by decide +kernel

noncomputable def singerGL : GL (Fin 4) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero singerMat singerMat_det

theorem orderOf_singerGL : orderOf singerGL = 15 := by
  have hv : ∀ n : ℕ, ((singerGL ^ n : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      singerMat ^ n := fun n => by
    rw [Units.val_pow_eq_pow_val]
    rfl
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (Units.ext ?_) ?_
  · rw [hv, singerMat_pow_fifteen]
    rfl
  · intro p hp hpd
    have hp' : p = 3 ∨ p = 5 := by
      have : p ∣ 3 * 5 := hpd
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)
    intro h1
    have h2 := congrArg (fun g : GL (Fin 4) (ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
    simp only [hv, Units.val_one] at h2
    rcases hp' with rfl | rfl
    · exact singerMat_pow_five h2
    · exact singerMat_pow_three h2

theorem card_GL4_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 :=
  CFSG.OddStandard.Seitz77.card_GL_four_two

theorem no_L34_into_GL4 {Q : Type} [Group Q]
    (ψ : Q →* GL (Fin 4) (ZMod 2)) (hψ : Function.Injective ψ)
    (hQ : LieModel Q .PSL 3 2 2) : False := by
  have hst := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hQ
  have hq : CFSG.Quasithin.IsPSLEps3q true 4 Q :=
    ⟨2, 2, Nat.prime_two, by norm_num, by norm_num, hst⟩
  obtain ⟨-, hcard⟩ := CFSG.Quasithin.H13.L34.card_of_isPSLEps3q hq
  have h20160 : Nat.card Q = 20160 := by
    rw [hcard]
    decide +kernel
  have hfin : Finite (GL (Fin 4) (ZMod 2)) := inferInstance
  have hbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).2 ⟨hψ, by rw [h20160, card_GL4_two]⟩
  obtain ⟨q, hq15⟩ := hbij.2 singerGL
  have hord : orderOf q = 15 := by
    rw [← orderOf_injective ψ hψ q, hq15, orderOf_singerGL]
  obtain ⟨p, e, -, -, hqe, hX⟩ := hq
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
  have h4 : Nat.card K = 4 := by
    rw [hK, ← hqe]
  exact CFSG.Quasithin.H13.L34.no_orderOf_eq_fifteen h4 (φ q)
    (by rw [MulEquiv.orderOf_eq]; exact hord)

end CFSG.GH74.QTGen4
