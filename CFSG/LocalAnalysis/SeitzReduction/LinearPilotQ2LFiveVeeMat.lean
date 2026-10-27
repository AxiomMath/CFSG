module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer

@[expose] def veeW : F4 := F4.ω

@[expose] def veeW2 : F4 := F4.ω * F4.ω

@[expose] def veeMatB : Matrix (Fin 4) (Fin 4) F4 := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def veeMatC : Matrix (Fin 4) (Fin 4) F4 := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def veeMatG : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW, veeW2, 1, 1]

@[expose] def veeMatG' : Matrix (Fin 4) (Fin 4) F4 := diagonal ![1, 1, veeW, veeW2]

@[expose] def veeMatGG : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW, veeW2, veeW, veeW2]

@[expose] def veeMatZ : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW, veeW2, veeW2, veeW]

@[expose] def veeMatH1 : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW, veeW, veeW, 1]

@[expose] def veeMatH2 : Matrix (Fin 4) (Fin 4) F4 := diagonal ![1, veeW, veeW, veeW]

@[expose] def veeMatZH : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW2, 1, 1, veeW]

@[expose] def veeMatZZH : Matrix (Fin 4) (Fin 4) F4 := diagonal ![1, veeW2, veeW2, veeW2]

@[expose] def veeMatH1i : Matrix (Fin 4) (Fin 4) F4 := diagonal ![veeW2, veeW2, veeW2, 1]

@[expose] def veeMatP1 : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, veeW, 0, 0; 1, veeW2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def veeMatP2 : Matrix (Fin 4) (Fin 4) F4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def veeMatP3 : Matrix (Fin 4) (Fin 4) F4 := !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

@[expose] def veeMatP4 : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, veeW, 0, 0; 1, veeW2, 0, 0; 0, 0, 1, veeW; 0, 0, 1, veeW2]

@[expose] def veeMatP5 : Matrix (Fin 4) (Fin 4) F4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def veeMatP6 : Matrix (Fin 4) (Fin 4) F4 := !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

@[expose] def veeB : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatB, by decide +kernel⟩
@[expose] def veeC : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatC, by decide +kernel⟩
@[expose] def veeG : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatG, by decide +kernel⟩
@[expose] def veeG' : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatG', by decide +kernel⟩
@[expose] def veeGG : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatGG, by decide +kernel⟩
@[expose] def veeZ : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatZ, by decide +kernel⟩
@[expose] def veeH1 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatH1, by decide +kernel⟩
@[expose] def veeH2 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatH2, by decide +kernel⟩
@[expose] def veeZH : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatZH, by decide +kernel⟩
@[expose] def veeZZH : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatZZH, by decide +kernel⟩
@[expose] def veeH1i : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatH1i, by decide +kernel⟩
@[expose] def veeP1 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP1, by decide +kernel⟩
@[expose] def veeP2 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP2, by decide +kernel⟩
@[expose] def veeP3 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP3, by decide +kernel⟩
@[expose] def veeP4 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP4, by decide +kernel⟩
@[expose] def veeP5 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP5, by decide +kernel⟩
@[expose] def veeP6 : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatP6, by decide +kernel⟩

theorem veeP1_mul_veeB : veeP1 * veeB = veeG * veeP1 := Subtype.ext (by decide +kernel)
theorem veeP2_mul_veeG : veeP2 * veeG = veeG' * veeP2 := Subtype.ext (by decide +kernel)
theorem veeP3_mul_veeG : veeP3 * veeG = veeZH * veeP3 := Subtype.ext (by decide +kernel)
theorem veeP4_mul_veeC : veeP4 * veeC = veeGG * veeP4 := Subtype.ext (by decide +kernel)
theorem veeP5_mul_veeGG : veeP5 * veeGG = veeZ * veeP5 := Subtype.ext (by decide +kernel)
theorem veeP6_mul_veeH1i : veeP6 * veeH1i = veeZZH * veeP6 := Subtype.ext (by decide +kernel)
theorem veeP6_mul_veeH1 : veeP6 * veeH1 = veeH2 * veeP6 := Subtype.ext (by decide +kernel)
theorem veeG_mul_veeG' : veeG * veeG' = veeGG := Subtype.ext (by decide +kernel)
theorem veeG_mul_veeG'_mul_veeG' : veeG * veeG' * veeG' = veeZ := Subtype.ext (by decide +kernel)
theorem veeG_mul_veeG'_comm : veeG * veeG' = veeG' * veeG := Subtype.ext (by decide +kernel)
theorem veeH1_mul_veeH2 : veeH1 * veeH2 = veeZ := Subtype.ext (by decide +kernel)
theorem veeH1_mul_veeH2_comm : veeH1 * veeH2 = veeH2 * veeH1 := Subtype.ext (by decide +kernel)
theorem veeZ_mul_veeH1 : veeZ * veeH1 = veeZH := Subtype.ext (by decide +kernel)
theorem veeZ_mul_veeZ_mul_veeH1 : veeZ * veeZ * veeH1 = veeZZH := Subtype.ext (by decide +kernel)
theorem veeZ_mul_veeH1_comm : veeZ * veeH1 = veeH1 * veeZ := Subtype.ext (by decide +kernel)
theorem veeH1_mul_veeH1i : veeH1 * veeH1i = 1 := Subtype.ext (by decide +kernel)
theorem veeG_pow_three : veeG ^ 3 = 1 := Subtype.ext (by decide +kernel)
theorem veeG'_pow_three : veeG' ^ 3 = 1 := Subtype.ext (by decide +kernel)
theorem veeZ_pow_three : veeZ ^ 3 = 1 := Subtype.ext (by decide +kernel)
theorem veeH1_pow_three : veeH1 ^ 3 = 1 := Subtype.ext (by decide +kernel)
theorem veeH2_pow_three : veeH2 ^ 3 = 1 := Subtype.ext (by decide +kernel)

end CFSG.SeitzReduction.LinearPilot
