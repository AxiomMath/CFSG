module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabHub
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub

open CFSG.LieType.Universal.Spin QuadraticMap

section Odd

variable {K : Type} [Field K]

@[expose] noncomputable def tvO (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  Pi.single (.inl i) 1 + Pi.single (.inr (.inl i)) 1

@[expose] noncomputable def svO (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  Pi.single (.inl i) 1 - Pi.single (.inr (.inl i)) 1

@[expose] noncomputable def zvO : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (.inr (.inr ())) 1

@[expose] noncomputable def oddSys : Sys (quadOdd 3 K) where
  o := ![tvO 0, tvO 1, tvO 2, zvO, svO 0, svO 1]
  sq := by
    intro i
    fin_cases i <;> simp [quadOdd_apply, tvO, svO, zvO, eps, Pi.single_apply]
  orth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (rw [polar_quadOdd]; simp [tvO, svO, zvO, Pi.single_apply, Fin.sum_univ_three])

end Odd

section Minus

variable {K : Type} [Field K]

@[expose] noncomputable def tvM (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K :=
  Pi.single (.inl i) 1 + Pi.single (.inr (.inl i)) 1

@[expose] noncomputable def svM (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K :=
  Pi.single (.inl i) 1 - Pi.single (.inr (.inl i)) 1

@[expose] noncomputable def uvM : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K := Pi.single (.inr (.inr 0)) 1

@[expose] noncomputable def minusSys (b c : K) : Sys (quadMinus 4 K b c) where
  o := ![tvM 0, tvM 1, tvM 2, uvM, svM 0, svM 1]
  sq := by
    intro i
    fin_cases i <;> (rw [quadMinus_apply]; simp [tvM, svM, uvM, eps, Pi.single_apply])
  orth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (rw [polar_quadMinus]; simp [tvM, svM, uvM, Pi.single_apply, Fin.sum_univ_three])

end Minus

end CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub
