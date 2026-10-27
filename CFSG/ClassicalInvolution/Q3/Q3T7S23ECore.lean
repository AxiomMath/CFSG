module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22PsuPair
public import CFSG.ClassicalInvolution.Q3.Q3PsuSup3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C22G
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)


theorem eSide_core3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (P : PSULayer 3 1 Φ) {K K' J J' : Subgroup X} {z t e a b : X}
    (hKΦ : K ∈ Φ) (hK'Φ : K' ∈ Φ) (hJΦ : J ∈ Φ) (hJ'Φ : J' ∈ Φ)
    (hzK : IsUniqueInvolution K z) (htJ : IsUniqueInvolution J t)
    (htJ' : IsUniqueInvolution J' t) (ha : a ∈ K) (hb : b ∈ K') (haa : a * a = z)
    (hcomm : Commutes K K') (hcomm' : Commutes J J') (he : e ∈ omegaGen Φ)
    (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e)
    (hKJ : K ≠ J) (hKJc : ¬ Commutes K J) (hKJ' : K ≠ J') (hKJc' : ¬ Commutes K J') :
    (∃ W', UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' K J) ∧
      (∃ W', UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' K J') ∧
      J' ⊔ K ⊔ J = omegaGen Φ := by
  obtain ⟨RK, hRK, hKR⟩ := P.fund K hKΦ
  obtain ⟨RK', hRK', hKR'⟩ := P.fund K' hK'Φ
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund J hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund J' hJ'Φ
  obtain ⟨hpJR, hpJ⟩ := Q3T8.Asc77.C22G.psuLayer_pair3 P hRK hRJ hKR hKR' hJR hzK htJ ha hb haa
    hcomm he hec htab hKJ hKJc
  obtain ⟨hpJ'R, hpJ'⟩ := Q3T8.Asc77.C22G.psuLayer_pair3 P hRK hRJ' hKR hKR' hJ'R hzK htJ' ha hb
    haa hcomm he hec htab hKJ' hKJc'
  refine ⟨hpJ, hpJ', ?_⟩
  obtain ⟨W₁, hW₁⟩ := hpJ'R
  exact Q3PsuSup.psuLayer_sup3 P hRJ' hKR hJR hJ'R
    ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ hpJR hcomm'

end CFSG.ClassicalInvolution.Q3.Q3T7S23
