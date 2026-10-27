module

public import CFSG.GH74.Uniqueness.SU.KInputsR3

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint

@[expose] def KI1Concl (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H) : Prop :=
  ((GLS.oPrimeResidual 2 H = generalizedFitting H ⊔ zpowers x ∧
      LieModel ↥(generalizedFitting H) .PSL 3 2 2 ∧
      9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H)) ∧ J2Structure H T) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
      IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f) ∨
    (generalizedFitting H ≤ (T : Subgroup H) ∧ J2Structure H T)

@[expose] def KI1r4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → pPrimeCore 2 H = ⊥ →
    4 ≤ Open.twoRank H → center H = ⊥ →
    ∀ (T : Sylow 2 H) (x : H), x ∈ (T : Subgroup H) → orderOf x = 2 →
      Open.pRank 2 (centralizer ({x} : Set H)) = 2 → KI1Concl H T x

theorem ki1_of_r3_r4 (h3 : KI1r3) (h4 : KI1r4) : KI1 := by
  intro H _ _ hGH hO hrank hcenter T x hxT hx2 hrk2
  rcases Nat.lt_or_ge (Open.twoRank H) 4 with hlt | hge
  · have h3' : Open.twoRank H = 3 := by omega
    exact Or.inr (Or.inl (h3 H hGH hO h3' hcenter T x hxT hx2 hrk2))
  · exact h4 H hGH hO hge hcenter T x hxT hx2 hrk2

end CFSG.GH74.Uniqueness.SU.K
