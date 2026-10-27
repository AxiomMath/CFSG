module

public import CFSG.GH74.Uniqueness.SU.KInputsR4
public import CFSG.GH74.Uniqueness.SU.KI1r3Simple

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.SU.K.R3

@[expose] def F61Full : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H →
    IsSimpleGroup ↥(generalizedFitting H) → (∃ a b : ↥(generalizedFitting H), a * b ≠ b * a) →
    centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ →
    ∀ x : H, orderOf x = 2 → x ∉ generalizedFitting H →
      Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1 →
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
          IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f) ∨
        (LieModel ↥(generalizedFitting H) .PSL 3 2 2 ∧
          9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H))

@[expose] def KI1r4L34 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H), Cfg H T x → 4 ≤ Open.twoRank H →
    IsSimpleGroup ↥(generalizedFitting H) →
    centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ →
    x ∉ generalizedFitting H →
    LieModel ↥(generalizedFitting H) .PSL 3 2 2 →
    9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H) →
      ((GLS.oPrimeResidual 2 H = generalizedFitting H ⊔ zpowers x ∧
        LieModel ↥(generalizedFitting H) .PSL 3 2 2 ∧
        9 ∣ Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H)) ∧ J2Structure H T)

@[expose] def KI1r4TwoGroup : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H), Cfg H T x → 4 ≤ Open.twoRank H →
    fittingSubgroup H ≠ ⊥ → generalizedFitting H ≤ (T : Subgroup H) ∧ J2Structure H T

theorem ki1r4_of_parts (hF : F61Full) (hL : KI1r4L34) (hQ : KI1r4TwoGroup) : KI1r4 := by
  intro H _ _ hGH hO hrank hcenter T x hxT hx2 hrk2
  have h : Cfg H T x := ⟨hO, by omega, hcenter, hxT, hx2, hrk2⟩
  by_cases hFit : fittingSubgroup H = ⊥
  · obtain ⟨hsimple, hnab, hcen, hxK, hrk⟩ := h.fstar_simple hFit
    rcases hF H hGH hsimple hnab hcen x hx2 hxK hrk with hB | ⟨hL34, h9⟩
    · exact Or.inr (Or.inl hB)
    · exact Or.inl (hL H T x h hrank hsimple hcen hxK hL34 h9)
  · exact Or.inr (Or.inr (hQ H T x h hrank hFit))

end CFSG.GH74.Uniqueness.SU.K.R4
