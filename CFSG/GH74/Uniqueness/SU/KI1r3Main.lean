module

public import CFSG.GH74.Uniqueness.SU.KI1r3Simple
public import CFSG.GH74.Uniqueness.SU.KI1r3Pow

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU

open CFSG.Blueprint in
@[expose] def F61r3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SU0.GHGroup H → Open.twoRank H = 3 →
    IsSimpleGroup ↥(generalizedFitting H) → (∃ a b : ↥(generalizedFitting H), a * b ≠ b * a) →
    centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ →
    ∀ x : H, orderOf x = 2 → x ∉ generalizedFitting H →
      Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1 →
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥(generalizedFitting H) .PSL 2 p f ∧
          IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f

theorem r3PowStmt : R3PowStmt :=
  fun _ _ _ R hR y z hz hzR hyR hy hzy hC hrk => r3pow R hR y z hz hzR hyR hy hzy hC hrk

theorem ki1r3_of_F61 (hF : F61r3) : KI1r3 := by
  intro H _ _ hGH hO hrank hcenter T x hxT hx2 hrk2
  have h : Cfg H T x := ⟨hO, hrank.ge, hcenter, hxT, hx2, hrk2⟩
  obtain ⟨hsimple, hnab, hcen, hxK, hrk⟩ :=
    h.fstar_simple (h.fitting_eq_bot r3PowStmt hrank)
  exact hF H hGH hrank hsimple hnab hcen x hx2 hxK hrk

end CFSG.GH74.Uniqueness.SU.K.R3
