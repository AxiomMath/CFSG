module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7OneS331
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20B68

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem lem12220_b68_F4 (h331 : Stmt3_3_1_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}
    (hH : Hyp1223 G T L V) (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hsolv : Group.IsSolvable ↥H) :
    ∃ (P : Subgroup G) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥P ∧ P ≤ H ∧ ¬ p ∣ P.relIndex H ∧
      H = P ⊔ T ∧ P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype := by
  obtain ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, hΦ⟩ :=
    Lem20B68.exists_sylow_of_minParabolic (Lem7.minParabolic_F4 h331 hH hHs) hsolv
  refine ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, ?_⟩
  rw [← hΦ, ← inf_assoc, inf_eq_left.mpr hPH]

end CFSG.Quasithin.H13
