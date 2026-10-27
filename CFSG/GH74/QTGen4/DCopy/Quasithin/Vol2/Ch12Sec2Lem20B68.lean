module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20B68S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def Lem12220Choice_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P : Subgroup G) (p : ℕ), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
    p.Prime → p ≠ 2 → IsPGroup p ↥P → P ≤ H → ¬ p ∣ P.relIndex H → H = P ⊔ T →
    P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype →
      ∃ (U I : Subgroup G) (h : G), h ∈ P ∧ h ∉ Subgroup.normalizer (L : Set G) ∧
        I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
        U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
        IsElemAbelian 2 U ∧ U = ⁅U, oTwoUpper I⁆ ∧
        (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
        (U ⊓ V).relIndex V = 2 ∧
        ∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)

theorem lem12220PickFull_of_F4 (h331 : Stmt3_3_1_F4) (hch : Lem12220Choice_F4) : Lem12220PickFull_F4 := by
  intro G _ _ T L V H hH hNE hHs hsolv
  obtain ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, hΦ⟩ := lem12220_b68_F4 h331 hH hHs hsolv
  obtain ⟨U, I, h, hhP, hhM, hI, hU, hUdec, hUinf, hUe, hUc, hD, hidx, htr⟩ :=
    hch G T L V H P p hH hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  exact ⟨P, U, I, h, p, hHs, hsolv, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, hhP, hhM, hI, hU, hUdec,
    hUinf, hUe, hUc, hD, hidx, htr⟩

end CFSG.Quasithin.H13
