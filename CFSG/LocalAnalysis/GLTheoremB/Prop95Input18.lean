module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18Claim
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Normalizes
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem input18_isPGroup_zpowers {p : ℕ} {Y : Type*} [Group Y] {x : Y} (hx : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx)

theorem input18Two_holds :
    ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
      GLAPPrimeCore p X = ⊥ → ∀ d : X, d ^ p = 1 →
        ∀ H : Subgroup X, H ≤ Subgroup.centralizer ({d} : Set X) →
          (∀ c ∈ Subgroup.centralizer ({d} : Set X), ∀ h ∈ H, c * h * c⁻¹ ∈ H) →
          IsPGroup 2 H →
          ∀ K : Subgroup X, GLAPComponent p ⊤ K → H ≤ Subgroup.normalizer (K : Set X) := by
  intro X _ _ _ p hp hp2 hO d hd H hHC hHn hH2 K hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hKc : IsComponentOf K ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent hO hK
  have hB : IsPGroup p (Subgroup.zpowers d) := input18_isPGroup_zpowers hd
  have hCB : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup X) : Set X) =
      Subgroup.centralizer ({d} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHle : H ≤ pCoreOf 2 (Subgroup.centralizer ((Subgroup.zpowers d : Subgroup X) : Set X)) := by
    rw [hCB]
    exact Input18.le_pCoreOf_of_normal hHC hHn hH2
  have hfin := Input18.claim_card hp2 hO _ (Subgroup.zpowers d) hB rfl K hKc
  exact hHle.trans hfin

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
