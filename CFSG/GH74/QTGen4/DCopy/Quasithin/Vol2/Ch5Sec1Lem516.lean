module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_6_cases_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H D : Subgroup G) (n : ℕ), Hyp5_0_1 G T M L n →
    IsCh5Module T L V → IsHStar T M H → Lin2.IsHallTwoPrimeOf D (borelL T L) →
    pCoreOf 2 (D ⊔ H) = ⊥ → Even n → ¬ D ≤ Subgroup.normalizer (T : Set G) →
      (n = 2 ∧ IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∧
          ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        ((n = 2 ∨ n = 4) ∧ IsNatModCh5 L ⁅V, L⁆ n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) ∨
        (n = 2 ∧ IsBarS5 L T V ∧ IsS5ModCh5 L T ⁅V, L⁆ ∧ centerOf H = ⊥) ∨
        (n % 4 = 0 ∧ IsOrthCh5 L V n ∧ ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧
          ∀ Dp Dm : Subgroup G, Dp ≤ D → Dm ≤ D → Nat.card Dp = 2 ^ (n / 2) - 1 →
            Nat.card Dm = 2 ^ (n / 2) + 1 →
              quasithinOmegaOneCenter T ≤ centerOf (Dm ⊔ H) ∧
                (pCoreOf 2 (Dp ⊔ H) ≠ ⊥ ∨ n = 4 ∨ n = 8))

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem not_le_normalizer_T_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58)
    {H D : Subgroup G} (hH : IsHStar T M H) (hO : pCoreOf 2 (D ⊔ H) = ⊥) :
    ¬ D ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hDT
  have hT1 : T ≠ ⊥ := h.T_ne_bot
  have hM₀T : D ⊔ T ≤ Subgroup.normalizer (T : Set G) := sup_le hDT Subgroup.le_normalizer
  have hTO : T ≤ pCoreOf 2 (D ⊔ T) := le_pCoreOf_of_le_normalizer 2 le_sup_right hM₀T h.sylow.1
  have hM₀ : InH T (D ⊔ T) := ⟨le_sup_right, fun h0 => hT1 (le_bot_iff.mp (h0 ▸ hTO))⟩
  obtain ⟨⟨-, -, hu⟩, -⟩ := h.minParabolic_of_isHStar_F4 h331 hH
  have hTS : IsSylowTwoOf T (oTwoUpper H ⊔ T) := h.isSylowTwoOf le_sup_right
  obtain ⟨R₀, hR₀, hR₀T, hR₀n⟩ := theorem311_of_C58 hC58 h.simple h.nonabelian h.qtke h.sylow
    hM₀ hH.1 ⟨_, hu⟩ hT1 le_rfl hTS hM₀T
  have hsup : D ⊔ T ⊔ H = D ⊔ H := by
    rw [sup_assoc, sup_eq_right.mpr hH.1.1]
  rw [hsup] at hR₀n
  have hR₀le : R₀ ≤ D ⊔ H := hR₀T.trans (hH.1.1.trans le_sup_right)
  have := le_pCoreOf_of_le_normalizer 2 hR₀le hR₀n (h.sylow.1.to_le hR₀T)
  rw [hO] at this
  exact hR₀ (le_bot_iff.mp this)

end Hyp5_0_1

theorem stmt5_1_6_of_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (hodd : Stmt5_1_6_odd)
    (hcases : Stmt5_1_6_cases_F4) : Stmt5_1_6_F4 := by
  intro G _ _ T M L V H D n h hV hH hD hO
  have hDT := h.not_le_normalizer_T_F4 h331 hC58 hH hO
  have heven : Even n := by
    by_contra hne
    exact hDT (hodd G T M L D n h hD hne)
  exact ⟨heven, hcases G T M L V H D n h hV hH hD hO heven hDT⟩

end CFSG.Quasithin.H13
