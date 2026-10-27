module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem isUniqueM_of_le_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) {X : Subgroup G}
    (hX : IsTwoLocal X) (hLT : L ⊔ T ≤ X) : IsUniqueM X M := by
  have hU := h.isUniqueM_F4 h331
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hX
  have hM'eq : M' = M := hU.2 M' ⟨hM', hLT.trans hle⟩
  refine ⟨⟨hU.1.1, hM'eq ▸ hle⟩, fun M'' hM'' => hU.2 M'' ⟨hM''.1, hLT.trans hM''.2⟩⟩

theorem lemma_5_1_2_one_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hV : IsCh5Module T L V)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) ∧
      IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M ∧
      IsUniqueM (Subgroup.normalizer (baum T : Set G)) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hCR : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    h.centralizer_eq_pCoreOf hV
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := hCR ▸ inf_le_left
  have hJR : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := hCR ▸ le_inf hJT hJ
  have hJeq : thompsonJ T = thompsonJ (pCoreOf 2 (L ⊔ T)) := thompsonJ_eq_of_le hJR hRT
  have hVT : V ≤ T := (le_pCoreOf_of_isCh5Module hV).trans hRT
  have hVe : IsElemAbelian 2 V := hV.isTwoReducedIn.2.2.1
  have hBeq : baum T = baum (pCoreOf 2 (L ⊔ T)) := by
    rw [← hCR]
    exact baum_eq_baum_centralizer hVe hVT (le_inf hJT hJ)
  have hXN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 (L ⊔ T)
  have hXJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [hJeq]
    exact hXN.trans (normalizer_le_normalizer_thompsonJ _)
  have hXB : L ⊔ T ≤ Subgroup.normalizer (baum T : Set G) := by
    rw [hBeq]
    exact hXN.trans (normalizer_le_normalizer_baum _)
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hJne : thompsonJ T ≠ ⊥ := thompsonJ_ne_bot_of hT2 h.T_ne_bot
  have hBne : baum T ≠ ⊥ := fun hb => hJne (le_bot_iff.mp (hb ▸ B2F.thompsonJ_le_baum T))
  refine ⟨le_inf (hJT.trans h.T_le) hJ, hXJ, hXB, ?_, ?_⟩
  · exact h.isUniqueM_of_le_F4 h331 (isTwoLocal_normalizer (hT2.to_le hJT) hJne) hXJ
  · exact h.isUniqueM_of_le_F4 h331 (isTwoLocal_normalizer (hT2.to_le inf_le_left) hBne) hXB

end Hyp5_0_1

theorem stmt5_1_2_of_F4 (h331 : Stmt3_3_1_F4) (hFF : Stmt5_1_2_FF) : Stmt5_1_2_F4 := by
  intro G _ _ T M L V n h hV
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl (h.lemma_5_1_2_one_F4 h331 hV hJ)
  · have hVJ : ⁅V, thompsonJ T⁆ ≠ ⊥ := by
      intro hb
      apply hJ
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
      exact Subgroup.le_centralizer_iff.mp hb
    rcases hFF G T M L V n h hV hVJ with h2 | ⟨h2, hs, hb, h5⟩
    · exact Or.inr (Or.inl ⟨hVJ, h2⟩)
    · exact Or.inr (Or.inr ⟨hVJ, h2, hs, hb, h5⟩)

end CFSG.Quasithin.H13
