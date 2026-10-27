module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.EmptyFaithful.T1521SCutComp
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem res614TitsCore_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (T M L V M₁ K₁ X : Subgroup G),
      Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
      K₁ ∈ cComp M₁ → IsTits (ModO2 K₁) → ¬ K₁ ≤ M →
      X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
      ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
      X ≤ K₁ → T ≤ Subgroup.normalizer (K₁ : Set G) →
      ¬ X ≤ Subgroup.normalizer ((T ⊓ K₁ : Subgroup G) : Set G) →
      pCoreOf 2 (X ⊔ (T ⊓ K₁)) ≤
        thompsonJ T ⊔ centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (K₁ : Set G)) K₁ →
      False := by
  intro G _ _ hG T M L V M₁ K₁ X h _ hM₁ hC _ hK₁ htits _
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hd := modO2_dvd_of_cComp_maxTwoLocal hG h.qtke.2.1 P hM₁ hC hK₁
  rw [CFSG.Quasithin.T1521SCut.card_isTits htits] at hd
  omega

end CFSG.GH74.QTGen4
