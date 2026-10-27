module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4EIn
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4TA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Res614TitsCore_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
    K₁ ∈ cComp M₁ → IsTits (ModO2 K₁) → ¬ K₁ ≤ M →
    X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    X ≤ K₁ → T ≤ Subgroup.normalizer (K₁ : Set G) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ K₁ : Subgroup G) : Set G) →
    pCoreOf 2 (X ⊔ (T ⊓ K₁)) ≤
      thompsonJ T ⊔ centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (K₁ : Set G)) K₁ →
    False

theorem res614Tits_of_F4 (h331 : Stmt3_3_1_F4) (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4)
    (h37 : A37ForSQTK) (hB : TitsBasicFact) (hO5 : TitsOver5Fact) (hWC : TitsWCFact)
    (hcore : Res614TitsCore_F4) : Res614Tits_F4 := by
  intro G _ _ T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
    hXK₁ hXK₀ hnot
  obtain ⟨-, hK₁q, hZ⟩ := hB _ htits
  obtain ⟨hXK, hTK, hK₀, hJX, hJK₁, hTM₁, hsylM₁, -⟩ := tits614_setup_F4 h331 h512 h513 h37 h
    horth hM₁ hCM₁ hK₁ hK₁q hK₁M hXL hXM₁ hX2 hX5 hXn hTX hXK₁ hXK₀ hnot
  rw [hK₀] at hnot
  exact hcore G T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
    hXK hTK hnot (pCoreOf_le_of_tits614 hO5 hWC htits hZ hTK
      (B6.isSylowTwoOf_mono hsylM₁ le_sup_right (sup_le (le_of_mem_cComp hK₁) hTM₁))
      hXK hTX hX5 hJX hJK₁)

end CFSG.Quasithin.H13
