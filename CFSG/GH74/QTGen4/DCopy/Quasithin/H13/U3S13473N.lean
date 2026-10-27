module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

@[expose] def Stmt13473NonSolv_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : A6.Setting134 G T L V)
    (H₁ H₂ Y₂ Y : Subgroup G),
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
    Hyp1347 T H₁ H₂ → oTwoRes H₂ = l2Of S → Concl1347iii T H₁ H₂ →
    InH T (H₁ ⊔ H₂) → ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) →
    Y₂ ≤ H₁ ⊔ H₂ → H₁ ⊔ H₂ ≤ normalizer (Y₂ : Set G) → oTwoRes Y₂ = Y₂ →
    (∀ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G) →
      ∀ w ∈ v0Of T H₁ H₂, y * w * y⁻¹ = w → w = 1) →
    (∃ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G)) →
    quasithinOmegaOneCenter T ≤ v0Of T H₁ H₂ →
    Y₂ ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G) → T.relIndex (Y₂ ⊔ T) = 3 →
    quasithinO2QuotientIso (Y₂ ⊔ T) (Perm (Fin 3)) → ¬ Y₂ ≤ normalizer (L : Set G) →
    Y = (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T) →
    (L₁Of L (fsuV1 T V) ⊔ T) ⊓ (Y₂ ⊔ T) = T →
    F6.IsGoldschmidtTripleIn Y (L₁Of L (fsuV1 T V) ⊔ T) (Y₂ ⊔ T) →
    InH T Y → ¬ Y ≤ normalizer (L : Set G) →
    IsTwoReducedIn Y (VZ T Y) → Y ⊓ centralizer (VZ T Y : Set G) = pCoreOf 2 Y →
    ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ = L₁Of L (fsuV1 T V) →
    ¬ thompsonJ T ≤ pCoreOf 2 Y →
    (∀ Q : Subgroup G, IsPGroup 2 ↥Q → Q ≤ T → L₁Of L (fsuV1 T V) ≤ normalizer (Q : Set G) →
      ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V), y * l * y⁻¹ * l⁻¹ ∈ Q) →
    ¬ Group.IsSolvable ↥Y → False

end CFSG.Quasithin.H13.U3
