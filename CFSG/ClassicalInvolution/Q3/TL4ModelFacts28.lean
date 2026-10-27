module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscFusionR8
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def Model117 : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≤ 7 → ∀ β : MulAut ↥((AE.aeSub n).map (AE.mkQ n)),
    (∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      ∃ (α' : Finset (Fin n)) (h' : α'.card = 4) (b' : Bool),
        ((AE.memBar α h b).subgroupOf ((AE.aeSub n).map (AE.mkQ n))).map β.toMonoidHom =
          (AE.memBar α' h' b').subgroupOf ((AE.aeSub n).map (AE.mkQ n))) →
      ∃ x : AE.AEQ n, ∀ g : ↥((AE.aeSub n).map (AE.mkQ n)), ((β g : _) : AE.AEQ n) = x * g * x⁻¹

@[expose] def Model117Pair : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≤ 7 → ∀ (α : Finset (Fin n)) (h : α.card = 4) (x : AE.AEQ n),
    IsPGroup 3 (Subgroup.zpowers x) →
    x ∈ Subgroup.normalizer ((AE.memBar α h true : Subgroup (AE.AEQ n)) : Set (AE.AEQ n)) →
    x ∈ Subgroup.normalizer ((AE.memBar α h false : Subgroup (AE.AEQ n)) : Set (AE.AEQ n)) →
    (∀ k ∈ AE.memBar α h false, x * k = k * x) → ∀ k ∈ AE.memBar α h true, x * k = k * x

end CFSG.ClassicalInvolution.Q3.TL4
