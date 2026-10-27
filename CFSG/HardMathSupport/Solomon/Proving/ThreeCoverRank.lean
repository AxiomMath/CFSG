module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Suz
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.HardMathSupport.Timmesfeld.SporadicRank

theorem threeCover_Suz_rank
    (L : Type) [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group)
    (hZ3 : Nat.card (Subgroup.center L) = 3) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, hn, hA, hF⟩ := exists_spec_Suz
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  let f : L ⧸ Subgroup.center L ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz := e.trans b.symm
  have hZ6 : Nat.card (Subgroup.center L) ∣ 6 := by rw [hZ3]; norm_num
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ3]
  have hlow := lower_of_cover hq f hZ6 h3 D hA hF
  omega

theorem threeCover_lower_of_datum {s : TauCeti.SporadicName} {X : Type} [Group X]
    (b : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (D : CFSG.AGLEmbedding.ModuleSpec X 3)
    (hA : D.NoAlt) (hF : D.NoFun) (L : Type) [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hZ6 : Nat.card (Subgroup.center L) ∣ 6) (h3 : 3 ∣ Nat.card (Subgroup.center L)) :
    D.n + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨b⟩ := b
  exact lower_of_cover hq (e.trans b.symm) hZ6 h3 D hA hF

theorem threeCover_Fi22_rank
    (L : Type) [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group)
    (hZ3 : Nat.card (Subgroup.center L) = 3) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowData_Fi22
  have hZ6 : Nat.card (Subgroup.center L) ∣ 6 := by rw [hZ3]; norm_num
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ3]
  have hb : Nonempty (CFSG.Blueprint.NativeSporadic.Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) :=
    CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hlow : D.n + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
    refine threeCover_lower_of_datum (s := .Fi22) (X := CFSG.Blueprint.NativeSporadic.Fi22) ?_ D hA hF L hq e hZ6 h3
    exact hb
  omega

theorem threeCover_Fi24_rank
    (L : Type) [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)
    (hZ3 : Nat.card (Subgroup.center L) = 3) :
    8 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨D, P, hn, hA, hF, -⟩ := sylowCover_Fi24
  have hZ6 : Nat.card (Subgroup.center L) ∣ 6 := by rw [hZ3]; norm_num
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ3]
  have hb : Nonempty (CFSG.Blueprint.NativeSporadic.Fi24prime ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :=
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hlow : D.n + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
    refine threeCover_lower_of_datum (s := .Fi24Prime) (X := CFSG.Blueprint.NativeSporadic.Fi24prime) ?_ D hA hF L hq e hZ6 h3
    exact hb
  omega

end CFSG.HardMathSupport.Solomon.Proving
