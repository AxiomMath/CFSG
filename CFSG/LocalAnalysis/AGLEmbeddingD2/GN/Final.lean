module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem center_eq_bot_and_quotient_of_mulEquiv_alternatingGroup {Y : Type*} [Group Y] {n : ℕ}
    (hn : 4 ≤ n) (e : Y ≃* alternatingGroup (Fin n)) :
    Subgroup.center Y = ⊥ ∧ Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) := by
  have hZ : Subgroup.center Y = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by simpa using hn)] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  exact ⟨hZ, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem classical_or_alt_of_gnYComponent
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂) {L : Subgroup (X ⧸ gnC T)}
    (hY : GNYComponent T C₁ C₂ L) :
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) ∨
      ∃ n : ℕ, (n = 7 ∨ 8 < n) ∧
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)) := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  rcases CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.gn_ffConclusion hFF X T hX L hY.1 hJ with
    hcl | ⟨m, hm5, he⟩
  · exact Or.inl hcl
  rcases (by omega : m = 5 ∨ m = 6 ∨ m = 8 ∨ m = 7 ∨ 8 < m) with h | h | h | h | h
  · exact Or.inl (Or.inr (Or.inl ⟨m, Or.inl h, he⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨m, Or.inr (Or.inl h), he⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨m, Or.inr (Or.inr h), he⟩))
  · exact Or.inr ⟨m, Or.inl h, he⟩
  · exact Or.inr ⟨m, Or.inr h, he⟩

end CFSG.AGLEmbeddingD2.GN
