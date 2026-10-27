module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open

theorem exists_isPGroup_map_eq {Y : Type*} [Group Y] [Finite Y] (O : Subgroup Y) [O.Normal]
    {X : Subgroup (Y ⧸ O)} (hX : IsPGroup 3 X) :
    ∃ R : Subgroup Y, IsPGroup 3 R ∧ R.map (QuotientGroup.mk' O) = X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hXP⟩ := hX.exists_le_sylow
  obtain ⟨P', hP'⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective O) 3 P
  have hP'' : (P' : Subgroup Y).map (QuotientGroup.mk' O) = (P : Subgroup _) := by
    have := congrArg (fun T : Sylow 3 (Y ⧸ O) => (T : Subgroup (Y ⧸ O))) hP'
    simpa using this
  refine ⟨(P' : Subgroup Y) ⊓ X.comap (QuotientGroup.mk' O), P'.2.to_le inf_le_left, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy.2
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (hP'' ▸ hXP hx : x ∈ (P' : Subgroup Y).map (QuotientGroup.mk' O))
    exact ⟨y, ⟨hy, show (QuotientGroup.mk' O) y ∈ X by rw [hyx]; exact hx⟩, hyx⟩

variable {G : Type} [Group G]

theorem mem_normalizer_of_mk_mem_barM_normalizer {M S : Subgroup G} (hSM : S ≤ M)
    (hS : pCoreOf 2 M ≤ S) {g : G} (hgM : g ∈ M)
    (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  have key : ∀ {g : G} (hgM : g ∈ M), QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∀ {w : G}, w ∈ S → g * w * g⁻¹ ∈ S := by
    intro g hgM hg w hw
    have hwM : w ∈ M := hSM hw
    have hwb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ ∈ barM M S :=
      ⟨⟨w, hwM⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hg _).mp hwb
    have hgwM : g * w * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hwM) (M.inv_mem hgM)
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨g * w * g⁻¹, hgwM⟩ : ↥M) ∈ barM M S := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨g * w * g⁻¹, hgwM⟩ : ↥M) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hwM⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this]
      exact h1
    exact coe_mem_of_mk_mem_barM hS ⟨g * w * g⁻¹, hgwM⟩ h2
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key hgM hg hw, fun hw => ?_⟩
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hg' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g⁻¹, hgM'⟩ ∈
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g⁻¹, hgM'⟩ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact Subgroup.inv_mem _ hg
  have := key hgM' hg' hw
  simpa [mul_assoc] using this

end CFSG.HardMathSupport.Curtis.Coordinator
