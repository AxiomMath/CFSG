module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem conj_mem_inf_of_barHom {G : Type} [Group G] {X S L : Subgroup G}
    (hQ : pCoreOf 2 X ≤ S) {x : ↥X} (hxL : (x : G) ∈ L)
    (hx : barHom X x ∈ Subgroup.normalizer (barM X (S ⊓ L) : Set _))
    {r : G} (hr : r ∈ S ⊓ L) (hrX : r ∈ X) : (x : G) * r * (x : G)⁻¹ ∈ S ⊓ L := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hx (barHom X ⟨r, hrX⟩)).mp
    (barHom_mem_barM (X := X) (Y := S ⊓ L) (x := ⟨r, hrX⟩) hr)
  have h2 : barHom X x * barHom X ⟨r, hrX⟩ * (barHom X x)⁻¹ =
      barHom X (x * ⟨r, hrX⟩ * x⁻¹) := by simp
  rw [h2] at h1
  have hmono : barM X (S ⊓ L) ≤ barM X S := fun γ hγ => by
    obtain ⟨z, hz, rfl⟩ := mem_barM_iff.mp hγ
    exact barHom_mem_barM hz.1
  refine ⟨mem_of_barHom_mem hQ (hmono h1), ?_⟩
  exact L.mul_mem (L.mul_mem hxL hr.2) (L.inv_mem hxL)

end CFSG.HardMathSupport.Cooperstein.StructureLie
