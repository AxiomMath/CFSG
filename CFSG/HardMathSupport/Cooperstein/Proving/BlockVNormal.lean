module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.AGLEmbedding (blockV)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_blockV (S L : Subgroup G) :
    S ≤ Subgroup.normalizer ((blockV S L : Subgroup G) : Set G) :=
  fun _ hs =>
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
      ((le_sup_right : S ≤ L ⊔ S) hs)

theorem conj_mem_commutator_of_normalizes {V L : Subgroup G} {h : G}
    (hV : h ∈ Subgroup.normalizer (V : Set G)) (hL : h ∈ Subgroup.normalizer (L : Set G)) :
    ∀ x ∈ ⁅V, L⁆, h * x * h⁻¹ ∈ ⁅V, L⁆ := by
  intro x hx
  have hle : ⁅V, L⁆ ≤ (⁅V, L⁆).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    show h * ⁅v, l⁆ * h⁻¹ ∈ ⁅V, L⁆
    rw [show h * ⁅v, l⁆ * h⁻¹ = ⁅h * v * h⁻¹, h * l * h⁻¹⁆ by
      simp only [commutatorElement_def]; group]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hV v).1 hv)
      ((Subgroup.mem_normalizer_iff.1 hL l).1 hl)
  exact hle hx

theorem mem_normalizer_commutator {V L : Subgroup G} {h : G}
    (hV : h ∈ Subgroup.normalizer (V : Set G)) (hL : h ∈ Subgroup.normalizer (L : Set G)) :
    h ∈ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_commutator_of_normalizes hV hL y hy,
    fun hy => ?_⟩
  have := conj_mem_commutator_of_normalizes ((Subgroup.normalizer (V : Set G)).inv_mem hV)
    ((Subgroup.normalizer (L : Set G)).inv_mem hL) _ hy
  rw [show h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y by group] at this
  exact this

end CFSG.HardMathSupport.Cooperstein.Proving

end
