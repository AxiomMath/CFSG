module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem schur_tail {m : ℕ} (hm : 1 ≤ m) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (G : ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃+ ((Fin m ⊕ Fin m → K) × (Fin 2 → K)))
    (σ : K ≃+* K) (hG : ∀ (a : K) (v : (Fin m ⊕ Fin m → K) × (Fin 2 → K)), G (a • v) = σ a • G v)
    (μ : K)
    (hGQ : ∀ v, quadTail m (minusTailForm K b c) (G v) =
      μ * σ (quadTail m (minusTailForm K b c) v))
    (hcomm : ∀ g ∈ orthDerived (quadTail m (minusTailForm K b c)), ∀ v, G (g v) = g (G v)) :
    (∀ a : K, σ a = a) ∧ ∃ a : K, a ≠ 0 ∧ ∀ v, G v = a • v := by
  set Q := quadTail m (minusTailForm K b c) with hQdef
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  have hfr : finrank K ((Fin m ⊕ Fin m → K) × (Fin 2 → K)) = 2 * m + 2 := by
    rw [finrank_tailSpace, finrank_fin_two_fun]
  have hT3 : 3 ≤ finrank K (⊤ : Submodule K ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) := by
    rw [finrank_top, hfr]
    omega
  have hTnd : (polarBilin (Q.comp
      (⊤ : Submodule K ((Fin m ⊕ Fin m → K) × (Fin 2 → K))).subtype)).Nondegenerate := by
    constructor
    · intro x hx
      exact Subtype.ext (eq_zero_of_polar_eq_zero hQ fun y => hx ⟨y, Submodule.mem_top⟩)
    · intro y hy
      refine Subtype.ext (eq_zero_of_polar_eq_zero hQ fun x => ?_)
      rw [polar_comm]
      exact hy ⟨x, Submodule.mem_top⟩
  have hsing : ∃ e ∈ (⊤ : Submodule K ((Fin m ⊕ Fin m → K) × (Fin 2 → K))), e ≠ 0 ∧ Q e = 0 := by
    refine ⟨hypVec K (Fin 2 → K) (.inl ⟨0, hm⟩), Submodule.mem_top, ?_, quadTail_hypVec _⟩
    intro h
    have := congrFun (congrArg Prod.fst h) (.inl ⟨0, hm⟩)
    simp [hypVec] at this
  have hM : ElementaryMapsMem Q ⊤ := elementaryMapsMem_of_regular hTnd hT3 fun hK hd4 U hU => by
    by_contra hcon
    push Not at hcon
    have hm1 : m = 1 := by
      rw [finrank_top, hfr] at hd4
      omega
    subst hm1
    obtain ⟨u, hu, hu0⟩ := exists_minusTail_ne_zero (b := b) (c := c) hirr
      (U.map (⊤ : Submodule K ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K))).subtype)
      (by rw [Submodule.finrank_map_subtype_eq]; exact hU)
    obtain ⟨u', hu', rfl⟩ := hu
    exact hu0 (hcon u' hu')
  have hcomm' : ∀ g ∈ supportedDerived Q ⊤, ∀ v, G (g v) = g (G v) := fun g hg v =>
    hcomm g (CFSG.StandardType.LayerCores.OrthRegular.supportedDerived_top_le hg) v
  obtain ⟨hσ, a, ha, hGa⟩ := scalar_restriction_of_commute G σ μ hGQ hcomm' hQ hTnd hT3 hsing hM hG
  exact ⟨hσ, a, ha, fun v => hGa v Submodule.mem_top⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
