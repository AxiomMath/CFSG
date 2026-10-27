module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerB3OGeom
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MModel
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

open CFSG.Open TauCeti.QuadraticMap QuadraticMap Module
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RankTwoClassical

noncomputable section

local notation "Ω[" Q "]" => ⁅orthogonalGroup Q, orthogonalGroup Q⁆

theorem geom7_hyp {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hdim : finrank K V = 7) (hnd : (polarBilin Q).Nondegenerate)
    (P : Subgroup ↥Ω[Q]) (hP : Nat.card P = 27)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ F : Subgroup ↥Ω[Q], F ≤ P ∧ Nat.card F = 9 ∧
      ∃ H : Subgroup ↥Ω[Q],
        (∀ h ∈ H, ∀ f ∈ F, h * f = f * h) ∧
        (∀ g : ↥Ω[Q], (∀ f ∈ F, g * f = f * g) → ∀ h ∈ H, g * h * g⁻¹ ∈ H) ∧
        CFSG.Open.IsQuasisimple H ∧ 3 ∣ Nat.card (H ⧸ Subgroup.center H) ∧
        (∀ h ∈ H, h ∈ (scalars K V).subgroupOf Ω[Q] → h = 1) := by
  have hG₀O : Ω[Q] ≤ orthogonalGroup Q := commutator_le_self _
  have hP'G : P.map Ω[Q].subtype ≤ Ω[Q] := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hP'card : Nat.card (P.map Ω[Q].subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (Ω[Q]).subtype_injective, hP]
  have hexp' : ∀ x ∈ P.map Ω[Q].subtype, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (hexp x hx)
    simpa using this
  have hcomm' : ∀ x ∈ P.map Ω[Q].subtype,
      ∀ y ∈ P.map Ω[Q].subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcomm x hx y hy)
  obtain ⟨F, hFP, hF9, Hv, hHvle, hHvcomm, hHvnorm, hHvq, hHv3, w, hw0, hwfix⟩ :=
    geometry7 h2 h3 hdim hnd (P.map Ω[Q].subtype)
      (hP'G.trans hG₀O) hP'card hexp' hcomm'
  have hFG : F ≤ Ω[Q] := hFP.trans hP'G
  refine ⟨F.subgroupOf Ω[Q], ?_, ?_, Hv.subgroupOf Ω[Q], ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hFP hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFG).toEquiv, hF9]
  · intro h hh f hf
    rw [Subgroup.mem_subgroupOf] at hh hf
    exact Subtype.ext (hHvcomm h.1 hh f.1 hf)
  · intro g hg h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have hgF : ∀ f ∈ F, g.1 * f = f * g.1 := by
      intro f hf
      have := hg ⟨f, hFG hf⟩ (by rw [Subgroup.mem_subgroupOf]; exact hf)
      exact congrArg Subtype.val this
    have := hHvnorm g.1 (hG₀O g.2) hgF h.1 hh
    simpa using this
  · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv
      (Subgroup.subgroupOfEquivOfLe hHvle).symm hHvq
  · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv
      (Subgroup.subgroupOfEquivOfLe hHvle).symm]
    exact hHv3
  · intro h hh hZ
    rw [Subgroup.mem_subgroupOf] at hh hZ
    obtain ⟨c, hc⟩ := mem_scalars.1 hZ
    have hcw : c • w = w := by rw [← hc w]; exact hwfix h.1 hh
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, hcw, one_smul, sub_self]
      rcases smul_eq_zero.1 this with h' | h'
      · exact sub_eq_zero.1 h'
      · exact absurd h' hw0
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc v, hc1, one_smul]
    rfl

theorem kerConcl_odd3 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 3 K))))
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  have hQ₀ : ⇑(quadOdd 3 K) = StatedQuadOdd 3 K := coe_quadOdd 3 K
  have hdim : finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    simp
  have hnd := nondegenerate_polarBilin_quadOdd 3 K h2
  haveI : Finite (Fin 3 ⊕ Fin 3 ⊕ Unit → K) := inferInstance
  haveI : Finite ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :=
    Finite.of_injective (fun f => (f : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →
      (Fin 3 ⊕ Fin 3 ⊕ Unit → K))) DFunLike.coe_injective
  have hv₀ : (quadOdd 3 K) (Pi.single (Sum.inr (Sum.inr ())) 1) = 1 := by
    rw [quadOdd_apply]
    simp
  refine CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv
    (projEquiv (quadOdd 3 K) hQ₀) E ?_
  refine kerConcl_of_central_quotient
    ((scalars K (Fin 3 ⊕ Fin 3 ⊕ Unit → K)).subgroupOf
      ⁅orthogonalGroup (quadOdd 3 K), orthogonalGroup (quadOdd 3 K)⁆)
    (fun z hz g => Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.1 hz) g.1))
    (fun z hz => Subtype.ext (scalar_sq_one hv₀ (commutator_le_self _ z.2)
      (Subgroup.mem_subgroupOf.1 hz)))
    (fun P hP hexp hcomm => geom7_hyp h2 h3 hdim hnd P hP hexp hcomm) _
    (CFSG.Open.IsElemAbelian.map hE _) ?_
  have hinj : Function.Injective (projEquiv (quadOdd 3 K) hQ₀).toMonoidHom :=
    (projEquiv (quadOdd 3 K) hQ₀).injective
  rw [Subgroup.card_map_of_injective hinj, hc]

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

end
