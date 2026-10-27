module

public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation
public import CFSG.LieType.Chevalley.GraphFixedSchreier

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem unipotentPairAut_outer_surjective
    [Finite K] :
    Function.Surjective ((QuotientGroup.mk' (inner (adjointGroup τ K))).comp
      (unipotentPairAut τ K).subtype) := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  have hopp := (exceptional_ordinary_Sylow_opposition τ K (ringChar K) w₀ hw₀).2.2.2.2.2
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ q
  obtain ⟨c, β, hU, hV, rfl⟩ := hopp α
  refine ⟨⟨β, ⟨hU, hV⟩⟩, ?_⟩
  have hc : MulAut.conj c ∈ inner (adjointGroup τ K) := ⟨c, rfl⟩
  change QuotientGroup.mk' _ β = QuotientGroup.mk' _ (MulAut.conj c * β)
  rw [map_mul, QuotientGroup.mk'_apply _ (MulAut.conj c), (QuotientGroup.eq_one_iff _).2 hc,
    one_mul]

theorem derivedSeries_outer_eq_bot_of_le_ker
    [Finite K] {G : Type*} [Group G] {d : ℕ}
    (φ : unipotentPairAut τ K →* G) (hker : derivedSeries φ.ker 2 = ⊥)
    (hd : derivedSeries (unipotentPairAut τ K) d ≤ φ.ker) :
    derivedSeries (Outer (adjointGroup τ K)) (d + 2) = ⊥ := by
  have h2 := derivedSeries_add_le_map hd 2
  rw [hker, Subgroup.map_bot, le_bot_iff] at h2
  rw [← map_derivedSeries_eq unipotentPairAut_outer_surjective, h2, Subgroup.map_bot]

theorem exceptional_E_pinned_model_Schreier
    (K : Type) [Field K] [Finite K] :
    derivedSeries (Outer (adjointGroup Tag.E6 K)) 3 = ⊥ ∧
      derivedSeries (Outer (adjointGroup Tag.E7 K)) 2 = ⊥ ∧
      derivedSeries (Outer (adjointGroup Tag.E8 K)) 2 = ⊥ := by
  obtain ⟨-, hE6, hE7, hE8⟩ := exceptional_E_intrinsic_diagram_permutation K
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, φ, hφ, -, -, -, hker⟩ := exceptional_ordinary_intrinsic_simple_pairs Tag.E6 K
    have hd : derivedSeries (unipotentPairAut Tag.E6 K) 1 ≤ φ.ker := by
      rw [derivedSeries_one, _root_.commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      rcases hE6 a a.2 (φ a) (hφ a) with ha | ha <;>
        rcases hE6 b b.2 (φ b) (hφ b) with hb | hb <;> rw [ha, hb] <;>
          first | exact (Commute.one_left _).eq | exact (Commute.one_right _).eq
    exact derivedSeries_outer_eq_bot_of_le_ker φ hker hd
  · obtain ⟨-, φ, hφ, -, -, -, hker⟩ := exceptional_ordinary_intrinsic_simple_pairs Tag.E7 K
    have hd : derivedSeries (unipotentPairAut Tag.E7 K) 0 ≤ φ.ker := by
      rw [derivedSeries_zero]
      intro a _
      exact hE7 a a.2 (φ a) (hφ a)
    exact derivedSeries_outer_eq_bot_of_le_ker φ hker hd
  · obtain ⟨-, φ, hφ, -, -, -, hker⟩ := exceptional_ordinary_intrinsic_simple_pairs Tag.E8 K
    have hd : derivedSeries (unipotentPairAut Tag.E8 K) 0 ≤ φ.ker := by
      rw [derivedSeries_zero]
      intro a _
      exact hE8 a a.2 (φ a) (hφ a)
    exact derivedSeries_outer_eq_bot_of_le_ker φ hker hd

end CFSG.LieType.Chevalley
