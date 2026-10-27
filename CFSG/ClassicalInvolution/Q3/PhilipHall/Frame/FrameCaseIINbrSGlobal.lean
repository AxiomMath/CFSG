module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T3 CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D

section Transport

variable {G : Type} [Group G]

theorem aviol_of_aviol_conjSub {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K J' : Subgroup G} {z zM zJ : G} (hz : IsUniqueInvolution K z) (x : G)
    (hv : AViol Ω (conjSub x K) J' zM zJ) :
    zM = x * z * x⁻¹ ∧ AViol Ω K (conjSub x⁻¹ J') z (x⁻¹ * zJ * x) := by
  have h1 := aviol_conj hΩ hv x⁻¹
  rw [conjSub_inv_conjSub, inv_inv] at h1
  have e : x⁻¹ * zM * x = z := (hz.eq h1.hzK).symm
  rw [e] at h1
  refine ⟨?_, h1⟩
  calc zM = x * (x⁻¹ * zM * x) * x⁻¹ := by group
    _ = x * z * x⁻¹ := by rw [e]

theorem alphaOf_closure_pair_conj (x u v : G) :
    alphaOf (Subgroup.closure ({x * u * x⁻¹, x * v * x⁻¹} : Set G)) =
      conjSub x (alphaOf (Subgroup.closure ({u, v} : Set G))) := by
  rw [← conjSub_closure_pair, alphaOf_conjSub]

theorem alphaOf_eq_conjSub_of_aviol {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K J' : Subgroup G} {z zM zJ : G} (hz : IsUniqueInvolution K z) (x : G)
    (hv : AViol Ω (conjSub x K) J' zM zJ) :
    alphaOf (Subgroup.closure ({zM, zJ} : Set G)) =
      conjSub x (alphaOf (Subgroup.closure ({z, x⁻¹ * zJ * x} : Set G))) := by
  obtain ⟨hzM, -⟩ := aviol_of_aviol_conjSub hΩ hz x hv
  have e : x * (x⁻¹ * zJ * x) * x⁻¹ = zJ := by group
  rw [← alphaOf_closure_pair_conj x z (x⁻¹ * zJ * x), e, ← hzM]

theorem pairNormalizers_le_normalizer_alphaOf {K J : Subgroup G} {z t : G} :
    pairNormalizers K J z t ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({z, t} : Set G)) : Set G) := by
  intro a ha
  have hle : pairNormalizers K J z t ≤
      Subgroup.normalizer ((Subgroup.closure ({z, t} : Set G) : Subgroup G) : Set G) :=
    sup_le inf_le_right inf_le_right
  rw [mem_normalizer_iff_conjSub_eq, ← alphaOf_conjSub,
    mem_normalizer_iff_conjSub_eq.mp (hle ha)]

end Transport

section Constancy

variable {G : Type} [Group G] {K J : Subgroup G} {z t : G} {α : Subgroup G}

@[expose] def AlphaConstAt (K : Subgroup G) (z : G) (α : Subgroup G) : Prop :=
  ∀ (J₁ : Subgroup G) (u : G), AViol (CoreAssembly.conjClass K) K J₁ z u →
    alphaOf (Subgroup.closure ({z, u} : Set G)) = α

theorem normalizer_le_normalizer_alphaOf (hΩ : ConjInvariant (CoreAssembly.conjClass K))
    (hz : IsUniqueInvolution K z) (hα : AlphaConstAt K z α)
    (hv : AViol (CoreAssembly.conjClass K) K J z t) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (α : Set G) := by
  intro c hc
  have hcK : conjSub c K = K := mem_normalizer_iff_conjSub_eq.mp hc
  have hcz : c * z * c⁻¹ = z := hz.conj_eq hcK
  have hv' := aviol_conj hΩ hv c
  rw [hcK, hcz] at hv'
  have h1 := alphaOf_closure_pair_conj c z t
  rw [hcz, hα _ _ hv', hα _ _ hv] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr h1.symm

end Constancy

section Global

variable {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z t a g : G} {α : Subgroup G}

theorem mem_normalizer_of_aviol_conjSub {u x : G}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hz : IsUniqueInvolution K z)
    (hα : AlphaConstAt K z α) (hv : AViol (CoreAssembly.conjClass K) K (conjSub x K) z u) :
    x ∈ Subgroup.normalizer (α : Set G) := by
  have hsym := aviol_symm_of_hypOmegaGen hΩ (CoreAssembly.mem_conjClass_self K) hv
  obtain ⟨-, hv'⟩ := aviol_of_aviol_conjSub hΩ.conjInvariant hz x hsym
  have h1 := alphaOf_eq_conjSub_of_aviol hΩ.conjInvariant hz x hsym
  rw [hα _ _ hv', Set.pair_comm, hα _ _ hv] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr h1.symm

theorem exists_mem_normalizer_conjSub_of_aviol {C : Subgroup G} {zB zC y : G}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hz : IsUniqueInvolution K z)
    (hα : AlphaConstAt K z α) (hy : y ∈ Subgroup.normalizer (α : Set G))
    (hv : AViol (CoreAssembly.conjClass K) (conjSub y K) C zB zC) :
    ∃ x ∈ Subgroup.normalizer (α : Set G), conjSub x K = C := by
  obtain ⟨-, hv'⟩ := aviol_of_aviol_conjSub hΩ.conjInvariant hz y hv
  obtain ⟨w, hw⟩ := CoreAssembly.single_class K _ hv'.mem
  have hwα : w ∈ Subgroup.normalizer (α : Set G) :=
    mem_normalizer_of_aviol_conjSub hΩ hz hα (by rw [← hw]; exact hv')
  refine ⟨y * w, Subgroup.mul_mem _ hy hwα, ?_⟩
  rw [conjSub_mul, ← hw, conjSub_conjSub_inv]

theorem FrameIIHyp.twinSet_eq (h : FrameIIHyp K J z t a g) :
    twinSet (CoreAssembly.conjClass K) K = {K, conjSub a J} := by
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨v, Ks, -, -, -, -, htw, -⟩ := exists_hexagon_data3 h.hyp hKΩ h.viol.mem
    h.viol.hzK h.viol.hzJ h.viol.star h.viol.not_nbr h.viol.no_conj
  have hzK' : IsUniqueInvolution (conjSub a J) z := by
    have := h.viol.hzJ.conj a
    rwa [h.haz] at this
  have hmem : conjSub a J ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨h.hyp.conjInvariant a J h.viol.mem, z, h.viol.hzK, hzK'⟩
  rw [htw] at hmem ⊢
  rcases hmem with h1 | h1
  · exact absurd h1 h.hne
  · rw [h1]

theorem FrameIIHyp.exists_mem_normalizer_conjSub_twin (h : FrameIIHyp K J z t a g)
    (hα : AlphaConstAt K z (alphaOf (Subgroup.closure ({z, t} : Set G)))) :
    ∃ x ∈ Subgroup.normalizer ((alphaOf (Subgroup.closure ({z, t} : Set G)) : Subgroup G) :
      Set G), conjSub x K = conjSub a J := by
  obtain ⟨w, hw⟩ := CoreAssembly.single_class K J h.viol.mem
  have hwα := mem_normalizer_of_aviol_conjSub h.hyp h.viol.hzK hα (by rw [← hw]; exact h.viol)
  exact ⟨a * w, Subgroup.mul_mem _ (pairNormalizers_le_normalizer_alphaOf h.ha) hwα, by
    rw [conjSub_mul, ← hw]⟩

theorem FrameIIHyp.exists_mem_normalizer_conjSub (h : FrameIIHyp K J z t a g)
    (hα : AlphaConstAt K z (alphaOf (Subgroup.closure ({z, t} : Set G))))
    {M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) :
    ∃ y ∈ Subgroup.normalizer ((alphaOf (Subgroup.closure ({z, t} : Set G)) : Subgroup G) :
      Set G), conjSub y K = M := by
  have hΩ := h.hyp
  have hz := h.viol.hzK
  have key : ∀ B : Subgroup G, Relation.ReflTransGen (aGraphAdj (CoreAssembly.conjClass K)) K B →
      ∃ y ∈ Subgroup.normalizer ((alphaOf (Subgroup.closure ({z, t} : Set G)) : Subgroup G) :
        Set G), conjSub y K = B := by
    intro B hB
    induction hB with
    | refl => exact ⟨1, Subgroup.one_mem _, conjSub_one K⟩
    | @tail B C _ hBC ih =>
      obtain ⟨y, hy, rfl⟩ := ih
      obtain ⟨hCΩ, hA | hA | ⟨hT, hne⟩⟩ := hBC
      · obtain ⟨zB, zC, hv⟩ := hA
        exact exists_mem_normalizer_conjSub_of_aviol hΩ hz hα hy hv
      · obtain ⟨zC, zB, hv⟩ := hA
        exact exists_mem_normalizer_conjSub_of_aviol hΩ hz hα hy
          (aviol_symm_of_hypOmegaGen hΩ hCΩ hv)
      · have hT' := twinSet_conj hΩ.conjInvariant hT y⁻¹
        rw [conjSub_inv_conjSub, h.twinSet_eq] at hT'
        have hne' : conjSub y⁻¹ C ≠ K := fun e => hne (by
          calc C = conjSub y (conjSub y⁻¹ C) := (conjSub_conjSub_inv y C).symm
            _ = conjSub y K := by rw [e])
        rcases hT' with h1 | h1
        · exact absurd h1 hne'
        · obtain ⟨x, hx, hxK⟩ := h.exists_mem_normalizer_conjSub_twin hα
          refine ⟨y * x, Subgroup.mul_mem _ hy hx, ?_⟩
          rw [conjSub_mul, hxK, ← h1, conjSub_conjSub_inv]
  have hMa : M ∈ aStar (CoreAssembly.conjClass K) K := by rw [h.star]; exact hM
  exact key M hMa

theorem FrameIIHyp.normalizer_alphaOf_eq_top_of_const (h : FrameIIHyp K J z t a g)
    (hα : AlphaConstAt K z (alphaOf (Subgroup.closure ({z, t} : Set G)))) :
    Subgroup.normalizer ((alphaOf (Subgroup.closure ({z, t} : Set G)) : Subgroup G) : Set G) =
      ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hxΩ : conjSub x K ∈ CoreAssembly.conjClass K := ⟨x, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h.exists_mem_normalizer_conjSub hα hxΩ
  have hxy : y⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hyx, conjSub_inv_conjSub]
  have hxy' := normalizer_le_normalizer_alphaOf h.hyp.conjInvariant h.viol.hzK hα h.viol hxy
  have hx : x = y * (y⁻¹ * x) := by group
  rw [hx]
  exact Subgroup.mul_mem _ hy hxy'

end Global

section Main

variable {G : Type} [Group G] [Finite G] [FrameCore G] {K J : Subgroup G} {z t a g : G}

theorem FrameIIHyp.alphaOf_eq_bot_of_const (h : FrameIIHyp K J z t a g)
    (hconst : ∀ (J₁ J₂ : Subgroup G) (u₁ u₂ : G),
      AViol (CoreAssembly.conjClass K) K J₁ z u₁ → AViol (CoreAssembly.conjClass K) K J₂ z u₂ →
        alphaOf (Subgroup.closure ({z, u₁} : Set G)) = alphaOf (Subgroup.closure ({z, u₂} : Set G)))
    (hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({z, t} : Set G))))) :
    ∀ M ∈ CoreAssembly.conjClass K, ∀ (J' : Subgroup G) (zM zJ : G),
      AViol (CoreAssembly.conjClass K) M J' zM zJ →
        alphaOf (Subgroup.closure ({zM, zJ} : Set G)) = ⊥ := by
  have hα : AlphaConstAt K z (alphaOf (Subgroup.closure ({z, t} : Set G))) :=
    fun J₁ u hv => hconst J₁ J u t hv h.viol
  have hnorm : (alphaOf (Subgroup.closure ({z, t} : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer
        ((alphaOf (Subgroup.closure ({z, t} : Set G)) : Subgroup G) : Set G) := by
      rw [h.normalizer_alphaOf_eq_top_of_const hα]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hbot : alphaOf (Subgroup.closure ({z, t} : Set G)) = ⊥ :=
    FrameCore.oddNormal h.nonabelian _ hnorm hodd
  intro M hM J' zM zJ hv
  obtain ⟨x, hx⟩ := CoreAssembly.single_class K M hM
  subst hx
  rw [alphaOf_eq_conjSub_of_aviol h.hyp.conjInvariant h.viol.hzK x hv,
    hα _ _ (aviol_of_aviol_conjSub h.hyp.conjInvariant h.viol.hzK x hv).2, hbot]
  exact Subgroup.map_bot _

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
