module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {G : Type} [Group G] [Finite G]

theorem isRigidRankOneComp_conj {x : G} {K : Subgroup G} (h : IsRigidRankOneComp x K) (g : G) :
    IsRigidRankOneComp (g * x * g⁻¹) (cmap g K) :=
  ⟨isPRigid_cmap h.1 g, by rw [pRank_cmap]; exact h.2⟩

omit [Finite G] in
private theorem cmap_injective' (g : G) : Function.Injective (cmap g : Subgroup G → Subgroup G) :=
  fun H H' h => by
    have := congrArg (cmap g⁻¹) h
    rwa [cmap_inv_cancel, cmap_inv_cancel] at this

theorem rrSet_conj (x g : G) :
    {J : Subgroup G | IsRigidRankOneComp (g * x * g⁻¹) J} =
      cmap g '' {K : Subgroup G | IsRigidRankOneComp x K} := by
  ext J
  constructor
  · intro hJ
    refine ⟨cmap g⁻¹ J, ?_, cmap_cancel g J⟩
    have := isRigidRankOneComp_conj hJ g⁻¹
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  · rintro ⟨K, hK, rfl⟩
    exact isRigidRankOneComp_conj hK g

theorem ncard_rr_conj (x g : G) :
    Set.ncard {J : Subgroup G | IsRigidRankOneComp (g * x * g⁻¹) J} =
      Set.ncard {K : Subgroup G | IsRigidRankOneComp x K} := by
  rw [rrSet_conj, Set.ncard_image_of_injective _ (cmap_injective' g)]

@[expose] def Pin (u : G) : Prop := ∃ J : Subgroup G, IsRigidRankOneComp u J ∧ u ∈ J

theorem pin_conj {u v : G} (h : Pin u) (hc : IsConj u v) : Pin v := by
  obtain ⟨J, hJ, huJ⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  refine ⟨cmap c J, isRigidRankOneComp_conj hJ c, mem_cmap.2 ?_⟩
  have e : c⁻¹ * (c * u * c⁻¹) * c = u := by group
  rw [e]; exact huJ

theorem cm_apply (hCM : CM) (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G) {x u : G}
    (hx : orderOf x = 2) (hu : orderOf u = 2) (hux : u ∈ centralizer ({x} : Set G))
    (hconj : IsConj x u) (hsec : ∀ K, IsRigidRankOneComp x K → u ∈ cSec K) :
    ∃ J : Subgroup G → Subgroup G, Set.InjOn J {K | IsRigidRankOneComp x K} ∧
      (∀ K, IsRigidRankOneComp x K → IsRigidRankOneComp u (J K)) ∧
      {J' : Subgroup G | IsRigidRankOneComp u J'} = J '' {K | IsRigidRankOneComp x K} ∧
      ∀ K, IsRigidRankOneComp x K → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P K →
        (∀ p ∈ P, u * p = p * u) → P ≤ J K := by
  classical
  let Rf : Finset (Subgroup G) :=
    (Set.toFinite {K : Subgroup G | IsRigidRankOneComp x K}).toFinset
  have hRf : ∀ K, K ∈ Rf ↔ IsRigidRankOneComp x K := fun K => by simp [Rf]
  have hRset : (Rf : Set (Subgroup G)) = {K | IsRigidRankOneComp x K} := by
    ext K; exact hRf K
  have hcard : Set.ncard {J : Subgroup G | IsRigidRankOneComp u J} ≤ Rf.card := by
    obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
    rw [ncard_rr_conj, ← hRset, Set.ncard_coe_finset]
  obtain ⟨J, h1, h2, h3', h4⟩ :=
    hCM G hG h3 x u hx hu hux Rf hRf (fun K hK => hsec K ((hRf K).1 hK)) hcard
  rw [hRset] at h1 h3'
  exact ⟨J, h1, fun K hK => h2 K ((hRf K).2 hK), h3', fun K hK => h4 K ((hRf K).2 hK)⟩

end CFSG.GH74.GLS.Bg.Iii2
