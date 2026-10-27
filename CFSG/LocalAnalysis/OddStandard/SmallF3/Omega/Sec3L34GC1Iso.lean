module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Orb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Img
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Pg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1FQ

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_img_equiv {E J : Subgroup G} (hJE : J ≤ E)
    (hcen : ∀ j ∈ J, (∀ e ∈ E, e * j = j * e) ↔ ∀ g ∈ J, g * j = j * g) :
    Nonempty ((↥J ⧸ center ↥J) ≃* ↥(l34gImg E J)) := by
  have hJN : J ≤ normalizer (E : Set G) := hJE.trans Subgroup.le_normalizer
  let ψ : ↥J →* ↥(l34gImg E J) :=
    (E.normalizerMonoidHom.comp (Subgroup.inclusion hJN)).codRestrict (l34gImg E J)
      fun j => mem_l34gImg.2 ⟨j.1, hJN j.2, j.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    intro a
    obtain ⟨g, hg, hgJ, hga⟩ := mem_l34gImg.1 a.2
    exact ⟨⟨g, hgJ⟩, Subtype.ext hga⟩
  have hker : ψ.ker = center ↥J := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have h1 : E.normalizerMonoidHom ⟨j.1, hJN j.2⟩ = 1 := congrArg Subtype.val h
      have h2 := (l34gAct_eq_one_iff (hJN j.2)).1 h1
      have h3 := (hcen j.1 j.2).1 fun e he => (h2 e he).symm
      exact Subtype.ext (h3 g.1 g.2)
    · intro h
      refine Subtype.ext ?_
      have h3 : ∀ g ∈ J, g * j.1 = j.1 * g := fun g hg => congrArg Subtype.val (h ⟨g, hg⟩)
      have h2 := (hcen j.1 j.2).2 h3
      exact (l34gAct_eq_one_iff (hJN j.2)).2 fun e he => (h2 e he).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

variable {u x : G} {K : Subgroup G} {𝒪 : Set (Subgroup G)}

theorem L34GOrb.img_simple [Finite G] (hO : L34GOrb u x K 𝒪) {J : Subgroup G} (hJ : J ∈ 𝒪) :
    SimpleFStarQuotient ↥(l34gImg (sSup 𝒪) J) := by
  obtain ⟨e⟩ := l34g_img_equiv (le_sSup hJ) fun j hj => hO.central_iff hJ hj
  exact l34g_simpleFStar_of_mulEquiv e (l34g_simpleFStar_of_inFStar (hO.inFStar J hJ))

theorem L34GOrb.img_le [Finite G] (hO : L34GOrb u x K 𝒪) {J J' : Subgroup G} (hJ : J ∈ 𝒪)
    (hJ' : J' ∈ 𝒪) (h : l34gImg (sSup 𝒪) J ≤ l34gImg (sSup 𝒪) J') : J ≤ J' := by
  refine l34g_perfect_le_of_central (le_sSup hJ) (le_sSup hJ') (hO.perfect_member hJ) ?_
  intro g hg
  have hgN : g ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (le_sSup hJ hg)
  obtain ⟨g', hg'N, hg'J', hαeq⟩ := mem_l34gImg.1 (h (mem_l34gImg.2 ⟨g, hgN, hg, rfl⟩))
  refine ⟨g', hg'J', ?_⟩
  have hgg'N : g * g'⁻¹ ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    (normalizer ((sSup 𝒪 : Subgroup G) : Set G)).mul_mem hgN
      ((normalizer ((sSup 𝒪 : Subgroup G) : Set G)).inv_mem hg'N)
  have hgg : (sSup 𝒪).normalizerMonoidHom ⟨g * g'⁻¹, hgg'N⟩ = 1 := by
    have hsub : (⟨g * g'⁻¹, hgg'N⟩ : normalizer ((sSup 𝒪 : Subgroup G) : Set G)) =
        ⟨g, hgN⟩ * ⟨g', hg'N⟩⁻¹ := rfl
    rw [hsub, map_mul, map_inv, hαeq, mul_inv_cancel]
  exact (l34gAct_eq_one_iff hgg'N).1 hgg

end CFSG.OddStandard.SmallF3.Omega
