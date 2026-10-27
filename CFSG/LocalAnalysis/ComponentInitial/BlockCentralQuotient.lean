module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

theorem isComponentOf_map_of_injective {G H : Type*} [Group G] [Group H] {K C : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K C) (φ : G →* H) (hφ : Function.Injective φ) :
    CFSG.Assembly.IsComponentOf (K.map φ) (C.map φ) := by
  obtain ⟨hKC, hs, hq⟩ := hK
  refine ⟨Subgroup.map_mono hKC, ?_, ?_⟩
  · have := Components.chain_map φ ((AssemblyBPredicates.isSubnormal_iff_open K C).1 hs)
    exact (AssemblyBPredicates.isSubnormal_iff_open _ _).2 this
  · rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    exact (isQuasisimple_congr (K.equivMapOfInjective φ hφ)).1 hq

theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (f : G ≃* H)
    (u : G) : (centralizer ({u} : Set G)).map f.toMonoidHom = centralizer ({f u} : Set H) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff]
    change f y * f u = f u * f y
    rw [← map_mul, hy, map_mul]
  · intro hx
    refine ⟨f.symm x, ?_, by simp⟩
    rw [mem_centralizer_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx]

theorem card_quotient_center_eq_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P) : Nat.card (P ⧸ center P) = Nat.card (Q ⧸ center Q) := by
  have hc : center P = ((QuotientGroup.mk' (center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp hf))).toEquiv

variable {G : Type*} [Group G]

theorem card_centerQuotientImage_quotient_center {K L : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple K) (hKL : K ≤ L) :
    Nat.card (centerQuotientImage L K ⧸ center (centerQuotientImage L K)) =
      Nat.card (K ⧸ center K) := by
  have hP : Group.IsPerfect K := Group.isPerfect_def.2 hq.1
  let ψ : K →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp (inclusion hKL)
  have hrange : ψ.range = centerQuotientImage L K := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let f : K →* centerQuotientImage L K :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hker : f.ker ≤ center K := by
    intro k hk
    have hk' : ψ k = 1 := by
      have h1 : f k = 1 := hk
      have h2 : ((f k : centerQuotientImage L K) : L ⧸ center L) = ψ k := rfl
      rw [← h2, h1]
      rfl
    have hkZ : inclusion hKL k ∈ center L := (QuotientGroup.eq_one_iff _).1 hk'
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (show ((g * k : K) : G) = ((k * g : K) : G) from
      congrArg (fun z : L => (z : G)) (mem_center_iff.1 hkZ (inclusion hKL g)))
  exact (card_quotient_center_eq_of_surjective hP f hf hker).symm

theorem card_conjSub_quotient_center (g : G) (J : Subgroup G) :
    Nat.card (conjSub g J ⧸ center (conjSub g J)) = Nat.card (J ⧸ center J) := by
  let e : J ≃* conjSub g J := J.equivMapOfInjective _ (MulAut.conj g).injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv).symm

theorem card_centerQuotientImage_block [Finite G] {J L K : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (hK : K ∈ block J) (hKL : K ≤ L) :
    Nat.card (centerQuotientImage L K ⧸ center (centerQuotientImage L K)) =
      Nat.card (J ⧸ center J) := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hK
  rw [card_centerQuotientImage_quotient_center (isQuasisimple_of_isConjOf hq ⟨g, rfl⟩) hKL]
  exact card_conjSub_quotient_center g J

end CFSG.LocalAnalysis.ComponentInitial
