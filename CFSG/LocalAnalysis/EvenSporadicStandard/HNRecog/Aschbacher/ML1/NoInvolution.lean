module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.A5Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreHyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.ML1

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

private lemma centralizer_map_eq_inf_range {H G : Type*} [Group H] [Group G]
    (ι : H →* G) (hι : Function.Injective ι) (s : H) :
    (Subgroup.centralizer ({s} : Set H)).map ι =
      Subgroup.centralizer ({ι s} : Set G) ⊓ ι.range := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : y * s = s * y := by
      simpa only [Subgroup.mem_centralizer_singleton_iff] using hy
    refine ⟨?_, ⟨y, hyx⟩⟩
    change x ∈ Subgroup.centralizer ({ι s} : Set G)
    rw [← hyx, Subgroup.mem_centralizer_singleton_iff]
    simpa only [← map_mul, hy']
  · rintro ⟨hx, y, hyx⟩
    rw [Subgroup.mem_map]
    refine ⟨y, ?_, hyx⟩
    change x ∈ Subgroup.centralizer ({ι s} : Set G) at hx
    have hx' : x * ι s = ι s * x := by
      simpa only [Subgroup.mem_centralizer_singleton_iff] using hx
    rw [← hyx] at hx'
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    simpa only [map_mul] using hx'

private noncomputable def centralizerInfRangeEquiv {H G : Type*} [Group H] [Group G]
    (ι : H →* G) (hι : Function.Injective ι) (s : H) :
    ↥(Subgroup.centralizer ({ι s} : Set G) ⊓ ι.range) ≃* Subgroup.centralizer ({s} : Set H) :=
  ((Subgroup.equivMapOfInjective (Subgroup.centralizer ({s} : Set H)) ι hι).trans
    (MulEquiv.subgroupCongr (centralizer_map_eq_inf_range ι hι s))).symm

theorem AschbacherHyp.sq_ne_one_of_innerInv (hC : AschbacherHyp C Q) (e : C ⧸ Q ≃* A5WrTwo)
    (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
    (hθs : Function.Surjective θ)
    (hθb : ∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = e (QuotientGroup.mk (l : C)))
    (l : ↥(commutator C)) (hl : InnerInv (θ l)) : l ^ 2 ≠ 1 := by
  intro h2
  have ht2 : (l : C) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, h2]
    rfl
  let ι : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* C ⧸ Q :=
    ((e.symm : A5WrTwo ≃* C ⧸ Q) : A5WrTwo →* C ⧸ Q).comp A5WrTwo.baseEmb
  have hι : Function.Injective ι := by
    intro x y h
    apply A5WrTwo.baseEmb_injective
    exact (EquivLike.injective e.symm) h
  have hιθ : ∀ l' : ↥(commutator C),
      ι (θ l') = QuotientGroup.mk (l' : C) := by
    intro l'
    have h := congrArg (fun x => e.symm x) (hθb l')
    simpa [ι, MonoidHom.comp_apply] using h
  have hrange : (commutator C).map (QuotientGroup.mk' Q) = ι.range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨θ ⟨y, hy⟩, ?_⟩
      rw [← hyx]
      simpa using hιθ ⟨y, hy⟩
    · rintro ⟨g, hgx⟩
      rw [Subgroup.mem_map]
      obtain ⟨l', hl'⟩ := hθs g
      refine ⟨(l' : C), l'.2, ?_⟩
      rw [QuotientGroup.mk'_apply, ← hgx, ← hιθ l', hl']
  have hno := hC.no_involution (l : C) l.2 ht2
  obtain ⟨a, ha1, ha2, hθ | hθ⟩ := hl
  · have hιθl : ι (a, 1) = QuotientGroup.mk (l : C) := by
      have h := hιθ l
      rwa [hθ] at h
    obtain ⟨e_inl⟩ := nonempty_mulEquiv_centralizer_inl ha1 ha2
    refine hno ⟨?_⟩
    rw [← hιθl, hrange]
    exact (centralizerInfRangeEquiv ι hι (a, 1)).trans e_inl
  · have hιθl : ι (1, a) = QuotientGroup.mk (l : C) := by
      have h := hιθ l
      rwa [hθ] at h
    obtain ⟨e_inr⟩ := nonempty_mulEquiv_centralizer_inr ha1 ha2
    refine hno ⟨?_⟩
    rw [← hιθl, hrange]
    exact (centralizerInfRangeEquiv ι hι (1, a)).trans e_inr

end CFSG.EvenSporadicStandard.HNRecog
