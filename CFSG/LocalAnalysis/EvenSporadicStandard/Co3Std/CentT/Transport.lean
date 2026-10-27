module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem CentFacts.of_mulEquiv {D D' : Type} [Group D] [Group D'] (e : D ≃* D')
    (h : CentFacts D') : CentFacts D := by
  obtain ⟨N', hN'n, hsmall, ⟨S', hS'N', hS'p, hS'cyc⟩, hprime, hbig⟩ := h.core
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id D' := by
    ext x; simp
  have hcomp' : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D := by
    ext x; simp
  have hSN : (S'.map e.symm.toMonoidHom).map e.toMonoidHom = S' := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]; exact h.not_dvd
  · refine ⟨N'.map e.symm.toMonoidHom, hN'n.map e.symm.toMonoidHom e.symm.surjective,
      ?_, ?_, ?_, ?_⟩
    · intro R _ _ hR f
      let iso := Subgroup.equivMapOfInjective N' e.symm.toMonoidHom e.symm.injective
      have hf : f.comp iso.toMonoidHom = 1 := hsmall R hR (f.comp iso.toMonoidHom)
      refine MonoidHom.ext fun x => ?_
      obtain ⟨y, rfl⟩ := iso.surjective x
      simpa only [MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom]
        using DFunLike.congr_fun hf y
    · refine ⟨S'.map e.symm.toMonoidHom, Subgroup.map_mono hS'N',
        hS'p.map e.symm.toMonoidHom, ?_⟩
      intro M hM hcyc
      have hMle : M.map e.toMonoidHom ≤ S' := by
        rw [← hSN]; exact Subgroup.map_mono hM
      have hcyc' : IsCyclic ↥(M.map e.toMonoidHom) :=
        (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective).isCyclic.mp hcyc
      have hres := hS'cyc (M.map e.toMonoidHom) hMle hcyc'
      rw [← hSN,
        Subgroup.relIndex_map_map_of_injective M (S'.map e.symm.toMonoidHom) e.injective] at hres
      exact hres
    · rwa [Subgroup.card_map_of_injective (K := N') e.symm.injective]
    · intro M hMn hMcard
      have hM'n : (M.map e.toMonoidHom).Normal := hMn.map e.toMonoidHom e.surjective
      have hcardM' : Nat.card (M.map e.toMonoidHom) = Nat.card M :=
        Subgroup.card_map_of_injective (K := M) e.injective
      have hle := hbig (M.map e.toMonoidHom) hM'n (by rw [hcardM']; exact hMcard)
      have hmap : (M.map e.toMonoidHom).map e.symm.toMonoidHom = M := by
        rw [Subgroup.map_map, hcomp', Subgroup.map_id]
      rw [← hmap]
      exact Subgroup.map_mono hle

theorem nonempty_centralizer_subtype_equiv {G : Type} [Group G] (H : Subgroup G) (w : ↥H) :
    Nonempty (↥(centralizer ({w} : Set ↥H)) ≃* ↥(centralizer ({(w : G)} : Set G) ⊓ H)) := by
  refine ⟨(Subgroup.equivMapOfInjective (centralizer ({w} : Set ↥H)) H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr ?_)⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg (fun z : ↥H => (z : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hy)), y.2⟩
  · intro hx
    obtain ⟨hxc, hxH⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxc)), rfl⟩

theorem CentFacts.of_centralizer_inf {G : Type} [Group G] (H : Subgroup G) (w : ↥H)
    (h : CentFacts ↥(centralizer ({(w : G)} : Set G) ⊓ H)) :
    CentFacts ↥(centralizer ({w} : Set ↥H)) := by
  obtain ⟨e⟩ := nonempty_centralizer_subtype_equiv H w
  exact CentFacts.of_mulEquiv e h

end CFSG.EvenSporadicStandard.Co3Std.CentT
