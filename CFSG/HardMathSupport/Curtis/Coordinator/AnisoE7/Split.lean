module

public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.RankThree.PartOne.KLR.FrobTrick

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.Open
open CFSG.HardMathSupport.Lang.TwE6Step3 (exists_fixed_split exists_fixed_split₂
  canonicalRep_conj_mem_rootSpan canonicalRep_inv_conj_mem_rootSpan rootSpan_union')

set_option linter.unusedSectionVars false

section Tools

variable {L : Type} [Field L]

theorem torusGroup_inf_rootSpan_parabolicRoots_E7 (J : Set (Fin Tag.E7.rank)) :
    torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J) =
      supportedTorus Tag.E7 L J := by
  rw [inf_comm, ← subsystemGroup_eq_rootSpan, subsystemGroup_inf_torusGroup_eq_supportedTorus]

end Tools

section Tools

variable {L : Type} [Field L]

theorem map_entrywise_mem_torusGroup [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {h : ModGL Tag.E7 L} (hh : h ∈ torusGroup Tag.E7 L) :
    Units.map (entrywiseHom Fr) h ∈ torusGroup Tag.E7 L := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have := units_map_entrywiseHom_rootDiagUnit_ringEquiv (τ := Tag.E7)
    (RingEquiv.ofBijective Fr hFrb) b
  have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
  rw [h2] at this
  rw [this]
  exact rootDiagUnit_mem_torusGroup _

theorem theta_mem_torusGroup [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {n : ModGL Tag.E7 L} (hn : n ∈ monomialSubgroup Tag.E7 L) {h : ModGL Tag.E7 L}
    (hh : h ∈ torusGroup Tag.E7 L) :
    n * Units.map (entrywiseHom Fr) h * n⁻¹ ∈ torusGroup Tag.E7 L :=
  (Subgroup.mem_normalizer_iff.1 (mem_normalizer_torusGroup_of_mem_monomialSubgroup hn) _).1
    (map_entrywise_mem_torusGroup hFrb hh)

end Tools

section Block

variable {L : Type} [Field L]

theorem theta_mem_rootSpan [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {n : ModGL Tag.E7 L} (hn : n ∈ monomialSubgroup Tag.E7 L) {J : Set (Fin Tag.E7.rank)}
    (hJ : ∀ β ∈ parabolicRoots Tag.E7 J,
      weylQuotientHom Tag.E7 L ⟨n, hn⟩ • β ∈ parabolicRoots Tag.E7 J)
    {g : ModGL Tag.E7 L} (hg : g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J)) :
    n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J) := by
  have h1 : Units.map (entrywiseHom Fr) g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 J) := by
    have h := CFSG.RankThree.PartOne.KLR.map_entrywise_rootSpan (τ := Tag.E7)
      (RingEquiv.ofBijective Fr hFrb) (parabolicRoots Tag.E7 J)
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h
    rw [← h]
    exact ⟨g, hg, rfl⟩
  have hmap := map_conj_rootSpan_of_mem_monomialSubgroup hn
    (S := parabolicRoots Tag.E7 J) (fun γ hγ => hγ.1)
  have h3 : n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈
      rootSpan Tag.E7 L ((fun γ => weylQuotientHom Tag.E7 L ⟨n, hn⟩ • γ) ''
        parabolicRoots Tag.E7 J) := by
    rw [← hmap]
    exact ⟨_, h1, rfl⟩
  exact rootSpan_mono (by rintro _ ⟨γ, hγ, rfl⟩; exact hJ γ hγ) h3

theorem conj_theta_canonicalRep [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    (n : ModGL Tag.E7 L) (v : WeylGroup Tag.E7) (x : ModGL Tag.E7 L) :
    n * Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem Tag.E7) L v * x *
        (canonicalRep (coxeterSystem Tag.E7) L v)⁻¹) * n⁻¹ =
      canonicalRep (coxeterSystem Tag.E7) L v *
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n * canonicalRep (coxeterSystem Tag.E7) L v *
          Units.map (entrywiseHom Fr) x *
          (canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n⁻¹ * canonicalRep (coxeterSystem Tag.E7) L v) *
        (canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ := by
  have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrb) v
  have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
  rw [h2] at h1
  rw [map_mul, map_mul, map_inv, h1]
  group

end Block

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
