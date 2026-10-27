module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109AInputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem asc82Step109A_of (hAO : Asc82Step109AOuter) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hb : Asc82Basic10) : Asc82Step109A := by
  intro G _ _ t L S z K1 K2 hctx hneg
  obtain ⟨g, hgN, hgM, hg2, hgt, hgz⟩ := sec10A_part1 h3 h hb hctx hneg
  obtain ⟨s, hsS, h1, h2, h4⟩ := hAO G t L S z K1 K2 hctx g hgN hgM hg2 hgt hgz
  have hsN : s ∈ normalizer (S : Set G) := Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => S.mul_mem (S.mul_mem hsS hx) (S.inv_mem hsS),
      fun hx => by
        have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
        rw [e]
        exact S.mul_mem (S.mul_mem (S.inv_mem hsS) hx) hsS⟩
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hsS)
  have hsz : s * z = z * s := hctx.central s hsS
  have hsM : s ∈ secM t S L := sec10A_cent_mem_M h3.l36 hctx hsN hst
  refine ⟨g * s,
    { toSec10Ctx := hctx
      norm := ?_
      not_M := ?_
      two := ?_
      swap := ?_
      outer1 := h1
      comm2 := h2
      sq := h4 }⟩
  · exact (normalizer (S : Set G)).mul_mem hgN hsN
  · intro hgs
    apply hgM
    have := (secM t S L).mul_mem hgs ((secM t S L).inv_mem hsM)
    simpa using this
  · have hT : IsPGroup 2 ↥(S ⊔ zpowers g) :=
      IsPGroup.to_sup_of_normal_left' hctx.sylow.2.1 hg2 (Subgroup.zpowers_le.mpr hgN)
    refine hT.to_le (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      (Subgroup.mem_sup_left hsS)
  · have e : (g * s)⁻¹ * t * (g * s) = s⁻¹ * (g⁻¹ * t * g) * s := by group
    rw [e, hgt]
    calc s⁻¹ * (t * z) * s = s⁻¹ * t * s * (s⁻¹ * z * s) := by group
      _ = t * z := by
        have e1 : s⁻¹ * t * s = t := by
          calc s⁻¹ * t * s = s⁻¹ * (t * s) := by group
            _ = s⁻¹ * (s * t) := by rw [hst]
            _ = t := by group
        have e2 : s⁻¹ * z * s = z := by
          calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
            _ = s⁻¹ * (s * z) := by rw [hsz]
            _ = z := by group
        rw [e1, e2]

end CFSG.OddStandard.SmallF3.Omega
