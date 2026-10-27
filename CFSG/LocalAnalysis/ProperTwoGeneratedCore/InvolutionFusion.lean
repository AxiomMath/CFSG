module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem involution_fusion_of_huppert
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (ht : orderOf t = 2) {g : G}
    (hchain : HuppertCentricConjugationDecomposition (S : Subgroup G)
      (HuppertExtremal S) (Subgroup.zpowers t) g) :
    ∃ h ∈ H, h⁻¹ * t * h = g⁻¹ * t * g := by
  induction hchain with
  | one => exact ⟨1, H.one_mem, rfl⟩
  | @tail g h U hprev _hU hUS hcur hh _hcentric ih =>
      obtain ⟨z, hzH, hzt⟩ := ih
      have htU : g⁻¹ * t * g ∈ U := hcur
        (Subgroup.mem_map.mpr ⟨t, Subgroup.mem_zpowers t, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
      by_cases hrank : 2 ≤ pRank 2 U
      · have hhH : h ∈ H :=
          normalizer_le_overgroup S H 2 hSH hcore U (S.isPGroup'.to_le hUS)
            (hUS.trans hSH) hrank hh
        refine ⟨z * h, H.mul_mem hzH hhH, ?_⟩
        calc
          (z * h)⁻¹ * t * (z * h) = h⁻¹ * (z⁻¹ * t * z) * h := by group
          _ = h⁻¹ * (g⁻¹ * t * g) * h := by rw [hzt]
          _ = (g * h)⁻¹ * t * (g * h) := by group
      · have htconj : orderOf (g⁻¹ * t * g) = 2 := by
          simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj g⁻¹).orderOf_eq t
        have hfixed := rank_one_twoGroup_normalizer_fixes_involution U
          (S.isPGroup'.to_le hUS) (by omega) _ htU htconj h hh
        refine ⟨z, hzH, ?_⟩
        calc
          z⁻¹ * t * z = g⁻¹ * t * g := hzt
          _ = h⁻¹ * (g⁻¹ * t * g) * h := hfixed.symm
          _ = (g * h)⁻¹ * t * (g * h) := by group

theorem sylow_involution_fusion
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (htS : t ∈ (S : Subgroup G)) (ht : orderOf t = 2)
    (g : G) (hg : g⁻¹ * t * g ∈ (S : Subgroup G)) :
    ∃ h ∈ H, h⁻¹ * t * h = g⁻¹ * t * g := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdomain : Subgroup.zpowers t ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr htS
  have himage : rightConjugate (Subgroup.zpowers t) g ≤ (S : Subgroup G) := by
    change (Subgroup.zpowers t).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr (by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg)
  exact involution_fusion_of_huppert S H hSH hcore t ht
    (HuppertExtremal.centric_conjugation_decomposition S hdomain himage)

theorem involution_conjugate_into_sylow
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2) :
    ∃ u ∈ H, u⁻¹ * t * u ∈ (S : Subgroup G) := by
  have hcyclic : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using ht
  obtain ⟨u, hu⟩ := pGroup_conjugate_into_sylow_within_overgroup 2 Nat.prime_two S H hSH
    (Subgroup.zpowers t) hcyclic (Subgroup.zpowers_le.mpr htH)
  refine ⟨(u : G)⁻¹, H.inv_mem u.property, ?_⟩
  have htimage := hu (Subgroup.mem_map_of_mem
    (MulAut.conj (u : G)).toMonoidHom (Subgroup.mem_zpowers t))
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using htimage

theorem two_generated_core_controls_involution_fusion
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (g : G) (hgH : g⁻¹ * t * g ∈ H) :
    ∃ h ∈ H, h⁻¹ * t * h = g⁻¹ * t * g := by
  obtain ⟨u, huH, huS⟩ := involution_conjugate_into_sylow S H hSH t htH ht
  have htconj : orderOf (g⁻¹ * t * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj g⁻¹).orderOf_eq t
  obtain ⟨v, hvH, hvS⟩ := involution_conjugate_into_sylow S H hSH _ hgH htconj
  have htu : orderOf (u⁻¹ * t * u) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj u⁻¹).orderOf_eq t
  have hadjusted : (u⁻¹ * g * v)⁻¹ * (u⁻¹ * t * u) * (u⁻¹ * g * v) ∈
      (S : Subgroup G) := by
    convert hvS using 1
    group
  obtain ⟨h, hhH, hh⟩ := sylow_involution_fusion S H hSH hcore _ huS htu
    (u⁻¹ * g * v) hadjusted
  refine ⟨u * h * v⁻¹, H.mul_mem (H.mul_mem huH hhH) (H.inv_mem hvH), ?_⟩
  calc
    (u * h * v⁻¹)⁻¹ * t * (u * h * v⁻¹) = v * (h⁻¹ * (u⁻¹ * t * u) * h) * v⁻¹ := by group
    _ = v * ((u⁻¹ * g * v)⁻¹ * (u⁻¹ * t * u) * (u⁻¹ * g * v)) * v⁻¹ := by rw [hh]
    _ = g⁻¹ * t * g := by group

theorem involution_conjugacy_set_inter_overgroup
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2) :
    {x : G | ∃ g : G, g⁻¹ * t * g = x} ∩ (H : Set G) =
      {x : G | ∃ h ∈ H, h⁻¹ * t * h = x} := by
  ext x
  constructor
  · rintro ⟨⟨g, rfl⟩, hgH⟩
    exact two_generated_core_controls_involution_fusion S H hSH hcore t htH ht g hgH
  · rintro ⟨h, hhH, rfl⟩
    exact ⟨⟨h, rfl⟩, H.mul_mem (H.mul_mem (H.inv_mem hhH) htH) hhH⟩

end CFSG.ProperTwoGeneratedCore
