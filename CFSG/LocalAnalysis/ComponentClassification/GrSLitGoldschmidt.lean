module

public import CFSG.Goldschmidt75.CorollaryB1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

namespace GoldB1

variable {G : Type} [Group G] [Finite G]

theorem centralizer_fStar_eq_bot (hsF : IsSimpleGroup ↥(GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) :
    centralizer ((GeneralizedFitting.subgroup G : Subgroup G) : Set G) = ⊥ := by
  set F := GeneralizedFitting.subgroup G with hFdef
  set C := centralizer (F : Set G) with hCdef
  have hFn : F.Normal := GeneralizedFitting.normal G
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCF : C ≤ F := GeneralizedFitting.centralizer_le G
  have hnorm : (C.subgroupOf F).Normal := Subgroup.Normal.subgroupOf hCn F
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsF _ hnorm with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.mp (h.mono_right hCF)
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    obtain ⟨a, b, hab⟩ := hnF
    apply hab
    exact Subtype.ext (mem_centralizer_iff.mp (h b.2) (a : G) a.2)

theorem fStar_le_of_normal (hsF : IsSimpleGroup ↥(GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {N : Subgroup G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : GeneralizedFitting.subgroup G ≤ N := by
  set F := GeneralizedFitting.subgroup G with hFdef
  have hFn : F.Normal := GeneralizedFitting.normal G
  have hnorm : ((N ⊓ F).subgroupOf F).Normal := Subgroup.Normal.subgroupOf inferInstance F
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsF _ hnorm with h | h
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h
    have hinf : N ⊓ F = ⊥ := disjoint_self.mp (h.mono_right inf_le_right)
    have hcomm : ⁅N, F⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf N F)
    have hNC : N ≤ centralizer (F : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hFdef, centralizer_fStar_eq_bot hsF hnF] at hNC
    exact hN1 (le_bot_iff.mp hNC)
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact h.trans inf_le_left

end GoldB1

theorem goldschmidtStronglyClosedInput_holds :
    GoldschmidtStronglyClosedInput := by
  intro G _ _ hsF hnF S A hAS hA hsc
  set F := GeneralizedFitting.subgroup G with hFdef
  have hO : CFSG.Open.goldschmidtOddCore G = ⊥ := by
    by_contra hne
    have hFO : F ≤ CFSG.Open.goldschmidtOddCore G :=
      GoldB1.fStar_le_of_normal hsF hnF inferInstance hne
    have hodd : Odd (Nat.card F) :=
      Odd.of_dvd_nat CFSG.Goldschmidt75.odd_card_oddCore (Subgroup.card_dvd_of_le hFO)
    have hsol : Group.IsSolvable F := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hnF
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hB1 := CFSG.Goldschmidt75.corollaryB1 S hAS hsc
  rw [hO, sup_bot_eq] at hB1
  have hD : (CFSG.perfectResidual ↥(centralizer (A : Set G))).map
      (centralizer (A : Set G)).subtype = ⊥ := by
    by_contra hD
    have hFC : F ≤ centralizer (A : Set G) :=
      (GoldB1.fStar_le_of_normal hsF hnF hB1 hD).trans (map_subtype_le _)
    have hAF : A ≤ centralizer (F : Set G) := le_centralizer_iff.mp hFC
    rw [hFdef, GoldB1.centralizer_fStar_eq_bot hsF hnF] at hAF
    exact hA (le_bot_iff.mp hAF)
  have hR : CFSG.perfectResidual ↥(centralizer (A : Set G)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (centralizer (A : Set G)).subtype_injective).mp hD
  exact (CFSG.perfect_residual_characterization (G := ↥(centralizer (A : Set G)))).2.2.2.2.2.mp hR

end CFSG.ComponentClassification.GrSLit
