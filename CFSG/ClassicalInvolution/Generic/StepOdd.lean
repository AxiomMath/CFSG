module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType CFSG.LieType.Universal CFSG.ClassicalInvolution
open scoped MatrixGroups

variable (p f : ℕ) [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem orderOf_mk_oddCore_eq_two {z : Y} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) = 2 := by
  have hnot : z ∉ classicalInvolutionOddCore Y := by
    intro hmem
    have h1 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hz] at h1
    have hodd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card Y
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) ≠ 1 := by
    intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h)
  have h2 : (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) ^ 2 = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  exact orderOf_eq_prime h2 h1

theorem centralizer_map_oddCore {z : Y} (hz : orderOf z = 2) :
    (Subgroup.centralizer ({z} : Set Y)).map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) =
      Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore Y) z} :
        Set (Y ⧸ classicalInvolutionOddCore Y)) := by
  have hA : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; simp)
  have hN : ¬ 2 ∣ Nat.card (classicalInvolutionOddCore Y) := by
    intro h
    have hodd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card Y
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2
    (classicalInvolutionOddCore Y) hN _ hA
  have hC : ∀ {H : Type} [Group H] (w : H),
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup H) : Set H) =
        Subgroup.centralizer ({w} : Set H) := fun w => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [hC, MonoidHom.map_zpowers, hC] at h

theorem oddCore_restriction_ker_odd (L : Subgroup Y) :
    Odd (Nat.card ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L).ker) := by
  have hkernel : ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L).ker =
      ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).domRestrict L).ker := by
    ext x
    change (QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L x = 1 ↔
      QuotientGroup.mk' (classicalInvolutionOddCore Y) (x : Y) = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hkernel]
  apply CFSG.ComponentClassification.OddKernel.odd_card_restriction_kernel
  rw [QuotientGroup.ker_mk']
  exact CFSG.ComponentClassification.OddCore.odd_card Y

variable {p f}

theorem IsClassicalMember.map_oddQuotient {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) :
    IsClassicalMember p f (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) where
  orderOf_eq_two := orderOf_mk_oddCore_eq_two h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))
  subnormal := by
    rw [← centralizer_map_oddCore h.orderOf_eq_two]
    exact CFSG.ComponentClassification.Components.chain_map _ h.subnormal
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv
      ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L)
      (MonoidHom.subgroupMap_surjective _ L) (oddCore_restriction_ker_odd L)).symm.trans e⟩

theorem inClass_oddQuotient {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) :
    InClass p f (oddQuotientFamily Λ) where
  nonempty := hΛ.nonempty.image _
  conjInvariant := conjInvariant_oddQuotientFamily hΛ.conjInvariant
  generated := by
    set π := QuotientGroup.mk' (classicalInvolutionOddCore Y)
    have h : ⨆ M ∈ oddQuotientFamily Λ, M = (⨆ L ∈ Λ, L).map π := by
      refine le_antisymm (iSup₂_le fun M hM => ?_) ?_
      · obtain ⟨L, hL, rfl⟩ := hM
        exact Subgroup.map_mono (le_iSup₂ (f := fun (L : Subgroup Y) (_ : L ∈ Λ) => L) L hL)
      · rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun L hL => ?_
        exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂
          (f := fun (M : Subgroup (Y ⧸ classicalInvolutionOddCore Y))
            (_ : M ∈ oddQuotientFamily Λ) => M) (L.map π) ⟨L, hL, rfl⟩)
    rw [h, hΛ.generated, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  classical := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact ⟨_, hz.map_oddQuotient⟩

end CFSG.ClassicalInvolution.Generic
