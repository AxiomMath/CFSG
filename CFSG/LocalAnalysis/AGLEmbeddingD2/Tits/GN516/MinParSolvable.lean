module

public import CFSG.Quasithin.Background.B6Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem isSolvable_kerIn {G : Type} [Group G] [Finite G] {H R M : Subgroup G}
    (h : MinParabolic H R M) : Group.IsSolvable ↥(kerIn M H) := by
  have hsyl := h.isSylowTwoOf_pCoreOf_kerIn
  have hQJ : pCoreOf 2 H ≤ kerIn M H := hsyl.1
  have hNn : ((pCoreOf 2 H).subgroupOf (kerIn M H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2
      (h.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have h2 : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf (kerIn M H)) :=
    (hsyl.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
  have hnil := h2.isNilpotent
  have : Group.IsSolvable ↥((pCoreOf 2 H).subgroupOf (kerIn M H)) := inferInstance
  have hodd : Odd (Nat.card (↥(kerIn M H) ⧸ (pCoreOf 2 H).subgroupOf (kerIn M H))) := by
    rw [Nat.odd_iff]
    have hrel := hsyl.2.2
    rcases Nat.even_or_odd (Nat.card (↥(kerIn M H) ⧸ (pCoreOf 2 H).subgroupOf (kerIn M H)))
      with he | ho
    · exact absurd (even_iff_two_dvd.1 he) hrel
    · exact Nat.odd_iff.1 ho
  have hq : Group.IsSolvable (↥(kerIn M H) ⧸ (pCoreOf 2 H).subgroupOf (kerIn M H)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((pCoreOf 2 H).subgroupOf (kerIn M H)).subtype
    (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf (kerIn M H))) (by simp)

section Map

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_minParabolic_of_map {K S M : Subgroup G} (hmin : MinParabolic K S M)
    {Q : Type*} [Group Q] (π : G →* Q) (hsolv : Group.IsSolvable ↥(K.map π))
    (hne : K.map π ≠ S.map π) : Group.IsSolvable ↥K := by
  have hYH : K ⊓ π.ker ≤ K := inf_le_left
  have hYn : K ≤ Subgroup.normalizer ((K ⊓ π.ker : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨K.mul_mem (K.mul_mem hh hx1) (K.inv_mem hh), π.normal_ker.conj_mem x hx2 h⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have := K.mul_mem (K.mul_mem (K.inv_mem hh) hx1) hh
        simpa [mul_assoc] using this
      · have := π.normal_ker.conj_mem _ hx2 h⁻¹
        simpa [mul_assoc] using this
  rcases hmin.le_kerIn_or_twoResidual_le hYH hYn with hY | hY
  · have hJ := isSolvable_kerIn hmin
    let g : ↥K →* ↥(K.map π) := (π.comp K.subtype).codRestrict _ (fun h => ⟨h, h.2, rfl⟩)
    let f : ↥(kerIn M K) →* ↥K := Subgroup.inclusion hmin.kerIn_le_H
    refine Group.isSolvable_of_ker_le_range f g fun h hh => ?_
    have h1 : π (h : G) = 1 := congrArg Subtype.val hh
    exact ⟨⟨h, hY ⟨h.2, h1⟩⟩, rfl⟩
  · exfalso
    apply hne
    apply le_antisymm
    · rw [← sup_twoResidual_eq hmin.isSylow, Subgroup.map_sup]
      refine sup_le le_rfl ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [show π x = 1 from (hY hx).2]
      exact Subgroup.one_mem _
    · exact Subgroup.map_mono hmin.isSylow.1

end Map

end CFSG.AGLEmbeddingD2.Tits.GN516
