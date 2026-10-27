module

public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem nonempty_mulEquiv_prod_of_central {G : Type*} [Group G] [Finite G] (X V S : Subgroup G)
    (hVX : V ≤ X) (hSX : S ≤ X) (hVcen : ∀ v ∈ V, ∀ x ∈ X, x * v = v * x)
    (hVS : ∀ v ∈ V, v ∈ S → v = 1) (hX : Nat.card ↥X = Nat.card ↥V * Nat.card ↥S) :
    Nonempty (↥X ≃* ↥V × ↥S) := by
  let V' : Subgroup ↥X := V.subgroupOf X
  let S' : Subgroup ↥X := S.subgroupOf X
  have hV'card : Nat.card ↥V' = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv
  have hS'card : Nat.card ↥S' = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  have hV'cen : V' ≤ center ↥X := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hVcen v.1 hv x.1 x.2)
  have hV'S' : V' ⊓ S' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxS⟩ := hx
    exact Subtype.ext (hVS x.1 hxV hxS)
  have hcardmul : Nat.card ↥V' * Nat.card ↥S' = Nat.card ↥X := by
    rw [hV'card, hS'card, hX]
  have hsup : V' ⊔ S' = ⊤ :=
    Subgroup.IsComplement'.sup_eq_top
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul (disjoint_iff.mpr hV'S'))
  obtain ⟨eX, _heX⟩ :=
    CFSG.RankThree.CentralExtension.exists_mulEquiv_prod_of_central hV'cen hsup hV'S'
  exact ⟨eX.symm.trans (MulEquiv.prodCongr (Subgroup.subgroupOfEquivOfLe hVX)
    (Subgroup.subgroupOfEquivOfLe hSX))⟩

theorem nonempty_mulEquiv_alternating_five {A : Type*} [Group A] (ψ : A →* Equiv.Perm (Fin 5))
    (hA : Nat.card A = 60) (hψ : Nat.card ↥ψ.range = 60) :
    Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hidx : ψ.range.index = 2 := by
    have h := Subgroup.index_mul_card (H := ψ.range)
    rw [hψ, hperm] at h
    omega
  have hrange_eq : ψ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hbij : Function.Bijective ψ.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card ψ.rangeRestrict).mpr
      ⟨ψ.rangeRestrict_surjective, by rw [hA, hψ]⟩
  exact ⟨(MulEquiv.ofBijective ψ.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hrange_eq)⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
