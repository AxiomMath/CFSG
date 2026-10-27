module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma natCard_elem2_two : Nat.card (Elem2 2) = 4 := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

theorem isShapeTwoTwoTimesA8_of_hom {G : Type*} [Group G] (X V S : Subgroup G)
    (φ : ↥X →* Equiv.Perm (Fin 8)) (hVX : V ≤ X) (hSX : S ≤ X)
    (hVcen : ∀ v ∈ V, ∀ x ∈ X, x * v = v * x) (hV : Nonempty (↥V ≃* Elem2 2))
    (hVker : ∀ (v : G) (h : v ∈ V), φ ⟨v, hVX h⟩ = 1)
    (hX : Nat.card ↥X = 80640) (hS : Nat.card ↥S = 20160) (hrange : Nat.card ↥φ.range = 20160)
    (hSinj : ∀ (s : G) (h : s ∈ S), φ ⟨s, hSX h⟩ = 1 → s = 1) :
    IsShapeTwoTwoTimesA8 ↥X := by
  have hperm : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hidx : φ.range.index = 2 := by
    have h := Subgroup.index_mul_card (H := φ.range)
    rw [hrange, hperm] at h
    omega
  have hrange_eq : φ.range = alternatingGroup (Fin 8) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  let V' : Subgroup ↥X := V.subgroupOf X
  let S' : Subgroup ↥X := S.subgroupOf X
  have hVcard : Nat.card ↥V = 4 := by
    obtain ⟨e⟩ := hV
    rw [Nat.card_congr e.toEquiv, natCard_elem2_two]
  have hV'card : Nat.card ↥V' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, hVcard]
  have hS'card : Nat.card ↥S' = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS]
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
    refine Subtype.ext (hSinj x.1 hxS ?_)
    have h : (⟨x.1, hSX hxS⟩ : ↥X) = ⟨x.1, hVX hxV⟩ := Subtype.ext rfl
    rw [h]
    exact hVker x.1 hxV
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hcardmul : Nat.card ↥V' * Nat.card ↥S' = Nat.card ↥X := by
    rw [hV'card, hS'card, hX]
  have hsup : V' ⊔ S' = ⊤ :=
    Subgroup.IsComplement'.sup_eq_top
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul (disjoint_iff.mpr hV'S'))
  obtain ⟨eX, _heX⟩ :=
    CFSG.RankThree.CentralExtension.exists_mulEquiv_prod_of_central hV'cen hsup hV'S'
  have hinj_comp : Function.Injective (φ.comp S'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine Subtype.ext (Subtype.ext (hSinj (x.1).1 x.2 ?_))
    have h : (⟨(x.1).1, hSX x.2⟩ : ↥X) = x.1 := Subtype.ext rfl
    rw [h]
    exact hx
  let ψ : ↥S' →* ↥φ.range :=
    (φ.comp S'.subtype).codRestrict φ.range
      (fun x => (MonoidHom.mem_range (f := φ)).mpr ⟨S'.subtype x, rfl⟩)
  have hψinj : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict (φ.comp S'.subtype) φ.range
      (fun x => (MonoidHom.mem_range (f := φ)).mpr ⟨S'.subtype x, rfl⟩)).mpr hinj_comp
  haveI : Finite ↥φ.range := Nat.finite_of_card_ne_zero (by rw [hrange]; norm_num)
  have hcardψ : Nat.card ↥S' = Nat.card ↥φ.range := by rw [hS'card, hrange]
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψinj, hcardψ⟩
  have hS'A8 : ↥S' ≃* alternatingGroup (Fin 8) :=
    (MulEquiv.ofBijective ψ hψbij).trans (MulEquiv.subgroupCongr hrange_eq)
  obtain ⟨eV⟩ := hV
  refine ⟨eX.symm.trans (MulEquiv.prodCongr
    ((Subgroup.subgroupOfEquivOfLe hVX).trans eV) hS'A8)⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
