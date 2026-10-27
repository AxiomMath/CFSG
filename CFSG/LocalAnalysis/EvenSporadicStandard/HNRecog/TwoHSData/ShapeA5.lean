module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec
public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma natCard_elem2_two : Nat.card (Elem2 2) = 4 := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

theorem isShapeTwoTwoTimesTwoFourA5_of_hom {G : Type} [Group G] (X V S N : Subgroup G)
    (ψ : ↥S →* Equiv.Perm (Fin 5)) (hVX : V ≤ X) (hSX : S ≤ X)
    (hVcen : ∀ v ∈ V, ∀ x ∈ X, x * v = v * x) (hV : Nonempty (↥V ≃* Elem2 2))
    (hVS : ∀ v ∈ V, v ∈ S → v = 1) (hX : Nat.card ↥X = 3840) (hS : Nat.card ↥S = 960)
    (hNS : N ≤ S) (hNker : ∀ (n : G) (h : n ∈ N), ψ ⟨n, hNS h⟩ = 1) (hN : Nat.card ↥N = 16)
    (hNsq : ∀ n ∈ N, n * n = 1) (hrange : Nat.card ↥ψ.range = 60) :
    IsShapeTwoTwoTimesTwoFourA5 ↥X := by
  let V' : Subgroup ↥X := V.subgroupOf X
  let S' : Subgroup ↥X := S.subgroupOf X
  have hVcard : Nat.card ↥V = 4 := by
    obtain ⟨e⟩ := hV
    rw [Nat.card_congr e.toEquiv, natCard_elem2_two]
  have hV'card : Nat.card ↥V' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, hVcard]
  have hS'card : Nat.card ↥S' = 960 := by
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
    exact Subtype.ext (hVS x.1 hxV hxS)
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hcardmul : Nat.card ↥V' * Nat.card ↥S' = Nat.card ↥X := by
    rw [hV'card, hS'card, hX]
  have hsup : V' ⊔ S' = ⊤ :=
    Subgroup.IsComplement'.sup_eq_top
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul (disjoint_iff.mpr hV'S'))
  obtain ⟨eX, _heX⟩ :=
    CFSG.RankThree.CentralExtension.exists_mulEquiv_prod_of_central hV'cen hsup hV'S'
  haveI : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have hNsub_le : N.subgroupOf S ≤ ψ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    simpa using hNker (n : G) hnN
  have hNsub_card : Nat.card ↥(N.subgroupOf S) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv, hN]
  have hker_card : Nat.card ↥ψ.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, hS] at h
    omega
  have hker : ψ.ker = N.subgroupOf S :=
    (Subgroup.eq_of_le_of_card_ge hNsub_le (by omega)).symm
  have hNiso : Nonempty (↥ψ.ker ≃* Elem2 4) := by
    obtain ⟨eN⟩ := nonempty_mulEquiv_elem2 (G := ↥N) 4 (fun g : ↥N => by
      apply Subtype.ext
      exact hNsq (g : G) g.2) (by rw [hN]; norm_num)
    exact ⟨(MulEquiv.subgroupCongr hker).trans
      ((Subgroup.subgroupOfEquivOfLe hNS).trans eN)⟩
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hidx : ψ.range.index = 2 := by
    have h := Subgroup.index_mul_card (H := ψ.range)
    rw [hrange, hcardPerm] at h
    omega
  have hrange_eq : ψ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hSiso : Nonempty (↥S ⧸ ψ.ker ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange_eq)⟩
  obtain ⟨eV⟩ := hV
  refine ⟨↥S, inferInstance, ⟨ψ.ker, inferInstance, hNiso, hSiso⟩, ?_⟩
  exact ⟨eX.symm.trans (MulEquiv.prodCongr
    ((Subgroup.subgroupOfEquivOfLe hVX).trans eV) (Subgroup.subgroupOfEquivOfLe hSX))⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
