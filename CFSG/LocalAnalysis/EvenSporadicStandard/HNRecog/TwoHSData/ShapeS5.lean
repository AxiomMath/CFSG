module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elem2Rec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma natCard_Elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isShapeTwoTwoSixS5_of_hom {G : Type*} [Group G] (X V N : Subgroup G)
    (φ : ↥X →* Equiv.Perm (Fin 5)) (hVN : V ≤ N) (hNX : N ≤ X)
    (hVcen : ∀ v ∈ V, ∀ x ∈ X, x * v = v * x) (hV : Nonempty (↥V ≃* Elem2 2))
    (hNker : ∀ (n : G) (h : n ∈ N), φ ⟨n, hNX h⟩ = 1)
    (hX : Nat.card ↥X = 30720) (hN : Nat.card ↥N = 256) (hrange : Nat.card ↥φ.range = 120)
    (hsq : ∀ n ∈ N, n * n ∈ V) : IsShapeTwoTwoSixS5 ↥X := by
  have hVX : V ≤ X := hVN.trans hNX
  have hcardK : Nat.card ↥φ.ker = 256 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hX, hrange] at h
    omega
  haveI : Finite ↥φ.ker :=
    Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  have hNK : N.subgroupOf X ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    simpa using hNker (n : G) hnN
  have hcardN' : Nat.card ↥(N.subgroupOf X) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hN]
  have hN'eqK : N.subgroupOf X = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hNK (by rw [hcardK, hcardN'])
  have hN'Normal : (N.subgroupOf X).Normal := by
    rw [hN'eqK]; infer_instance
  haveI := hN'Normal
  have hVcenX : V.subgroupOf X ≤ Subgroup.center ↥X := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext
      (hVcen (v : G) (Subgroup.mem_subgroupOf.mp hv) (y : G) y.2)
  have hV'Normal : (V.subgroupOf X).Normal := Subgroup.normal_of_le_center hVcenX
  haveI := hV'Normal
  have hV'N' : V.subgroupOf X ≤ N.subgroupOf X := Subgroup.subgroupOf_mono X hVN
  have hV'iso : Nonempty (↥(V.subgroupOf X) ≃* Elem2 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hVX).trans hV.some⟩
  have hcardV' : Nat.card ↥(V.subgroupOf X) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv,
      Nat.card_congr hV.some.toEquiv, natCard_Elem2 2]
    norm_num
  have hcardV'N' : Nat.card ↥((V.subgroupOf X).subgroupOf (N.subgroupOf X)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'N').toEquiv, hcardV']
  haveI : ((V.subgroupOf X).subgroupOf (N.subgroupOf X)).Normal := inferInstance
  have hcardQ :
      Nat.card (↥(N.subgroupOf X) ⧸ (V.subgroupOf X).subgroupOf (N.subgroupOf X)) = 64 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((V.subgroupOf X).subgroupOf (N.subgroupOf X))
    rw [hcardN', hcardV'N'] at h
    omega
  have hsqQ : ∀ g : ↥(N.subgroupOf X) ⧸ (V.subgroupOf X).subgroupOf (N.subgroupOf X),
      g * g = 1 := by
    intro g
    refine QuotientGroup.induction_on g ?_
    intro n
    rw [← QuotientGroup.mk_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have hnN : ((n : ↥X) : G) ∈ N := Subgroup.mem_subgroupOf.mp n.2
    simpa using hsq ((n : ↥X) : G) hnN
  have hQ : Nonempty (↥(N.subgroupOf X) ⧸ (V.subgroupOf X).subgroupOf (N.subgroupOf X) ≃*
      Elem2 6) :=
    nonempty_mulEquiv_elem2 6 hsqQ (by rw [hcardQ]; norm_num)
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  haveI : Finite ↥φ.range :=
    Nat.finite_of_card_ne_zero (by rw [hrange]; norm_num)
  have hrange_top : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (G := Equiv.Perm (Fin 5)) (H := φ.range) ?_
    rw [hrange, hcardPerm]
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange_top
  have hisoQ : Nonempty (↥X ⧸ N.subgroupOf X ≃* Equiv.Perm (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hN'eqK).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩
  exact ⟨V.subgroupOf X, N.subgroupOf X, hV'Normal, hN'Normal, hV'N', hV'iso, hQ, hisoQ⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
