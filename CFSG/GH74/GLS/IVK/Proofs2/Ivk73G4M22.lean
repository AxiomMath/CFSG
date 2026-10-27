module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvOut
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem mathieu_inv_centralizer_card {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {c s : ℕ}
    (h : OddStandard.MathieuInnerStatement G [(s, c)]) :
    ∀ u ∈ G, orderOf u = 2 → Nat.card (centralizerIn G u) = c := by
  obtain ⟨⟨recs, hshape, hvalid⟩, -⟩ := h
  obtain ⟨hrecs, -, hcover⟩ := hvalid
  intro u hu hu2
  obtain ⟨r, hr, hur⟩ := hcover u hu hu2
  have hrc : r.centralizerOrder = c := by
    have hm : (r.classSize, r.centralizerOrder) ∈ OddStandard.recordShape recs := List.mem_map_of_mem hr
    rw [hshape] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    exact hm.2
  rw [GHInv.card_centralizerIn_eq_of_mem_conjClass G hur]
  exact (hrecs r hr).2.2.2.1.trans hrc

theorem ivk73_m22 :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := hL
  have e' : ↥L ≃* NativeSporadic.M22 := e
  have hcent : ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 384 :=
    mathieu_inv_centralizer_card
      (OddStandard.ctuc_mathieu_inner_involution_centralizer_odd_core_trivial.2.2.1)
  have hOutM : Nat.card (Outer NativeSporadic.M22) ≤ 2 :=
    GHInv.card_outer_le_of_card_mulAut_le (Sporadic.Schreier.m22_center_eq_bot')
      (by simpa using Sporadic.Schreier.m22_mulAut_card)
  have hOut : ∀ E : Subgroup (Outer ↥L), (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ 1 := by
    apply GHInv.hOut_of_card_outer_le_two
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact hOutM
  refine h.false_of_inner_solvable hOut fun y hy2 hy1 M hM => ?_
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hcardC : Nat.card ↥(centralizer ({y} : Set ↥L)) = 384 := by
    have h1 := GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M22 e' y
    rw [h1]
    exact hcent _ (e' y).2 (by rw [Subgroup.orderOf_coe]; exact hord)
  have hdvd : Nat.card ↥M ∣ 2 ^ 7 * 3 ^ 1 := by
    have h1 : Nat.card ↥M ∣ Nat.card ↥(centralizer ({y} : Set ↥L)) :=
      Subgroup.card_dvd_of_le hM
    rw [hcardC] at h1
    exact h1.trans (by norm_num)
  exact GHInv.isSolvable_of_card_dvd_two_pow_mul_three_pow hdvd

end CFSG.GH74.GLS.IVK
