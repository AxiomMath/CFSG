module

public import CFSG.GH74.GLS.C3.Layer2.ModelFusion
public import CFSG.GH74.GLS.C3.Layer2.LocalIso

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem approxTo_of_config_67
    (h : IsAConfig n x K T Q S a) (hn : n = 6 ∨ n = 7)
    (hG : IsSimpleGroup G) (hnab : ∃ u w : G, u * w ≠ w * u)
    (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t)
    (hW2 : ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2)
    (hCv : ∃ v' : alternatingGroup (Fin (n + 4)), orderOf v' = 2 ∧
      numMoved (v' : Equiv.Perm (Fin (n + 4))) = 8 ∧
      Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
        ↥(centralizer ({v'} : Set (alternatingGroup (Fin (n + 4))))))) :
    IsApproxTo G (alternatingGroup (Fin (n + 4))) := by
  have hn' : NeZero n := ⟨by rcases hn with rfl | rfl <;> norm_num⟩
  obtain ⟨ι, hι1, hιQ, hιT⟩ := h.exists_equiv_Fgrp_T0 hn hnt
  let c : Coord h := ⟨ι, hι1, hιQ, hιT⟩
  have hM := c.modelIso hn hW2
  obtain ⟨Sg, S', φ, hcl, hφ⟩ := fusion_of_modelIso h c hn hG hnab hM
  obtain ⟨⟨x', hx'o, hx'n⟩, -⟩ := exists_involution_numMoved n hn
  obtain ⟨v', hv'o, hv'n, Cv⟩ := hCv
  have hn11 : n + 4 ≤ 11 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨e⟩ := fgrp_equiv_centralizer n hn x' hx'o hx'n
  have Cx : Nonempty (↥(centralizer ({x} : Set G)) ≃*
      ↥(centralizer ({x'} : Set (alternatingGroup (Fin (n + 4)))))) := ⟨ι.trans e⟩
  have hconj4 : ∀ g : alternatingGroup (Fin (n + 4)), orderOf g = 2 →
      (IsConj g x' ↔ numMoved (g : Equiv.Perm (Fin (n + 4))) = 4) := by
    intro g hg
    constructor
    · intro hc
      rw [numMoved_eq_of_isConj_alternating (n + 4) hc, hx'n]
    · intro h4
      exact isConj_alternating_of_numMoved_eq (n + 4) g x' hg hx'o (by rw [h4, hx'n])
  have hcl' : ∀ u : ↥(S' : Subgroup (alternatingGroup (Fin (n + 4)))), orderOf u = 2 →
      IsConj (u : alternatingGroup (Fin (n + 4))) x' ∨
        IsConj (u : alternatingGroup (Fin (n + 4))) v' := by
    intro u hu
    have hu2 : orderOf (u : alternatingGroup (Fin (n + 4))) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hu
    rcases numMoved_eq_of_involution_alternating (n + 4) hn11 _ hu2 with h4 | h8
    · exact Or.inl (isConj_alternating_of_numMoved_eq (n + 4) _ _ hu2 hx'o (by rw [h4, hx'n]))
    · exact Or.inr (isConj_alternating_of_numMoved_eq (n + 4) _ _ hu2 hv'o (by rw [h8, hv'n]))
  have hφ' : ∀ u : ↥(Sg : Subgroup G), orderOf u = 2 →
      (IsConj (u : G) x ↔ IsConj (φ u : alternatingGroup (Fin (n + 4))) x') := by
    intro u hu
    have hφu : orderOf (φ u : alternatingGroup (Fin (n + 4))) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hu
    rw [hφ u hu, hconj4 _ hφu]
  refine ⟨sameCentralizerOfInvolutionPattern_of_classes Sg S' φ x _ x' v' hcl hcl' hφ' Cx Cv, ?_⟩
  rintro (h7 | h11)
  · exfalso
    obtain ⟨e₁⟩ := h7
    have h1 := Nat.card_congr e₁.toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h1
    rcases hn with rfl | rfl <;> revert h1 <;> decide
  · exfalso
    obtain ⟨e₁⟩ := h11
    have h1 := Nat.card_congr e₁.toEquiv
    have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
      CFSG.Semidihedral.GL2Recognition.card_nativeM11
    rw [hc, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rcases hn with rfl | rfl <;> revert h1 <;> decide

end CFSG.GH74.GLS
