module

public import CFSG.GF2Type.Smith1979.W4AsOmega
public import CFSG.GF2Type.Smith1979.W4AsSel
public import CFSG.GF2Type.Smith1979.W4FiveOne
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isComponentOf_layer (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar)) :
    CFSG.Open.IsComponentOf ((timmesfeldLayer S.Mbar).map S.Mbar.subtype) S.Mbar := by
  haveI : (timmesfeldLayer S.Mbar).Normal := CFSG.ComponentClassification.Layer.normal S.Mbar
  exact isComponentOf_map_subtype ⟨le_top,
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top inferInstance, hq⟩

theorem Mbar_le_normalizer_layer (S : Setting G) :
    S.Mbar ≤
      normalizer (((timmesfeldLayer S.Mbar).map S.Mbar.subtype : Subgroup S.O) : Set S.O) := by
  intro m hm
  refine S4.mem_normalizer_of_conj_le fun p hp => ?_
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹,
    (CFSG.ComponentClassification.Layer.normal S.Mbar).conj_mem y hy ⟨m, hm⟩, rfl⟩

namespace Component

noncomputable def compAtLayer (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar)) {l : S.O}
    (hl : l ∈ S.Lbar g) (hl1 : l ≠ 1)
    (hlE : ∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) : CompAt S g where
  X := (timmesfeldLayer S.Mbar).map S.Mbar.subtype
  t := l
  isComponentOf := isComponentOf_layer hq
  norm h := (S.Lbar_le_Mbar _).trans (Mbar_le_normalizer_layer S)
  mem_Lbar := hl
  ne_one := hl1
  comm x hx := (hlE x hx).symm

theorem exists_omega (A : CompAt S g) (hIrr : S5.Irr S) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) :
    ∃ hVQ : ¬ V S g A.t ≤ S.Qa g, OmegaCase H C A.mem_Lbar A.ne_one hVQ ∧
      finrank (ZMod 2) (Vt S g A.t) = 4 := by
  rcases W4As.classify_four hw H hNo C A.mem_Lbar A.ne_one (A.Rbar_ne hIrr H) with
    ⟨hL, h2⟩ | h
  · exact (false_of_isQuasisimple_of_le_solvable (imgR_le_RmodN H.conj_mem A.t A.X)
      (A.isQuasisimple_img hIrr H C) ((S45Q.hyp45Q H C).lin_two A.mem_Lbar hL h2)).elim
  · exact h

theorem imgR_eq_RmodN (A : CompAt S g) (hIrr : S5.Irr S) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (hVQ : ¬ V S g A.t ≤ S.Qa g) :
    imgR H.conj_mem A.t A.X = RmodN S g A.t ∧ Nat.card (LmodN S g A.t) = 4 :=
  W4Five.quasisimple_w4 (S45Q.hyp45Q H C) hNo hw A.mem_Lbar A.ne_one (A.Rbar_ne hIrr H) hVQ
    (A.isSubnormal_img hIrr H) (A.isQuasisimple_img hIrr H C)

theorem nonempty_mulEquiv_RmodN (A : CompAt S g) (hCE : CentralExtInput.{0})
    (hIrr : S5.Irr S) (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hKR : imgR H.conj_mem A.t A.X = RmodN S g A.t) : Nonempty (A.X ≃* RmodN S g A.t) := by
  have hNL := (W4Five.Nbar_le_Lbar_w4 A hCE hIrr H hNo C (S45Q.hyp45Q H C) hw).2
  have hXR : A.X ≤ Rbar S g A.t := A.le_Rbar hIrr H
  obtain ⟨φ, hφ⟩ : ∃ φ : A.X →* (Vt S g A.t ≃ₗ[ZMod 2] Vt S g A.t),
      φ = (resV H.conj_mem A.t).comp (Subgroup.inclusion hXR) := ⟨_, rfl⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hφ] at hy
    have hyN : (y : S.O) ∈ Nbar S g A.t :=
      (resV_eq_one_iff H.conj_mem (Subgroup.inclusion hXR y)).mp hy
    have hyL : (y : S.O) ∈ S.Lbar g := hNL hyN
    have hyy : (y : S.O) ^ (2 ^ 1) = 1 := by
      rw [pow_one, pow_two]
      exact S4.mul_self_of_mem_Lbar S H.conj_mem hyL
    exact Subtype.ext (eq_one_of_mem_center_of_pow S A.isComponentOf.2.1 y.2
      (fun z hz => A.commute_of_mem_Nbar hIrr H C hyL hyN hz) hyy)
  have hrange : φ.range = RmodN S g A.t := by
    rw [← hKR, hφ]
    ext e
    rw [MonoidHom.mem_range, mem_imgR]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hXR y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem card_RmodN_eq_sixty (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hns : ¬ Group.IsSolvable (RmodN S g t)) :
    Nat.card (RmodN S g t) = 60 := by
  obtain ⟨Q, hQ, -, hR, -, -⟩ := hΩ.exists_form
  haveI : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  haveI : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hidx := Subgroup.relIndex_mul_card (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_eq_left.mpr (omegaGroup_le Q hQ), relIndex_omegaGroup] at hidx
  by_cases hplus : IsPlusType Q
  · exfalso
    have hcardZ := natCard_orthogonalGroup_of_type (K := ZMod 2) (V := Vt S g t) hQ (m := 1)
      (by rw [h4]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
    have h72 : (2 * (Nat.card (ZMod 2) : ℤ) ^ (1 * (1 + 1)) *
        ((Nat.card (ZMod 2) : ℤ) ^ (1 + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1)) = 72 := by
      norm_num [Nat.card_zmod]
    rw [h72] at hcardZ
    have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 72 :=
      Nat.cast_injective hcardZ
    have h36 : Nat.card (omegaGroup Q hQ) = 36 := by omega
    refine hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (G := RmodN S g t) ?_)
    rw [hR, h36]
    norm_num
  · have hcardZ := natCard_orthogonalGroup_of_type (K := ZMod 2) (V := Vt S g t) hQ (m := 1)
      (by rw [h4]) (ε := -1) (Or.inr ⟨rfl, hplus⟩)
    have h120 : (2 * (Nat.card (ZMod 2) : ℤ) ^ (1 * (1 + 1)) *
        ((Nat.card (ZMod 2) : ℤ) ^ (1 + 1) - (-1)) *
          ∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1)) = 120 := by
      norm_num [Nat.card_zmod]
    rw [h120] at hcardZ
    have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 120 :=
      Nat.cast_injective hcardZ
    rw [hR]
    omega

theorem layer_data (A : CompAt S g) (hCE : CentralExtInput.{0}) (hIrr : S5.Irr S)
    (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) :
    Nonempty (A.X ≃* alternatingGroup (Fin 5)) ∧ Nat.card (RmodN S g A.t) = 60 ∧
      4 ≤ Nat.card (S.Lbar g ⊓ A.X : Subgroup S.O) ∧
      ∀ s ∈ S.Lbar g, s ∈ A.X ∨ s * A.t ∈ A.X := by
  have Q := S45Q.hyp45Q H C
  haveI : Finite (Vt S g A.t ≃ₗ[ZMod 2] Vt S g A.t) := finite_linearEquiv_of_finite
  obtain ⟨hVQ, hΩ, h4⟩ := exists_omega A hIrr hw H hNo C
  obtain ⟨hKR, hLmod⟩ := imgR_eq_RmodN A hIrr hw H hNo C hVQ
  have hns : ¬ Group.IsSolvable (RmodN S g A.t) := fun hsol =>
    false_of_isQuasisimple_of_le_solvable (imgR_le_RmodN H.conj_mem A.t A.X)
      (A.isQuasisimple_img hIrr H C) hsol
  have h60 := card_RmodN_eq_sixty H C A.mem_Lbar A.ne_one hVQ hΩ h4 hns
  have hsimple : IsSimpleGroup (RmodN S g A.t) :=
    (Q.omega_four A.mem_Lbar A.ne_one hVQ hΩ h4).resolve_right hns
  refine ⟨?_, h60, ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_RmodN A hCE hIrr hw H hNo C hKR
    obtain ⟨e'⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := RmodN S g A.t) h60
    exact ⟨e.trans e'⟩
  · have h := W4Five.card_LmodN_inf_le_w4 A hCE hIrr H hNo C Q hw
    have hle : LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X = LmodN S g A.t := by
      rw [hKR]
      exact inf_eq_left.mpr (LmodN_le_RmodN A.mem_Lbar)
    rw [hle, hLmod] at h
    exact h
  · intro s hs
    have hsR : s ∈ Rbar S g A.t := Lbar_le_Rbar A.mem_Lbar hs
    have hsK : resV H.conj_mem A.t ⟨s, hsR⟩ ∈ imgR H.conj_mem A.t A.X := by
      rw [hKR]
      exact LmodN_le_RmodN A.mem_Lbar (resV_mem_LmodN H.conj_mem hs hsR)
    obtain ⟨y, hyX, hye⟩ := mem_imgR.mp hsK
    have hN : ((y⁻¹ * ⟨s, hsR⟩ : Rbar S g A.t) : S.O) ∈ Nbar S g A.t := by
      rw [← resV_eq_one_iff H.conj_mem, map_mul, map_inv, hye, inv_mul_cancel]
    rw [W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C A.mem_Lbar A.ne_one hVQ hΩ h4] at hN
    have htt : A.t * A.t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem A.mem_Lbar
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hN with h1 | h1
    · left
      have h2 : (y : S.O) = s := inv_mul_eq_one.mp h1
      exact h2 ▸ hyX
    · right
      have h1' : (y : S.O)⁻¹ * s = A.t := h1
      have h2 : s = (y : S.O) * A.t := by
        calc s = (y : S.O) * ((y : S.O)⁻¹ * s) := (mul_inv_cancel_left _ _).symm
          _ = (y : S.O) * A.t := by rw [h1']
      have h3 : s * A.t = (y : S.O) := by
        rw [h2, mul_assoc, htt, mul_one]
      exact h3 ▸ hyX

end Component

theorem layer_data_of_commute (hCE : CentralExtInput.{0}) (hIrr : S5.Irr S) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar)) {l : S.O} (hl : l ∈ S.Lbar g)
    (hl1 : l ≠ 1)
    (hlE : ∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype, l * y = y * l) :
    Nonempty ((timmesfeldLayer S.Mbar).map S.Mbar.subtype ≃* alternatingGroup (Fin 5)) ∧
      Nat.card (RmodN S g l) = 60 ∧
      4 ≤ Nat.card (S.Lbar g ⊓ (timmesfeldLayer S.Mbar).map S.Mbar.subtype : Subgroup S.O) ∧
      ∀ s ∈ S.Lbar g, s ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype ∨
        s * l ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype :=
  Component.layer_data (Component.compAtLayer hq hl hl1 hlE) hCE hIrr hw H hNo C

end CFSG.GF2Type.Smith1979.OmegaPlus
