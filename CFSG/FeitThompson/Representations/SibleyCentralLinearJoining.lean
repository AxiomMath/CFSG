module

public import CFSG.FeitThompson.Representations.FreeCentralSectionTISylowRestriction
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
public import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.CentralPGroupFrobeniusTICoherence
import CFSG.FeitThompson.Representations.NormBoundLinearFamilyOrientation
import CFSG.FeitThompson.Representations.FreeCentralSectionCoherentLayer
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.DadeCosetConjugatesDisjoint
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleyCentralLinearJoining

open Subgroup NormalLinearInduced

section TI

variable {G : Type*} [Group G]

theorem conjInv_image_eq_or_inter_eq_empty {A : Set G} {L : Subgroup G}
    (hTI : IsTIWithNormalizer A L) (g k : G) :
    (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅ := by
  have hcomp : (fun x => k⁻¹ * x * k) '' ((fun x => (g * k⁻¹)⁻¹ * x * (g * k⁻¹)) '' A)
      = (fun x => g⁻¹ * x * g) '' A := by
    rw [conjInv_image_conjInv_image]; simp
  by_cases hs : g * k⁻¹ ∈ L
  · left
    have hA : (fun x => (g * k⁻¹)⁻¹ * x * (g * k⁻¹)) '' A = A := by
      rw [← mem_normalizer_iff_conjInv_image_eq, hTI.normalizer_eq]; exact hs
    rw [← hcomp, hA]
  · right
    have hinj : Function.Injective (fun x : G => k⁻¹ * x * k) := fun x y hxy => by simpa using hxy
    have himg := (Set.disjoint_image_iff hinj).2 (hTI.disjoint_image_conj_inv hs)
    rw [hcomp] at himg
    exact Set.disjoint_iff_inter_eq_empty.1 himg.symm

end TI

section Abstract

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {X Y : Set (L → ℂ)}

theorem isCoherent_union_of_norm_one_bridge
    (hXIrr : X ⊆ Irr L) (hYIrr : Y ⊆ Irr L) (hXY : Disjoint X Y)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero (X ∪ Y), (τ f : G → ℂ) 1 = 0)
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτstar : ∀ f g : charSpanZero (X ∪ Y), (g : L → ℂ) = star (f : L → ℂ) →
      (τ g : G → ℂ) = star ((τ f : G → ℂ)))
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y)
    (hXnr : ∀ χ ∈ X, star χ ≠ χ) (hYnr : ∀ χ ∈ Y, star χ ≠ χ)
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {ξ₀ η₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y)
    (hdegratio : ∀ χ : X, ∃ b : ℤ, 0 < b ∧ (χ : L → ℂ) 1 = (b : ℂ) * ξ₀ 1)
    {c : ℤ} (hc : ξ₀ 1 = (c : ℂ) * η₀ 1)
    {Γ : G → ℂ} (hΓmem : Γ ∈ virtualChars G) (hΓnorm : cfInner Γ Γ = 1)
    (hΓY : ∀ η : Y, cfInner Γ (coherentVal νY η) = 0)
    (hbridge : ∀ f : charSpanZero (X ∪ Y), (f : L → ℂ) = ξ₀ - (c : ℤ) • η₀ →
      (τ f : G → ℂ) = Γ - (c : ℂ) • coherentVal νY ⟨η₀, hη₀⟩) :
    IsCoherent (X ∪ Y) τ := by
  classical
  obtain ⟨μX, hμX, -, hμΓ⟩ :=
    SibleyCentralAlignment.exists_isCoherentWith_apply_eq_of_bridge hXIrr hYIrr hXY
      ⟨ξ₀, hξ₀⟩ ⟨η₀, hη₀⟩ hXstar hYstar hXnr hYnr hτ1 hτiso hτstar hνX hνY hξ₀ hη₀
      hdegratio hc hΓmem hΓnorm hΓY hbridge
  obtain ⟨e, -, he⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (hYIrr hη₀)
  have hsm : ((c : ℤ) • η₀ : L → ℂ) = (c : ℂ) • η₀ := (Int.cast_smul_eq_zsmul ℂ c η₀).symm
  have hmem : ξ₀ - (c : ℤ) • η₀ ∈ charSpanZero (X ∪ Y) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span (Or.inl hξ₀))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr hη₀))), ?_⟩
    rw [Pi.sub_apply, hsm]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hc, sub_self]
  have hcoe : (η₀ 1 • ξ₀ - ξ₀ 1 • η₀ : L → ℂ) = (e : ℤ) • (ξ₀ - (c : ℤ) • η₀) := by
    rw [hsm, ← Int.cast_smul_eq_zsmul ℂ (e : ℤ), hc, he]
    push_cast
    module
  have hw3 : η₀ 1 • ξ₀ - ξ₀ 1 • η₀ ∈ charSpanZero (X ∪ Y) := by
    rw [hcoe]; exact Submodule.smul_mem _ _ hmem
  refine IsCoherentWith.isCoherent (ν := joinHom μX νY
    (disjoint_span_span_of_disjoint hXIrr hYIrr hXY)) ?_
  refine isCoherentWith_joinHom hXIrr hYIrr hXY ⟨ξ₀, hξ₀⟩ ⟨η₀, hη₀⟩ hXstar hYstar hXnr hYnr
    hτ1 hτiso (fun f => hτstar f _ (by simp)) hμX hνY hξ₀ hη₀ (hw3 := hw3) ?_
  have hkey : (⟨η₀ 1 • ξ₀ - ξ₀ 1 • η₀, hw3⟩ : charSpanZero (X ∪ Y))
      = (e : ℤ) • (⟨ξ₀ - (c : ℤ) • η₀, hmem⟩ : charSpanZero (X ∪ Y)) := Subtype.ext hcoe
  rw [hkey, map_zsmul]
  have hb := hbridge ⟨ξ₀ - (c : ℤ) • η₀, hmem⟩ rfl
  rw [show (((e : ℤ) • τ ⟨ξ₀ - (c : ℤ) • η₀, hmem⟩ : virtualChars G) : G → ℂ)
      = (e : ℤ) • ((τ ⟨ξ₀ - (c : ℤ) • η₀, hmem⟩ : virtualChars G) : G → ℂ) from rfl, hb, hμΓ,
    hc, he, ← Int.cast_smul_eq_zsmul ℂ (e : ℤ)]
  push_cast
  module

end Abstract

namespace IsFreeCentralSection

section Config

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

theorem E_subgroupOf_ne_bot : E.subgroupOf L ≠ ⊥ := by
  intro hbot
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 h.E_le] at hbot
  exact h.E_ne_bot hbot

theorem P_subgroupOf_ne_bot : P.subgroupOf L ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot _).1 h.nontrivial_subgroupOf_P

theorem conjInv_punctured_image_eq_iff (g : G) :
    (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ↔ g ∈ L := by
  constructor
  · intro hg
    have hmem : g ∈ {g : G | (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1})
      = (P : Set G) \ {1}} := hg
    rw [h.stabilizer_punctured_eq] at hmem
    exact hmem
  · intro hg
    have hmem : g ∈ (L : Set G) := hg
    rw [← h.stabilizer_punctured_eq] at hmem
    exact hmem

variable [Fintype ↥L]

theorem exists_minDegree_mem_indFamDetect [Finite G] :
    ∃ ξ₀ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      ∀ χ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
        ∃ b : ℤ, 0 < b ∧ χ 1 = (b : ℂ) * ξ₀ 1 := by
  classical
  have hPn := h.normal_subgroupOf
  have hZn := h.normal_Z_subgroupOf
  have hXfin : (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).Finite :=
    finite_Irr.subset h.indFamDetect_subset_Irr
  obtain ⟨ζ, hζ⟩ := h.indFamDetect_nonempty_subgroupOf
  obtain ⟨ξ₀, hξ₀F, hmin⟩ :=
    hXfin.toFinset.exists_min_image natDeg ⟨ζ, hXfin.mem_toFinset.2 hζ⟩
  have hξ₀ := hXfin.mem_toFinset.1 hξ₀F
  refine ⟨ξ₀, hξ₀, fun χ hχ => ?_⟩
  obtain ⟨b, hb, -⟩ := h.exists_degree_eq_mul_pow_and_sq_dvd hχ
  obtain ⟨b₀, hb₀, -⟩ := h.exists_degree_eq_mul_pow_and_sq_dvd hξ₀
  have hle : natDeg ξ₀ ≤ natDeg χ := hmin χ (hXfin.mem_toFinset.2 hχ)
  rw [natDeg_eq hb, natDeg_eq hb₀] at hle
  have hb₀b : b₀ ≤ b :=
    (Nat.pow_le_pow_iff_right h.prime.one_lt).1 (Nat.le_of_mul_le_mul_left hle Nat.card_pos)
  refine ⟨(p ^ (b - b₀) : ℕ), Int.natCast_pos.2 (pow_pos h.prime.pos _), ?_⟩
  rw [hb, hb₀]
  push_cast
  rw [← mul_assoc, mul_comm ((p : ℂ) ^ (b - b₀)) _, mul_assoc, ← pow_add]
  congr 2
  omega

variable [Fintype G]

theorem isCoherent_indFamDetect
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (τX : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hτX : ∀ f, (τX f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) τX := by
  have hPn := h.normal_subgroupOf
  have hZn := h.normal_Z_subgroupOf
  refine isCoherent_of_coe_eq_indClassFun_centralLayer (E := E.subgroupOf L)
    (A := (P : Set G) \ {1}) h.prime h.odd_prime h.one_le_exponent h.odd_natCard_L
    (P_subgroupOf_ne_bot h) (E_subgroupOf_ne_bot h) h.natCard_P_subgroupOf_eq_prime_pow
    h.sup_subgroupOf h.inf_subgroupOf_eq_bot
    (free_subgroupOf h.P_le hCfree) h.Z_subgroupOf_ne_bot h.Z_subgroupOf_le_P_subgroupOf
    h.Z_subgroupOf_le_centralizer ?_ (conjInv_punctured_image_eq_iff h)
    (fun g k => conjInv_image_eq_or_inter_eq_empty h.isTI g k) τX hτX
  rw [Subgroup.map_subgroupOf_eq_of_le h.P_le]

theorem isCoherent_indFamDetect_union_indFamLinear
    (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G))
    (hCfree : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥)
    (τ : charSpanZero (indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)) →+
      virtualChars G)
    (hτ : ∀ f, ((τ f : virtualChars G) : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)) τ := by
  classical
  have hPn := h.normal_subgroupOf
  have hZn := h.normal_Z_subgroupOf
  have hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G) := by
    intro u hu hu1; rw [hCfree u hu hu1]; exact bot_le
  have hXIrr := h.indFamDetect_subset_Irr (E := E)
  have hYIrr := h.indFamLinear_subset_Irr hCP
  have hdisj : Disjoint (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) (indFamLinear (P.subgroupOf L)) :=
    Set.disjoint_iff_inter_eq_empty.2 (h.inter_indFamDetect_indFamLinear_eq_empty' hZP')
  have hXind : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
    have hh := indFamDetect_subset_indFam_irrChar (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
    rwa [irrChar_eq_Irr] at hh
  have hYind := indFamLinear_subset_indFam_Irr (P.subgroupOf L)
  have hXstar : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ∈
      indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) :=
    fun χ hχ => h.conj_mem_indFamDetect hχ
  have hYstar : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ∈ indFamLinear (P.subgroupOf L) :=
    fun χ hχ => conj_mem_indFamLinear _ hχ
  have hXnr : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ≠ χ := fun χ hχ hcon =>
    h.not_conj_eq_self_of_mem_indFamDetect hχ hcon.symm
  have hYnr : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ≠ χ := fun χ hχ hcon =>
    h.not_conj_eq_self_of_mem_indFamLinear' hCP hχ hcon.symm
  have hz0 : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (f : ↥L → ℂ) ∈ dadeZDomain L ((P : Set G) \ {1}) := fun f =>
    mem_dadeZDomain_of_mem_charSpanZero (Set.union_subset hXind hYind)
      (Set.union_subset hXIrr hYIrr) f
  have hτ1 : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      ((τ f : virtualChars G) : G → ℂ) 1 = 0 := fun f => by
    rw [hτ f]
    exact h.isTI.indClassFun_apply_one (fun x hx => (mem_dadeZDomain.1 (hz0 f)).2 x hx)
  have hτiso : ∀ f g : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      cfInner ((τ f : virtualChars G) : G → ℂ) ((τ g : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := fun f g => by
    rw [hτ f, hτ g]
    exact h.isTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hz0 f))
      (mem_dadeDomain_of_mem_dadeZDomain (hz0 g))
  have hτstar : ∀ f g : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (g : ↥L → ℂ) = star (f : ↥L → ℂ) →
      ((τ g : virtualChars G) : G → ℂ)
        = star ((τ f : virtualChars G) : G → ℂ) := fun f g hfg => by
    rw [hτ f, hτ g, hfg, DisjointCoherentFamilies.indClassFun_star]
  have hτX : ∀ f, ((restrictBaseline (Set.subset_union_left
      (s := indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)))
      (t := indFamLinear (P.subgroupOf L))) τ f : virtualChars G) : G → ℂ)
      = indClassFun L (f : ↥L → ℂ) := fun f => by rw [restrictBaseline_apply, hτ]; rfl
  have hτY : ∀ f, ((restrictBaseline (Set.subset_union_right
      (s := indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)))
      (t := indFamLinear (P.subgroupOf L))) τ f : virtualChars G) : G → ℂ)
      = indClassFun L (f : ↥L → ℂ) := fun f => by rw [restrictBaseline_apply, hτ]; rfl
  have hcohY : IsCoherent (indFamLinear (P.subgroupOf L))
      (restrictBaseline Set.subset_union_right τ) := by
    refine IsCoherent.congr_tau (τ₁ := tiIndCharSpanZeroHom h.isTI
      (indFamLinear_subset_indFam_Irr (P.subgroupOf L)) (h.indFamLinear_subset_Irr hCP))
      (fun f => ?_) (h.isCoherent_indFamLinear hCP)
    rw [coe_tiIndCharSpanZeroHom, hτY]
  have hcohX : IsCoherent (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)))
      (restrictBaseline Set.subset_union_left τ) :=
    isCoherent_indFamDetect h hCfree _ hτX
  obtain ⟨νY, hνY⟩ := isCoherent_iff.1 hcohY
  obtain ⟨νX, hνX⟩ := isCoherent_iff.1 hcohX
  obtain ⟨ξ₀, hξ₀, hdegratio⟩ := exists_minDegree_mem_indFamDetect h
  obtain ⟨η₀, hη₀⟩ := h.indFamLinear_nonempty'
  obtain ⟨c, -, hcξ, μY, hμY, -, Γ, hΓmem, hΓnorm, hΓY, hbr⟩ :=
    SibleyLinearOrientation.IsFreeCentralSection.exists_int_and_isCoherentWith_and_bridge h
      hCP hZP' hτX νX hνX hτY νY hνY hξ₀ hη₀
  have hηdeg : η₀ 1 = (Nat.card ↥E : ℂ) := h.apply_one_of_mem_indFamLinear hη₀
  refine isCoherent_union_of_norm_one_bridge hXIrr hYIrr hdisj hτ1 hτiso hτstar
    hXstar hYstar hXnr hYnr hνX hμY hξ₀ hη₀
    (fun χ => hdegratio _ χ.2) (c := c) (by rw [hcξ, hηdeg]) hΓmem hΓnorm hΓY ?_
  intro f hf
  rw [hτ f, hf, ← Int.cast_smul_eq_zsmul ℂ c η₀, hbr]

end Config

end IsFreeCentralSection

end SibleyCentralLinearJoining

end CFSG.FeitThompson
