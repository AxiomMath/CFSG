module

public import CFSG.FeitThompson.Representations.LinearCoherentCommonRestriction
public import CFSG.FeitThompson.Representations.CentralFamilyCoherentMapNormOneBridge
public import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
public import CFSG.FeitThompson.Representations.CoherentJoiningOneBridge
public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
public import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleyLinearOrientation

open Subgroup NormalLinearInduced SibleyCentralAlignment

section Weighted

variable {L : Type*} [Group L] [Fintype L] {P : Subgroup L} {H : Subgroup ↥P}

theorem cfInner_centralLayerWeightedChar_of_mem (hXIrr : indFamDetect P H ⊆ Irr L) (e : ℂ)
    {ξ : L → ℂ} (hξ : ξ ∈ indFamDetect P H) :
    cfInner ξ (centralLayerWeightedChar P H e) = (starRingEnd ℂ) (ξ 1 / e) := by
  classical
  rw [centralLayerWeightedChar_eq_sum_smul, cfInner_sum_right]
  rw [Finset.sum_eq_single ξ (fun ζ hζ hne => ?_) (fun hcon => ?_)]
  · rw [cfInner_smul_right, cfInner_self_of_mem_Irr (hXIrr hξ), mul_one]
  · rw [cfInner_smul_right, cfInner_eq_zero_of_mem_Irr (hXIrr hξ)
      (hXIrr (mem_centralLayerFinset.1 hζ)) (Ne.symm hne), mul_zero]
  · exact absurd (mem_centralLayerFinset.2 hξ) hcon

theorem cfInner_centralLayerWeightedChar_eq_zero (hXIrr : indFamDetect P H ⊆ Irr L) (e : ℂ)
    {η : L → ℂ} (hη : η ∈ Irr L) (hηX : η ∉ indFamDetect P H) :
    cfInner η (centralLayerWeightedChar P H e) = 0 := by
  classical
  rw [centralLayerWeightedChar_eq_sum_smul, cfInner_sum_right]
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  rw [cfInner_smul_right, cfInner_eq_zero_of_mem_Irr hη
    (hXIrr (mem_centralLayerFinset.1 hζ))
    (fun he => hηX (he ▸ mem_centralLayerFinset.1 hζ)), mul_zero]

end Weighted

section Abstract

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {S : Set (L → ℂ)}
  {τ : charSpanZero S →+ virtualChars G} {ν : Submodule.span ℤ S →+ virtualChars G}

open scoped Classical in
theorem exists_isCoherentWith_cfInner_eq_neg_ite
    (hSIrr : S ⊆ Irr L) (hSfin : S.Finite) (hν : IsCoherentWith S τ ν)
    {η₀ : L → ℂ} (hη₀ : η₀ ∈ S) (hne : ∃ η₁ ∈ S, η₁ ≠ η₀)
    (hdeg : ∀ η ∈ S, η 1 = η₀ 1)
    {δ : G → ℂ} {c k : ℤ} (hc : 1 < c)
    (hnorm : cfInner δ δ = 1 + (c : ℂ) ^ 2)
    (hrel : ∀ η : S, cfInner δ (coherentVal ν η)
      = (c : ℂ) * ((k : ℂ) - if η = (⟨η₀, hη₀⟩ : S) then 1 else 0)) :
    ∃ μ : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ μ ∧
      Submodule.span ℂ (Set.range fun χ : S => coherentVal μ χ)
        = Submodule.span ℂ (Set.range fun χ : S => coherentVal ν χ) ∧
      ∀ η : S, cfInner δ (coherentVal μ η)
        = -(c : ℂ) * (if η = (⟨η₀, hη₀⟩ : S) then 1 else 0) := by
  classical
  have hfin : Fintype S := hSfin.fintype
  have hON : ∀ χ ψ : S, cfInner (coherentVal ν χ) (coherentVal ν ψ) = if χ = ψ then 1 else 0 :=
    cfInner_coherentVal_coherentVal hSIrr hν
  set a : S → ℤ := fun η => c * (k - if η = (⟨η₀, hη₀⟩ : S) then 1 else 0) with hadef
  have hval : ∀ η : S, cfInner δ (coherentVal ν η) = ((a η : ℤ) : ℂ) := by
    intro η
    rw [hrel η]
    simp only [hadef]
    split_ifs <;> push_cast <;> ring
  have hbound : ∑ η : S, a η ^ 2 ≤ 1 + c ^ 2 := by
    have hb := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hON δ
    have hre : (1 : ℂ) + (c : ℂ) ^ 2 = (((1 + c ^ 2 : ℤ)) : ℂ) := by push_cast; ring
    rw [hnorm, hre, Complex.intCast_re] at hb
    have hrw : ∀ η ∈ (Finset.univ : Finset S), ‖cfInner δ (coherentVal ν η)‖ ^ 2
        = ((a η ^ 2 : ℤ) : ℝ) := by
      intro η _
      rw [hval η, Complex.norm_intCast]
      push_cast
      rw [sq_abs]
    rw [Finset.sum_congr rfl hrw] at hb
    exact_mod_cast hb
  have hpair : ∀ i j : S, i ≠ j → a i ^ 2 + a j ^ 2 ≤ 1 + c ^ 2 := by
    intro i j hij
    have hle : ∑ x ∈ ({i, j} : Finset S), a x ^ 2 ≤ ∑ x : S, a x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => sq_nonneg _
    rw [Finset.sum_pair hij] at hle
    exact le_trans hle hbound
  obtain ⟨η₁, hη₁S, hη₁ne⟩ := hne
  have hi₁ : (⟨η₁, hη₁S⟩ : S) ≠ ⟨η₀, hη₀⟩ := fun he => hη₁ne (congrArg Subtype.val he)
  have ha0 : a (⟨η₀, hη₀⟩ : S) = c * (k - 1) := by simp [hadef]
  have ha1 : a (⟨η₁, hη₁S⟩ : S) = c * k := by simp [hadef, hi₁]
  have hcsq : 1 < c ^ 2 := by nlinarith
  have hk : k = 0 ∨ k = 1 := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hp := hpair (⟨η₀, hη₀⟩ : S) ⟨η₁, hη₁S⟩ (Ne.symm hi₁)
    rw [ha0, ha1] at hp
    have hsq0 : 1 ≤ k ^ 2 := by rcases lt_or_gt_of_ne h0 with hlt | hgt <;> nlinarith
    have hsq1 : 1 ≤ (k - 1) ^ 2 := by rcases lt_or_gt_of_ne h1 with hlt | hgt <;> nlinarith
    nlinarith
  rcases hk with h0 | h1
  ·
    refine ⟨ν, hν, rfl, fun η => ?_⟩
    rw [hrel η, h0]
    split_ifs <;> push_cast <;> ring
  ·
    have huniq : ∀ χ : S, χ ≠ (⟨η₀, hη₀⟩ : S) → χ = ⟨η₁, hη₁S⟩ := by
      intro χ hχ
      by_contra hne'
      have hp := hpair χ ⟨η₁, hη₁S⟩ hne'
      have hax : a χ = c * k := by simp [hadef, hχ]
      rw [hax, ha1, h1] at hp
      nlinarith
    obtain ⟨μ, hμ, hspan, hμ0⟩ := exists_isCoherentWith_swap hSIrr hSfin hν hη₀
      (⟨η₁, hη₁S⟩ : S) hi₁ huniq hdeg rfl
    have hmem : η₁ - η₀ ∈ charSpanZero S := by
      refine mem_charSpanZero.2
        ⟨sub_mem (Submodule.subset_span hη₁S) (Submodule.subset_span hη₀), ?_⟩
      simp only [Pi.sub_apply]
      rw [hdeg η₁ hη₁S, sub_self]
    have hd1 := coe_baseline_sub hμ hη₁S hη₀ hmem
    have hd2 := coe_baseline_sub hν hη₁S hη₀ hmem
    have hμ1 : coherentVal μ (⟨η₁, hη₁S⟩ : S) = -coherentVal ν (⟨η₀, hη₀⟩ : S) := by
      have hh := hd1.symm.trans hd2
      rw [hμ0] at hh
      funext x
      have hx := congrFun hh x
      simp only [Pi.sub_apply, Pi.neg_apply] at hx ⊢
      linear_combination hx
    refine ⟨μ, hμ, hspan, fun η => ?_⟩
    by_cases hη : η = (⟨η₀, hη₀⟩ : S)
    · rw [hη, if_pos rfl, hμ0, cfInner_neg_right, hrel (⟨η₁, hη₁S⟩ : S), if_neg hi₁, h1]
      push_cast
      ring
    · rw [huniq η hη, hμ1, cfInner_neg_right, hrel (⟨η₀, hη₀⟩ : S), if_pos rfl, if_neg hi₁, h1]
      push_cast
      ring

end Abstract

section Bridge

variable {G : Type*} [Group G] [Fintype G] {K : Subgroup G} [Fintype ↥K]
  {X Y : Set (↥K → ℂ)}

theorem cfInner_indClassFun_sub_smul_eq
    (hXIrr : X ⊆ Irr ↥K) (hYIrr : Y ⊆ Irr ↥K) (hdisj : Disjoint X Y)
    {ξ₀ η₀ η : ↥K → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y) (hη : η ∈ Y)
    {A Δ : ↥K → ℂ} {c lam d : ℤ} {ψ : G → ℂ} (hψ : ψ ∈ classFun G)
    (hresψ : resClassFun K ψ = η + Δ + (lam : ℂ) • A)
    (hξ₀A : cfInner ξ₀ A = (c : ℂ)) (hη₀A : cfInner η₀ A = 0)
    (hξ₀Δ : cfInner ξ₀ Δ = 0) (hη₀Δ : cfInner η₀ Δ = (d : ℂ)) :
    cfInner (indClassFun K (ξ₀ - (c : ℂ) • η₀)) ψ
      = (c : ℂ) * (((lam - d : ℤ) : ℂ) - if η = η₀ then 1 else 0) := by
  classical
  rw [cfInner_indClassFun K _ hψ, hresψ]
  have h1 : cfInner ξ₀ η = 0 :=
    cfInner_eq_zero_of_mem_Irr (hXIrr hξ₀) (hYIrr hη)
      (fun he => (Set.disjoint_left.1 hdisj hξ₀) (he ▸ hη))
  have h2 : cfInner η₀ η = if η = η₀ then 1 else 0 := by
    by_cases hcase : η = η₀
    · rw [if_pos hcase, hcase, cfInner_self_of_mem_Irr (hYIrr hη₀)]
    · rw [if_neg hcase, cfInner_eq_zero_of_mem_Irr (hYIrr hη₀) (hYIrr hη) (Ne.symm hcase)]
  rw [cfInner_sub_left, cfInner_smul_left, cfInner_add_right, cfInner_add_right,
    cfInner_add_right, cfInner_add_right, cfInner_smul_right, cfInner_smul_right,
    h1, h2, hξ₀A, hη₀A, hξ₀Δ, hη₀Δ, map_intCast]
  push_cast
  ring

end Bridge

section Core

variable {G : Type*} [Group G] [Fintype G] {L P : Subgroup G} [Fintype ↥L]
  [(P.subgroupOf L).Normal] {X Y : Set (↥L → ℂ)}

open scoped Classical in
theorem exists_isCoherentWith_and_norm_one_bridge
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L)
    (hXIrr : X ⊆ Irr ↥L) (hYIrr : Y ⊆ Irr ↥L) (hdisj : Disjoint X Y)
    (hXind : X ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    (hYind : Y ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    (hYfin : Y.Finite)
    {ξ₀ η₀ : ↥L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y) (hYne : ∃ η₁ ∈ Y, η₁ ≠ η₀)
    (hdegY : ∀ η ∈ Y, η 1 = η₀ 1)
    {c : ℤ} (hc1 : 1 < c) (hc : ξ₀ 1 = (c : ℂ) * η₀ 1)
    {τY : charSpanZero Y →+ virtualChars G}
    {νY : Submodule.span ℤ Y →+ virtualChars G} (hνY : IsCoherentWith Y τY νY)
    {A Δ : ↥L → ℂ} {lam : ℤ}
    (hres : ∀ η, ∀ hη : η ∈ Y,
      resClassFun L ((νY ⟨η, Submodule.subset_span hη⟩ : virtualChars G) : G → ℂ)
        = η + Δ + (lam : ℂ) • A)
    (hξ₀A : cfInner ξ₀ A = (c : ℂ)) (hη₀A : cfInner η₀ A = 0)
    (hξ₀Δ : cfInner ξ₀ Δ = 0) (hη₀Δ : ∃ d : ℤ, cfInner η₀ Δ = (d : ℂ)) :
    ∃ μY : Submodule.span ℤ Y →+ virtualChars G, IsCoherentWith Y τY μY ∧
      Submodule.span ℂ (Set.range fun η : Y => coherentVal μY η)
        = Submodule.span ℂ (Set.range fun η : Y => coherentVal νY η) ∧
      ∃ Γ : G → ℂ, Γ ∈ virtualChars G ∧ cfInner Γ Γ = 1 ∧
        (∀ η : Y, cfInner Γ (coherentVal μY η) = 0) ∧
        indClassFun L (ξ₀ - (c : ℂ) • η₀) = Γ - (c : ℂ) • coherentVal μY ⟨η₀, hη₀⟩ := by
  classical
  obtain ⟨d, hd⟩ := hη₀Δ
  have hmemU : ξ₀ - (c : ℂ) • η₀ ∈ charSpanZero (X ∪ Y) := by
    refine mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span (Or.inl hξ₀)) ?_, ?_⟩
    · rw [show ((c : ℂ) • η₀) = c • η₀ from (Int.cast_smul_eq_zsmul ℂ c η₀)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr hη₀))
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hc, sub_self]
  have hz0 := mem_dadeZDomain_of_mem_charSpanZero (Set.union_subset hXind hYind)
    (Set.union_subset hXIrr hYIrr) ⟨_, hmemU⟩
  have hδmem : indClassFun L (ξ₀ - (c : ℂ) • η₀) ∈ virtualChars G :=
    hTI.indClassFun_mem_virtualChars hz0
  have hδnorm : cfInner (indClassFun L (ξ₀ - (c : ℂ) • η₀))
      (indClassFun L (ξ₀ - (c : ℂ) • η₀)) = 1 + (c : ℂ) ^ 2 := by
    rw [hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain hz0)
      (mem_dadeDomain_of_mem_dadeZDomain hz0)]
    have h1 : cfInner ξ₀ ξ₀ = 1 := cfInner_self_of_mem_Irr (hXIrr hξ₀)
    have h2 : cfInner η₀ η₀ = 1 := cfInner_self_of_mem_Irr (hYIrr hη₀)
    have h3 : cfInner ξ₀ η₀ = 0 :=
      cfInner_eq_zero_of_mem_Irr (hXIrr hξ₀) (hYIrr hη₀)
        (fun he => (Set.disjoint_left.1 hdisj hξ₀) (he ▸ hη₀))
    have h4 : cfInner η₀ ξ₀ = 0 := by rw [← conj_cfInner, h3, map_zero]
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
      cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, h1, h2, h3, h4, map_intCast]
    ring
  have hrel : ∀ η : Y, cfInner (indClassFun L (ξ₀ - (c : ℂ) • η₀)) (coherentVal νY η)
      = (c : ℂ) * (((lam - d : ℤ) : ℂ) - if η = (⟨η₀, hη₀⟩ : Y) then 1 else 0) := by
    intro η
    have hψ : coherentVal νY η ∈ classFun G :=
      virtualChars_le_classFun (coherentVal_mem_virtualChars νY η)
    have hresη : resClassFun L (coherentVal νY η) = (η : ↥L → ℂ) + Δ + (lam : ℂ) • A := by
      rw [coherentVal_apply]
      exact hres _ η.2
    have hkey := cfInner_indClassFun_sub_smul_eq hXIrr hYIrr hdisj hξ₀ hη₀ η.2 hψ hresη
      hξ₀A hη₀A hξ₀Δ hd
    rw [hkey]
    congr 2
    by_cases hcase : (η : ↥L → ℂ) = η₀
    · rw [if_pos hcase, if_pos (Subtype.ext hcase : η = (⟨η₀, hη₀⟩ : Y))]
    · rw [if_neg hcase, if_neg (fun he : η = (⟨η₀, hη₀⟩ : Y) => hcase (congrArg Subtype.val he))]
  obtain ⟨μY, hμY, hspan, hμrel⟩ := exists_isCoherentWith_cfInner_eq_neg_ite hYIrr hYfin hνY
    hη₀ hYne (fun η hη => (hdegY η hη).trans (hdegY η₀ hη₀).symm) hc1 hδnorm hrel
  refine ⟨μY, hμY, hspan, indClassFun L (ξ₀ - (c : ℂ) • η₀)
    + (c : ℂ) • coherentVal μY ⟨η₀, hη₀⟩, ?_, ?_, ?_, ?_⟩
  · refine add_mem hδmem ?_
    rw [show ((c : ℂ) • coherentVal μY ⟨η₀, hη₀⟩) = c • coherentVal μY ⟨η₀, hη₀⟩ from
      Int.cast_smul_eq_zsmul ℂ c _]
    exact Submodule.smul_mem _ _ (coherentVal_mem_virtualChars μY _)
  · have hON := cfInner_coherentVal_coherentVal hYIrr hμY (⟨η₀, hη₀⟩ : Y) (⟨η₀, hη₀⟩ : Y)
    rw [if_pos rfl] at hON
    have h1 := hμrel (⟨η₀, hη₀⟩ : Y)
    rw [if_pos rfl] at h1
    have h2 : cfInner (coherentVal μY ⟨η₀, hη₀⟩) (indClassFun L (ξ₀ - (c : ℂ) • η₀))
        = -(c : ℂ) := by
      rw [← conj_cfInner, h1]
      simp
    rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, cfInner_smul_left,
      cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, hδnorm, hON, h1, h2,
      map_intCast]
    ring
  · intro η
    have hON := cfInner_coherentVal_coherentVal hYIrr hμY (⟨η₀, hη₀⟩ : Y) η
    have h1 := hμrel η
    rw [cfInner_add_left, cfInner_smul_left, h1, hON]
    by_cases hcase : η = (⟨η₀, hη₀⟩ : Y)
    · rw [if_pos hcase, if_pos hcase.symm]
      ring
    · rw [if_neg hcase, if_neg (Ne.symm hcase)]
      ring
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

end Core

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Fintype G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z) [Fintype ↥L]
  [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

include h

omit [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal] in
theorem exists_one_lt_int_apply_one_eq (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G)) {ξ : ↥L → ℂ}
    (hξ : ξ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    ∃ c : ℤ, 1 < c ∧ ξ 1 = (c : ℂ) * (Nat.card E : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect (P.subgroupOf L)).1 hξ
  have hθirr : θ ∈ Irr ↥(P.subgroupOf L) := by
    rw [← irrChar_eq_Irr]; exact (mem_irrDetect.1 hθ).1
  obtain ⟨d, hdpos, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hθirr
  have hd1 : d ≠ 1 := by
    intro hd1
    refine (mem_irrDetect.1 hθ).2 ?_
    have hone : θ 1 = 1 := by rw [hd, hd1]; norm_num
    have hker := Irr.commutator_subset_charValueKernel hθirr hone
    refine fun z hz => hker ?_
    rw [commutator_eq_subgroupOf_commutator, commutator_subgroupOf_eq h.P_le]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
      (hZP' (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hz))))
  refine ⟨(d : ℤ), by omega, ?_⟩
  rw [indClassFun_apply_one, hd, h.index_subgroupOf_eq]
  push_cast
  ring

omit [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal] in
theorem exists_ne_mem_indFamLinear
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    {η₀ : ↥L → ℂ} (hη₀ : η₀ ∈ indFamLinear (P.subgroupOf L)) :
    ∃ η₁ ∈ indFamLinear (P.subgroupOf L), η₁ ≠ η₀ :=
  ⟨fun y => (starRingEnd ℂ) (η₀ y), conj_mem_indFamLinear _ hη₀,
    fun he => IsFreeCentralSection.not_conj_eq_self_of_mem_indFamLinear' h hCP hη₀ he.symm⟩

omit [Fintype G] [(P.subgroupOf L).Normal] in
theorem notMem_irrTrivialOn_of_mem_indFamDetect {ξ : ↥L → ℂ}
    (hξ : ξ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :
    ξ ∉ irrTrivialOn (Z.subgroupOf L) := by
  intro hcon
  refine not_subset_charValueKernel_of_mem_indFamDetect
    (P := P.subgroupOf L) (Z := Z.subgroupOf L) h.Z_subgroupOf_le_P_subgroupOf hξ ?_
  intro z hz
  exact mem_charValueKernel.2 ((mem_irrTrivialOn.1 hcon).2 z hz)

open scoped Classical in
theorem exists_int_and_isCoherentWith_and_bridge
    (hCP : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G))
    (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G))
    {τX : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G}
    (hτX : ∀ f, (τX f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (νX : Submodule.span ℤ (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) →+ virtualChars G)
    (hνX : IsCoherentWith (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) τX νX)
    {τY : charSpanZero (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    (hτY : ∀ f, (τY f : G → ℂ) = indClassFun L (f : ↥L → ℂ))
    (νY : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hνY : IsCoherentWith (indFamLinear (P.subgroupOf L)) τY νY)
    {ξ₀ η₀ : ↥L → ℂ}
    (hξ₀ : ξ₀ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)))
    (hη₀ : η₀ ∈ indFamLinear (P.subgroupOf L)) :
    ∃ c : ℤ, 1 < c ∧ ξ₀ 1 = (c : ℂ) * (Nat.card E : ℂ) ∧
      ∃ μY : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G,
        IsCoherentWith (indFamLinear (P.subgroupOf L)) τY μY ∧
        Submodule.span ℂ (Set.range fun η : indFamLinear (P.subgroupOf L) => coherentVal μY η)
          = Submodule.span ℂ
              (Set.range fun η : indFamLinear (P.subgroupOf L) => coherentVal νY η) ∧
        ∃ Γ : G → ℂ, Γ ∈ virtualChars G ∧ cfInner Γ Γ = 1 ∧
          (∀ η : indFamLinear (P.subgroupOf L), cfInner Γ (coherentVal μY η) = 0) ∧
          indClassFun L (ξ₀ - (c : ℂ) • η₀) = Γ - (c : ℂ) • coherentVal μY ⟨η₀, hη₀⟩ := by
  classical
  obtain ⟨c, hc1, hc⟩ := exists_one_lt_int_apply_one_eq h hZP' hξ₀
  refine ⟨c, hc1, hc, ?_⟩
  have hXIrr := h.indFamDetect_subset_Irr
  have hYIrr := IsFreeCentralSection.indFamLinear_subset_Irr h hCP
  have hdisj : Disjoint (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) (indFamLinear (P.subgroupOf L)) :=
    Set.disjoint_iff_inter_eq_empty.2
      (IsFreeCentralSection.inter_indFamDetect_indFamLinear_eq_empty' h hZP')
  have hXind : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
    have hh := indFamDetect_subset_indFam_irrChar (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
    rwa [irrChar_eq_Irr] at hh
  have hYind := indFamLinear_subset_indFam_Irr (P.subgroupOf L)
  have hEne : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hdegY : ∀ η ∈ indFamLinear (P.subgroupOf L), η 1 = η₀ 1 := fun η hη => by
    rw [IsFreeCentralSection.apply_one_of_mem_indFamLinear h hη,
      IsFreeCentralSection.apply_one_of_mem_indFamLinear h hη₀]
  obtain ⟨lam, Δ, hΔ, hres⟩ := h.exists_int_forall_resClassFun_indFamLinear_eq hCP hZP' hτX νX hνX
    hτY νY hνY
  refine exists_isCoherentWith_and_norm_one_bridge h.isTI hXIrr hYIrr hdisj hXind hYind
    (finite_indFamLinear _) hξ₀ hη₀ (exists_ne_mem_indFamLinear h hCP hη₀) hdegY hc1
    (by rw [hc, IsFreeCentralSection.apply_one_of_mem_indFamLinear h hη₀]) hνY hres ?_ ?_ ?_ ?_
  · rw [cfInner_centralLayerWeightedChar_of_mem hXIrr _ hξ₀, hc,
      mul_div_assoc, div_self hEne, mul_one, map_intCast]
  · exact cfInner_centralLayerWeightedChar_eq_zero hXIrr _ (hYIrr hη₀)
      (fun hcon => (Set.disjoint_right.1 hdisj hη₀) hcon)
  · refine cfInner_eq_zero_of_mem_span_of_disjoint (X := {ξ₀})
      (Y := irrTrivialOn (Z.subgroupOf L)) (Set.singleton_subset_iff.2 (hXIrr hξ₀))
      irrTrivialOn_subset_Irr ?_ (Submodule.subset_span rfl) hΔ
    rw [Set.disjoint_singleton_left]
    exact notMem_irrTrivialOn_of_mem_indFamDetect h hξ₀
  · exact exists_int_cfInner_of_mem_span_Irr (Submodule.subset_span (hYIrr hη₀))
      (Submodule.span_mono irrTrivialOn_subset_Irr hΔ)

end IsFreeCentralSection

end SibleyLinearOrientation

end CFSG.FeitThompson
