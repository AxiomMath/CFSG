module

public import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
public import CFSG.FeitThompson.Representations.CentralScalarInductionDegreeSum
public import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
public import CFSG.FeitThompson.Representations.AbelianPointStabilizersCharacterStabilizers
public import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
public import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
public import CFSG.FeitThompson.Representations.CentralFamilyCoherentMapNormOneBridge
public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

theorem sum_eq_zero_of_mem_Irr_of_ne_one {X : Type*} [Group X] [Fintype X] {χ : X → ℂ}
    (hχ : χ ∈ Irr X) (hne : χ ≠ 1) : ∑ x : X, χ x = 0 := by
  have h := cfInner_eq_zero_of_mem_Irr hχ one_mem_Irr hne
  rw [cfInner_def] at h
  have hcard : (Nat.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [Pi.one_apply, map_one, mul_one] at h
  exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hcard)

theorem cfInner_eq_of_eq_on_ne_one {X : Type*} [Group X] [Fintype X] {χ : X → ℂ}
    (hχ : χ ∈ Irr X) (hne : χ ≠ 1) (hχ1 : χ 1 = 1) {F : X → ℂ} {v : ℂ}
    (hF : ∀ x : X, x ≠ 1 → F x = v) :
    cfInner χ F = (Nat.card X : ℂ)⁻¹ * (starRingEnd ℂ) (F 1 - v) := by
  classical
  rw [cfInner_def]
  congr 1
  have hsplit : ∑ x : X, χ x * (starRingEnd ℂ) (F x)
      = χ 1 * (starRingEnd ℂ) (F 1)
        + ∑ x ∈ (Finset.univ.erase (1 : X)), χ x * (starRingEnd ℂ) (F x) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (1 : X))).symm
  rw [hsplit, hχ1, one_mul]
  have hrw : ∀ x ∈ (Finset.univ.erase (1 : X)), χ x * (starRingEnd ℂ) (F x)
      = (starRingEnd ℂ) v * χ x := by
    intro x hx
    rw [hF x (Finset.ne_of_mem_erase hx)]
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hsum : ∑ x ∈ (Finset.univ.erase (1 : X)), χ x = -1 := by
    have h1 : χ 1 + ∑ x ∈ (Finset.univ.erase (1 : X)), χ x = ∑ x : X, χ x :=
      Finset.add_sum_erase _ _ (Finset.mem_univ (1 : X))
    rw [sum_eq_zero_of_mem_Irr_of_ne_one hχ hne, hχ1] at h1
    linear_combination h1
  rw [hsum, map_sub]
  ring

theorem inertiaGroup_eq_top_of_le_center {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (lam : ↥Z → ℂ) : inertiaGroup Z lam = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  rw [mem_inertiaGroup_iff_forall_conj]
  intro z
  congr 1
  refine Subtype.ext ?_
  rw [MulAut.conjNormal_apply]
  have hc := Subgroup.mem_center_iff.1 (hZ z.2) g⁻¹
  calc g⁻¹ * (z : X) * g⁻¹⁻¹ = (g⁻¹ * (z : X)) * g := by group
    _ = ((z : X) * g⁻¹) * g := by rw [hc]
    _ = (z : X) := by group

variable {X : Type*} [Group X] [Fintype X] {M N : Subgroup X}

set_option linter.unusedFintypeInType false in
theorem mem_nonprincipalIrr_of_mem_centralIrrFinset {W : Subgroup M}
    {lam : ↥W → ℂ} (hlam1 : lam ≠ 1) {θ : ↥M → ℂ}
    (hθ : θ ∈ centralIrrFinset W lam) : θ ∈ nonprincipalIrr ↥M := by
  obtain ⟨hθirr, hval⟩ := mem_centralIrrFinset.1 hθ
  refine mem_nonprincipalIrr.2 ⟨hθirr, fun hcon => hlam1 (funext fun z => ?_)⟩
  have h1 := hval z
  rw [hcon] at h1
  simp only [Pi.one_apply] at h1
  simpa using h1.symm

theorem indClassFun_mem_span_indFam_nonprincipalIrr (hNM : N ≤ M)
    (hcent : (N.subgroupOf M) ≤ Subgroup.center ↥M)
    {lam : ↥N → ℂ} (hlam : lam ∈ Irr ↥N) (hlam1 : lam ≠ 1) :
    indClassFun N lam ∈ Submodule.span ℤ (indFam M (nonprincipalIrr ↥M)) := by
  classical
  have : Fintype ↥M := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hNM with he
  set lam' : ↥(N.subgroupOf M) → ℂ := lam ∘ e with hlam'
  have hlam'irr : lam' ∈ Irr ↥(N.subgroupOf M) := FrobeniusInduction.mem_Irr_comp_mulEquiv hlam e
  have hlam'1 : lam' ≠ 1 := by
    intro hc
    refine hlam1 (funext fun z => ?_)
    have := congrFun hc (e.symm z)
    simpa [hlam'] using this
  have htrans : indClassFun M (indClassFun (N.subgroupOf M) lam') = indClassFun N lam :=
    AbelianInertiaBlock.indClassFun_indClassFun (H := N) M hNM lam
  rw [← htrans, indClassFun_eq_sum_centralIrrFinset hcent hlam'irr,
    AbelianInertiaBlock.indClassFun_sum]
  refine Submodule.sum_mem _ fun θ hθ => ?_
  obtain ⟨d, -, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr
    (mem_nonprincipalIrr.1 (mem_nonprincipalIrr_of_mem_centralIrrFinset hlam'1 hθ)).1
  rw [hd, indClassFun_smul,
    show ((d : ℂ)) • indClassFun M θ = (d : ℤ) • indClassFun M θ from by
      rw [← Int.cast_natCast (R := ℂ) d, Int.cast_smul_eq_zsmul]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (indClassFun_mem_indFam M (mem_nonprincipalIrr_of_mem_centralIrrFinset hlam'1 hθ)))

theorem resClassFun_mem_span_Irr {G : Type*} [Group G] [Finite G] (L : Subgroup G) {χ : G → ℂ}
    (hχ : χ ∈ Submodule.span ℤ (Irr G)) : resClassFun L χ ∈ Submodule.span ℤ (Irr ↥L) := by
  have h := comp_mem_span_Irr (X := ↥L) L.subtype hχ
  have he : χ ∘ L.subtype = resClassFun L χ := by
    funext x
    rw [resClassFun_apply]
    rfl
  rwa [he] at h

set_option linter.unusedFintypeInType false in
theorem cfInner_indClassFun_resClassFun_eq {G : Type*} [Group G] [Fintype G] {L Z : Subgroup G}
    [Fintype ↥L] [Fintype ↥(Z.subgroupOf L)] (hZL : Z ≤ L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    (hlamdeg : lam 1 = 1) {ψ : G → ℂ} (hψ : ψ ∈ classFun G) {b : ℂ}
    (hb : ∀ z ∈ Z, z ≠ 1 → ψ z = b) :
    cfInner (indClassFun (Z.subgroupOf L) lam) (resClassFun L ψ)
      = (Nat.card ↥Z : ℂ)⁻¹ * (starRingEnd ℂ) (ψ 1 - b) := by
  rw [cfInner_indClassFun _ _ (resClassFun_mem_classFun L hψ)]
  have hF : ∀ z : ↥(Z.subgroupOf L), z ≠ 1 →
      resClassFun (Z.subgroupOf L) (resClassFun L ψ) z = b := by
    intro z hz
    rw [resClassFun_apply, resClassFun_apply]
    exact hb _ (Subgroup.mem_subgroupOf.1 z.2) (fun hc => hz (Subtype.ext (Subtype.ext hc)))
  have h1 : resClassFun (Z.subgroupOf L) (resClassFun L ψ) 1 = ψ 1 := by
    rw [resClassFun_apply, resClassFun_apply]
    rfl
  rw [cfInner_eq_of_eq_on_ne_one hlam hlam1 hlamdeg hF, h1,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]

theorem sdiff_one_eq_image_subgroupOf {G : Type*} [Group G] {L P : Subgroup G} (hPL : P ≤ L) :
    (P : Set G) \ {1} = (fun x : ↥L => (x : G)) '' (((P.subgroupOf L) : Set ↥L) \ {1}) := by
  ext g
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe]
  refine ⟨fun ⟨hgP, hg1⟩ => ⟨⟨g, hPL hgP⟩,
      ⟨Subgroup.mem_subgroupOf.2 hgP, fun hc => hg1 (by simpa using hc)⟩, rfl⟩, ?_⟩
  rintro ⟨x, ⟨hxP, hx1⟩, rfl⟩
  exact ⟨Subgroup.mem_subgroupOf.1 hxP, fun hc => hx1 (Subtype.ext hc)⟩

theorem mem_dadeZDomain_of_mem_charSpanZero_of_subset_indFam {G : Type*} [Group G]
    {L P : Subgroup G} [Fintype ↥L] [(P.subgroupOf L).Normal] (hPL : P ≤ L)
    {S : Set (↥L → ℂ)} (hS : S ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)))
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero S) :
    f ∈ dadeZDomain L ((P : Set G) \ {1}) :=
  NormalInducedFamily.charSpanZero_le_dadeZDomain (sdiff_one_eq_image_subgroupOf hPL) hS hf

namespace SibleyLinearOrientation

open NormalLinearInduced SibleyCentralAlignment

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {S : Set (L → ℂ)}
  {τ : charSpanZero S →+ virtualChars G} {ν : Submodule.span ℤ S →+ virtualChars G}

open scoped Classical in
theorem exists_isCoherentWith_forall_cfInner_eq_neg_ite
    (hSIrr : S ⊆ Irr L) (hSfin : S.Finite) (hν : IsCoherentWith S τ ν)
    {η₀ η₁ : L → ℂ} (hη₀ : η₀ ∈ S) (hη₁ : η₁ ∈ S) (hη₁ne : η₁ ≠ η₀)
    (hdeg : ∀ η ∈ S, η 1 = η₀ 1)
    {δ : G → ℂ} {c k N : ℤ} (hc : 0 < c) (hN : N < 2 * c ^ 2)
    (hnorm : cfInner δ δ = (N : ℂ))
    (hrel : ∀ η : S, cfInner δ (coherentVal ν η)
      = (c : ℂ) * ((k : ℂ) - if η = (⟨η₀, hη₀⟩ : S) then 1 else 0)) :
    ∃ μ : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ μ ∧
      Submodule.span ℂ (Set.range fun χ : S => coherentVal μ χ)
        = Submodule.span ℂ (Set.range fun χ : S => coherentVal ν χ) ∧
      (μ = ν ∨ (S = {η₀, η₁} ∧
        coherentVal μ ⟨η₀, hη₀⟩ = -coherentVal ν ⟨η₁, hη₁⟩ ∧
        coherentVal μ ⟨η₁, hη₁⟩ = -coherentVal ν ⟨η₀, hη₀⟩)) ∧
      ∀ d : G → ℂ, (∀ η : S, cfInner d (coherentVal ν η)
          = (c : ℂ) * ((k : ℂ) - if η = (⟨η₀, hη₀⟩ : S) then 1 else 0)) →
        ∀ η : S, cfInner d (coherentVal μ η)
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
  have hbound : ∑ η : S, a η ^ 2 ≤ N := by
    have hb := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hON δ
    rw [hnorm, Complex.intCast_re] at hb
    have hrw : ∀ η ∈ (Finset.univ : Finset S), ‖cfInner δ (coherentVal ν η)‖ ^ 2
        = ((a η ^ 2 : ℤ) : ℝ) := by
      intro η _
      rw [hval η, Complex.norm_intCast]
      push_cast
      rw [sq_abs]
    rw [Finset.sum_congr rfl hrw] at hb
    exact_mod_cast hb
  have hsub : ∀ T : Finset S, ∑ x ∈ T, a x ^ 2 ≤ N := fun T =>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => sq_nonneg _) hbound
  have hi₁ : (⟨η₁, hη₁⟩ : S) ≠ ⟨η₀, hη₀⟩ := fun he => hη₁ne (congrArg Subtype.val he)
  have ha0 : a (⟨η₀, hη₀⟩ : S) = c * (k - 1) := by simp [hadef]
  have ha1 : a (⟨η₁, hη₁⟩ : S) = c * k := by simp [hadef, hi₁]
  have hcsq : 0 < c ^ 2 := by positivity
  have hpair : ∀ i j : S, i ≠ j → a i ^ 2 + a j ^ 2 ≤ N := by
    intro i j hij
    have := hsub {i, j}
    rwa [Finset.sum_pair hij] at this
  have hk : k = 0 ∨ k = 1 := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hp := hpair (⟨η₀, hη₀⟩ : S) ⟨η₁, hη₁⟩ (Ne.symm hi₁)
    rw [ha0, ha1] at hp
    have hsq0 : 1 ≤ k ^ 2 := by rcases lt_or_gt_of_ne h0 with hlt | hgt <;> nlinarith
    have hsq1 : 1 ≤ (k - 1) ^ 2 := by rcases lt_or_gt_of_ne h1 with hlt | hgt <;> nlinarith
    nlinarith
  rcases hk with h0 | h1
  ·
    refine ⟨ν, hν, rfl, Or.inl rfl, fun d hd η => ?_⟩
    rw [hd η, h0]
    split_ifs <;> push_cast <;> ring
  ·
    have huniq : ∀ χ : S, χ ≠ (⟨η₀, hη₀⟩ : S) → χ = ⟨η₁, hη₁⟩ := by
      intro χ hχ
      by_contra hne'
      have htri : a χ ^ 2 + a (⟨η₁, hη₁⟩ : S) ^ 2 + a (⟨η₀, hη₀⟩ : S) ^ 2 ≤ N := by
        have := hsub {χ, ⟨η₁, hη₁⟩, ⟨η₀, hη₀⟩}
        rw [Finset.sum_insert (by simp [hne', hχ]), Finset.sum_pair hi₁] at this
        linarith
      have hax : a χ = c * k := by simp [hadef, hχ]
      rw [hax, ha1, ha0, h1] at htri
      nlinarith
    obtain ⟨μ, hμ, hspan, hμ0⟩ := exists_isCoherentWith_swap hSIrr hSfin hν hη₀
      (⟨η₁, hη₁⟩ : S) hi₁ huniq hdeg rfl
    have hmem : η₁ - η₀ ∈ charSpanZero S := by
      refine mem_charSpanZero.2
        ⟨sub_mem (Submodule.subset_span hη₁) (Submodule.subset_span hη₀), ?_⟩
      simp only [Pi.sub_apply]
      rw [hdeg η₁ hη₁, sub_self]
    have hd1 := coe_baseline_sub hμ hη₁ hη₀ hmem
    have hd2 := coe_baseline_sub hν hη₁ hη₀ hmem
    have hμ1 : coherentVal μ (⟨η₁, hη₁⟩ : S) = -coherentVal ν (⟨η₀, hη₀⟩ : S) := by
      have hh := hd1.symm.trans hd2
      rw [hμ0] at hh
      funext x
      have hx := congrFun hh x
      simp only [Pi.sub_apply, Pi.neg_apply] at hx ⊢
      linear_combination hx
    have hSeq : S = {η₀, η₁} := by
      refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
      · by_cases hxe : x = η₀
        · exact Or.inl hxe
        · exact Or.inr
            (congrArg Subtype.val (huniq ⟨x, hx⟩ (fun he => hxe (congrArg Subtype.val he))))
      · rintro x (rfl | rfl)
        · exact hη₀
        · exact hη₁
    refine ⟨μ, hμ, hspan, Or.inr ⟨hSeq, hμ0, hμ1⟩, fun d hd η => ?_⟩
    by_cases hη : η = (⟨η₀, hη₀⟩ : S)
    · rw [hη, if_pos rfl, hμ0, cfInner_neg_right, hd (⟨η₁, hη₁⟩ : S), if_neg hi₁, h1]
      push_cast
      ring
    · rw [huniq η hη, hμ1, cfInner_neg_right, hd (⟨η₀, hη₀⟩ : S), if_pos rfl, if_neg hi₁, h1]
      push_cast
      ring

end SibleyLinearOrientation

end CFSG.FeitThompson
