module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndTight
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInnerRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mem_sup_of_isKleinFour (h : FooteSec4 G L) (hFI : FooteFourgroupInner)
    {M : Subgroup G} (hM : IsFooteM L M) {W : Subgroup G} (hW : IsKleinFour W)
    (hWN : W ≤ normalizer (M : Set G)) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ M ⊔ coreActionKernel M := by
  by_cases hA : ∃ w ∈ W, w ≠ 1 ∧ w ∈ coreActionKernel M
  · obtain ⟨w, hwW, hw1, hwC⟩ := hA
    exact ⟨w, hwW, hw1, mem_sup_right hwC⟩
  push Not at hA
  obtain ⟨hs, ⟨ε⟩⟩ := hM.quotient h
  set S := L ⧸ Open.fusionZStar L with hS
  set N := normalizer (M : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (oddBarConj M) with hΦ
  have hker : ∀ x : N, Φ x = 1 → (x : G) ∈ coreActionKernel M := by
    intro x hx
    apply mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (oddBarConj M x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  have hinj : Function.Injective (Φ.comp (W.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    by_contra hx1
    have hx1' : ((x : N) : G) ≠ 1 := fun h1 => hx1 (Subtype.ext (Subtype.ext h1))
    exact hA _ x.2 hx1' (hker _ hx)
  set W' := (W.subgroupOf N).map Φ with hW'
  have hrange : (Φ.comp (W.subgroupOf N).subtype).range = W' := by
    rw [MonoidHom.range_comp, range_subtype]
  have hW'4 : Nat.card W' = 4 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hW.card_four]
    exact Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv
  have hW'2 : ∀ e ∈ W', e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x * x = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
      exact sq_eq_one_of_isKleinFour hW hx)
    rw [← map_mul, hx2, map_one]
  obtain ⟨_, ⟨⟨w, hwN⟩, hwW, rfl⟩, hw1, ⟨s, hs⟩⟩ := hFI S h.footeFamilyType W' hW'2 hW'4
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (ε.symm s)
  have hmN : (m : G) ∈ N := le_normalizer m.2
  have hΦm : Φ ⟨m, hmN⟩ = MulAut.conj s := by
    rw [hΦ, MonoidHom.comp_apply, oddBarConj_eq_conj' m hmN]
    show MulAut.congr ε (MulAut.conj ((m : M ⧸ pPrimeCore 2 M))) = MulAut.conj s
    rw [MulAut.congr_conj, hm, MulEquiv.apply_symm_apply]
  have hC : ((⟨m, hmN⟩ : N)⁻¹ * ⟨w, hwN⟩ : N) ∈ (Φ.ker) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΦm, hs, inv_mul_cancel]
  have hmw : (m : G)⁻¹ * w ∈ coreActionKernel M := hker _ (MonoidHom.mem_ker.mp hC)
  refine ⟨w, hwW, fun h1 => hw1 (by rw [show (⟨w, hwN⟩ : N) = 1 from Subtype.ext h1, map_one]),
    ?_⟩
  rw [show w = (m : G) * ((m : G)⁻¹ * w) by group]
  exact mul_mem (mem_sup_left m.2) (mem_sup_right hmw)

omit [Finite G] in
theorem mem_normalizer_of_forall_commute {U : Subgroup G} {w : G}
    (h : ∀ u ∈ U, u * w = w * u) : w ∈ normalizer (U : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : w * x * w⁻¹ = x := by rw [← h x hx]; group
    rw [h1]
    exact hx
  · intro hx
    have h1 := h _ hx
    have h2 : x = w * x * w⁻¹ := by
      calc x = w⁻¹ * ((w * x * w⁻¹) * w) := by group
        _ = w⁻¹ * (w * (w * x * w⁻¹)) := by rw [h1]
        _ = w * x * w⁻¹ := by group
    rw [h2]
    exact hx

theorem false_of_commuting_fourgroups (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) {M : Subgroup G}
    (hM : IsFooteM L M) (hne : FooteNoEscape M) {g : G} (hg : g ∉ normalizer (M : Set G))
    {U W : Subgroup G} (hU : IsKleinFour U) (hUC : U ≤ coreActionKernel (conjugate M g))
    (hW : IsKleinFour W) (hWC : W ≤ coreActionKernel M)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) : False := by
  set M' := conjugate M g with hM'def
  have hM' : IsFooteM L M' := isFooteM_conjugate h hM g
  have hne' : FooteNoEscape M' := hne.conjugate g
  have hWU : W ≤ normalizer (U : Set G) := fun w hw =>
    mem_normalizer_of_forall_commute fun u hu => hUW u hu w hw
  have hUW' : U ≤ normalizer (W : Set G) := fun u hu =>
    mem_normalizer_of_forall_commute fun w hw => (hUW u hu w hw).symm
  have hWN' : W ≤ normalizer (M' : Set G) :=
    hWU.trans (foote_cor_4_8_iv h h47 hST hM' hUC hU le_rfl)
  have hUN : U ≤ normalizer (M : Set G) :=
    hUW'.trans (foote_cor_4_8_iv h h47 hST hM hWC hW le_rfl)
  obtain ⟨w, hwW, hw1, hwMC⟩ := exists_mem_sup_of_isKleinFour h hFI hM' hW hWN'
  have hw2 : orderOf w = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hW hwW) hw1
  obtain ⟨F₂, hF₂, hF₂2, hF₂8⟩ := exists_card_eight_le_inf_centralizer h h47 hM' hw2 hwMC
  have hF₂N : F₂ ≤ normalizer (M : Set G) := hF₂.trans (inf_le_right.trans (hne w (hWC hwW) hw2))
  obtain ⟨u, huU, hu1, huMC⟩ := exists_mem_sup_of_isKleinFour h hFI hM hU hUN
  have hu2 : orderOf u = 2 := orderOf_eq_prime (sq_eq_one_of_isKleinFour hU huU) hu1
  obtain ⟨F₁, hF₁, hF₁2, hF₁8⟩ := exists_card_eight_le_inf_centralizer h h47 hM hu2 huMC
  have hF₁N : F₁ ≤ normalizer (M' : Set G) :=
    hF₁.trans (inf_le_right.trans (hne' u (hUC huU) hu2))
  have hMN' : M ≤ normalizer (M' : Set G) :=
    le_of_forall_centralizer_le_e8 h hK hM hF₂N hF₂2 hF₂8 fun t ht ht2 =>
      hne' t (hF₂ ht).1 ht2
  have hM'N : M' ≤ normalizer (M : Set G) :=
    le_of_forall_centralizer_le_e8 h hK hM' hF₁N hF₁2 hF₁8 fun t ht ht2 =>
      hne t (hF₁ ht).1 ht2
  have hc : ⁅M, M'⁆ ≤ M ⊓ M' := commutator_le_inf_of_le_normalizer hMN' hM'N
  have heq := foote_theorem_4_6 h hA5 hE8 hK hcalc hM hM' hc hF₁2 hF₁8
    (le_inf (hF₁.trans inf_le_left) hF₁N) hF₂2 hF₂8 (le_inf (hF₂.trans inf_le_left) hF₂N)
  exact hg (mem_normalizer_of_conjugate_eq heq.symm)

end CFSG.ComponentClassification.FooteLit
