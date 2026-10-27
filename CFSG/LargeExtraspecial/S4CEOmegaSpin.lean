module

public import CFSG.LargeExtraspecial.S4CEToolTwo
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LargeExtraspecial.O62Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

section Elementary

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem omegaGroup_eq_elementaryGroup (hQ : Q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {P P' : HypPair Q} (hPP' : P.Orth P') :
    omegaGroup Q hQ = elementaryGroup Q := by
  refine le_antisymm ?_ (O62.elementaryGroup_le_omegaGroup hQ)
  rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6]
  refine commutator_le_of_le_closure (S := Set.range (reflect Q))
    (fun g hg x hx => conj_mem_elementaryGroup hg hx) (elementaryGroup_le_orthogonalGroup Q)
    (by rintro _ ⟨v, rfl⟩; exact reflect_mem_orthogonalGroup Q v) ?_ ?_
  · rw [orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl (by omega))]
    exact closure_mono Set.subset_union_left
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact commutatorElement_reflect_mem hQ hPP' u v

theorem range_spinAction_eq_omegaGroup (hQ : Q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {P P' : HypPair Q} (hPP' : P.Orth P') :
    (CFSG.LieType.Universal.Spin.spinAction Q).range = omegaGroup Q hQ := by
  rw [CFSG.LieType.Universal.Spin.range_spinAction_eq_elementaryGroup hQ (by omega) hPP',
    omegaGroup_eq_elementaryGroup hQ h6 hPP']

end Elementary

section MinusThree

open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem elementaryGroup_le_map_iSup_minusRootGroup_three :
    elementaryGroup (quadMinus 3 F b c) ≤
      (⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ).map
        (spinAction (quadMinus 3 F b c)) := by
  refine (minusFrame 3 b c).toHypFrame.elementaryGroup_le_map_spinAction ?_ ?_ ?_
  · intro i j hij s t x
    have hγ := mem_roots_of_toStdB_eq_long 3 hij s t
      (toStdB_ofStdB (3 - 1) (Pi.single i (boolSign s) + Pi.single j (boolSign t)))
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (longRoot_mem_minusRootGroup 3 hirr hij s t (toStdB_ofStdB (3 - 1) _) x))
  · intro i s v hv
    rw [eq_planeVec_of_polar_minusVec 3 b c hv, minusFrame_vec,
      ← spinAction_twShortRoot_eq_eichler 3 hirr i s]
    have hγ := mem_roots_of_toStdB_eq_short 3 i s
      (toStdB_ofStdB (3 - 1) (Pi.single i (boolSign s)))
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (twShortRoot_mem_minusRootGroup 3 hirr i s (toStdB_ofStdB (3 - 1) _) _)))
  · intro v hv hQ
    rw [eq_planeVec_of_polar_minusVec 3 b c hv] at hQ ⊢
    rw [quadMinus_planeVec'] at hQ
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQ
    rw [hw, planeVec_zero]

theorem iSup_minusRootGroup_three_eq_top [Finite F] [CharP F 2] :
    ⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ = ⊤ := by
  have := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
  have hker := ker_spinAction_eq_bot_of_isCentral (quadMinus 3 F b c) CharTwo.two_eq_zero
  have hrange : (spinAction (quadMinus 3 F b c)).range = elementaryGroup (quadMinus 3 F b c) :=
    range_spinAction_eq_elementaryGroup (nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin]
        omega)
      (minusPair_orth (K := F) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp))
  rw [eq_top_iff]
  intro g _
  have hg : spinAction (quadMinus 3 F b c) g ∈ elementaryGroup (quadMinus 3 F b c) :=
    hrange ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩
  obtain ⟨r, hr, hrg⟩ := elementaryGroup_le_map_iSup_minusRootGroup_three hirr hg
  rwa [(MonoidHom.ker_eq_bot_iff _).mp hker hrg] at hr

theorem minusDatum_isCTGroupDatum_three_charTwo [Finite F] [CharP F 2] :
    IsCTGroupDatum (coxeterMatrix (minusDatum 3 hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum 3 hirr).isFiniteType) (minusDatum 3 hirr).roots
      (minusDatum 3 hirr).rootGroup (minusWeyl 3 hirr) (minusTorus 3 hirr) where
  n_mem := minusDatum_n_mem 3 hirr
  conj_mem := minusDatum_conj_mem 3 hirr
  braid := minusDatum_braid 3 hirr
  H_le := minusDatum_H_le 3 hirr
  sq_mem := minusDatum_sq_mem 3 hirr
  H_conj_mem := minusDatum_H_conj_mem 3 hirr
  conj_H_mem := minusDatum_conj_H_mem 3 hirr
  le_rankOne := minusDatum_le_rankOne 3 hirr
  iSup_eq_top := iSup_minusRootGroup_three_eq_top hirr

open CFSG.LieType.Steinberg CFSG.LieType.CentralExt CFSG.SectionRank.EvenCover in
theorem spinMinusThree_central_odd_extension_splitting
    {k : Type} [Field k] [Finite k] [CharP k 2] {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus 3 k b c)} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadMinus 3 k b c) →* E, ∀ x, π (σ x) = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap k (ShortField b c)).injective _
  have hC := not_two_dvd_of_odd hodd
  suffices hex : ∃! σ : spinGroup (quadMinus 3 k b c) →* E, ∀ x, π (σ x) = x by
    obtain ⟨σ, hσ, -⟩ := hex
    exact ⟨σ, hσ⟩
  refine existsUnique_section_of_rankOne_lift (minusDatum_isCTGroupDatum_three_charTwo hirr)
    (minusDatum_steinbergExtras 3 hirr) (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hker
    hC fun i => ?_
  by_cases hi : i.val + 1 < 3 - 1
  · obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hker hC
      ((minusFrame 3 b c).longSL2 (succ_ne_of_lt 3 hi) true false)
    exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt 3 hirr hi).le fun g => DFunLike.congr_fun hρ' g
  · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras 3 hirr) i
      (shortRels 3 hirr i) (mem_minusRootGroup_single_iff hirr hi)
      (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
      (fun t ht h1 => shortRels_h_eq_one_of_charTwo hirr i ht h1) hπ hker hC

end MinusThree

section Models

open CFSG.LieType.Universal.Spin

theorem spinAction_quadPlus_injective (n : ℕ) :
    Function.Injective (spinAction (quadPlus n (ZMod 2))) := by
  have := isCentral_cliffordAlgebra_quadPlus (ZMod 2) n
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero)

theorem spinAction_quadMinus_injective (n : ℕ) {b c : ZMod 2}
    (hirr : ∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (spinAction (quadMinus n (ZMod 2) b c)) := by
  have := isCentral_cliffordAlgebra_quadMinus n b c hirr
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero)

theorem range_spinAction_quadPlus_eq_omegaGroup {n : ℕ} (hn : 3 ≤ n) :
    (spinAction (quadPlus n (ZMod 2))).range =
      omegaGroup (quadPlus n (ZMod 2)) (nondegenerate_polarBilin_quadPlus n (ZMod 2)) :=
  range_spinAction_eq_omegaGroup _
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega)
    (plusPair_orth (K := ZMod 2) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]))

theorem range_spinAction_quadMinus_eq_omegaGroup {n : ℕ} (hn : 3 ≤ n) {b c : ZMod 2}
    (hirr : ∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) :
    (spinAction (quadMinus n (ZMod 2) b c)).range =
      omegaGroup (quadMinus n (ZMod 2) b c)
        (nondegenerate_polarBilin_quadMinus_of_finite n (ZMod 2) hirr) :=
  range_spinAction_eq_omegaGroup _
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega)
    (minusPair_orth (K := ZMod 2) (b := b) (c := c) (i := ⟨0, by omega⟩)
      (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))

end Models

section Transport

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {Q' : QuadraticForm (ZMod 2) W}

theorem range_conjL_symm_comp_eq_omegaGroup (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) {L : V ≃ₗ[ZMod 2] W} (hL : ∀ v, Q' (L v) = Q v)
    {G : Type*} [Group G] {φ : G →* (W ≃ₗ[ZMod 2] W)} (hφ : φ.range = omegaGroup Q' hQ') :
    ((O62.conjL L).symm.toMonoidHom.comp φ).range = omegaGroup Q hQ := by
  ext x
  rw [MonoidHom.range_comp, Subgroup.mem_map_equiv, MulEquiv.symm_symm, hφ,
    O62.mem_omegaGroup_conjL hQ hQ' hL]

end Transport

namespace CEHyp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]
  {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem ker_eq_bot_of_injective_of_split [Finite K] (h : CEHyp π E a X E₀)
    (h2 : IsPGroup 2 E) (hodd : Odd (Nat.card π.ker)) {G : Type*} [Group G]
    (ψ : G →* (V ≃ₗ[ZMod 2] V)) (hψ : Function.Injective ψ) (hrange : ψ.range = X)
    (hsplit : ∀ ρ : K →* G, Function.Surjective ρ → ρ.ker ≤ center K →
      Odd (Nat.card ρ.ker) → ∃ σ : G →* K, ∀ x, ρ (σ x) = x) : π.ker = ⊥ := by
  have hr : π.range = ψ.range := h.range_eq.trans hrange.symm
  set ρ : K →* G := ((MonoidHom.ofInjective hψ).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr hr).toMonoidHom).comp π.rangeRestrict with hρdef
  have hρ : ∀ k, ψ (ρ k) = π k := by
    intro k
    rw [hρdef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, ← MonoidHom.ofInjective_apply hψ, MulEquiv.apply_symm_apply]
    rfl
  have hker : ρ.ker = π.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hρ k]
    exact ⟨fun h1 => by rw [h1, map_one], fun h1 => hψ (h1.trans (map_one ψ).symm)⟩
  have hsurj : Function.Surjective ρ := by
    intro g
    obtain ⟨k, hk⟩ : ψ g ∈ π.range := hr ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩
    exact ⟨k, hψ ((hρ k).trans hk)⟩
  obtain ⟨σ, hσ⟩ := hsplit ρ hsurj (hker ▸ h.ker_le_center) (hker ▸ hodd)
  have hcomp : π.comp σ = ψ := MonoidHom.ext fun x => by
    rw [MonoidHom.comp_apply, ← hρ, hσ]
  exact h.ker_eq_bot_of_hom_of_odd h2 hodd σ (by rw [hcomp]; exact hψ)
    (by rw [hcomp, hrange])

end CEHyp

end CFSG.LargeExtraspecial.S4
