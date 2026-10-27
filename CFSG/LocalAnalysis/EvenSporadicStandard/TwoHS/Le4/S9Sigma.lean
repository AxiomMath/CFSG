module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCover
public import Certificates.Certificate26750

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

structure HSCtx : Prop where
  perfect : Group.IsPerfect HSCover
  card_center : Nat.card (center HSCover) = 2
  quotient : IsSporadic (HSCover ⧸ center HSCover) .HS

@[expose] def hsGens : List HSCover := (List.finRange 6).map PresentedGroup.of

section Ctx


theorem HSCtx.card_eq (h : HSCtx) : Nat.card HSCover = 88704000 :=
  card_eq_of_double_cover h.card_center h.quotient

theorem HSCtx.finite (h : HSCtx) : Finite HSCover :=
  Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)

@[expose] noncomputable def HSCtx.coverMaps (h : HSCtx) : CoverMaps HSCover :=
  have := h.finite
  { g := fun i => PresentedGroup.of i
    ρ := harRhoHom
    π := harPiHom
    ρ_g := fun i => harRhoHom_of i
    π_g := fun i => harPiHom_of i
    π_surj := harPiHom_surjective
    π_ker := fun x => by
      have hker2 : Nat.card (harPiHom : HSCover →* ↥hsP).ker = 2 := by
        have h1 := Subgroup.card_ker_mul_card_range (harPiHom : HSCover →* ↥hsP)
        rw [MonoidHom.range_eq_top.2 harPiHom_surjective, Subgroup.card_top, h.card_eq,
          card_hsP] at h1
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans (by norm_num))
      have hkc : (harPiHom : HSCover →* ↥hsP).ker ≤ center HSCover := by
        obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : ↥(harPiHom : HSCover →* ↥hsP).ker)).1 hker2
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro g
        by_cases hz1 : z = 1
        · rw [hz1]; simp
        · have h1 : (⟨z, hz⟩ : ↥(harPiHom : HSCover →* ↥hsP).ker) = x :=
            hx _ (fun h => hz1 (congrArg Subtype.val h))
          have hgz : g * z * g⁻¹ ∈ (harPiHom : HSCover →* ↥hsP).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv]
            have : harPiHom z = 1 := hz
            rw [this]; simp
          have hgz1 : g * z * g⁻¹ ≠ 1 := by
            intro h
            apply hz1
            have h' : z = g⁻¹ * (g * z * g⁻¹) * g := by group
            rw [h', h]
            simp
          have h2 : (⟨g * z * g⁻¹, hgz⟩ : ↥(harPiHom : HSCover →* ↥hsP).ker) = x :=
            hx _ (fun h => hgz1 (congrArg Subtype.val h))
          have h3 : g * z * g⁻¹ = z := congrArg Subtype.val (h2.trans h1.symm)
          calc g * z = g * z * g⁻¹ * g := by group
            _ = z * g := by rw [h3]
      have hkeq : (harPiHom : HSCover →* ↥hsP).ker = center HSCover :=
        Subgroup.eq_of_le_of_card_ge hkc (by rw [hker2, h.card_center])
      rw [← hkeq, MonoidHom.mem_ker] }

theorem HSCtx.rho_injective (h : HSCtx) : Function.Injective harRhoHom := by
  have := isSimpleGroup_hsP
  exact (h.coverMaps).rho_injective h.perfect h.card_center

end Ctx


theorem fixCnt_eq {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    fixCnt n T = (Finset.univ.filter fun i : Fin n => g i = i).card := by
  unfold fixCnt
  have h1 : ((List.finRange n).filter fun i : Fin n => ap T i.val == i.val) =
      (List.finRange n).filter fun i : Fin n => decide (g i = i) := by
    apply List.filter_congr
    intro i _
    have h2 : ap T i.val = (g i).val := by
      rw [hT i.val i.2, idx_of_lt g i.2]
      rfl
    rw [h2, Bool.eq_iff_iff]
    simp [Fin.ext_iff]
  rw [h1, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

theorem card_fix_conj {n : ℕ} (a b : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i : Fin n => (a * b * a⁻¹) i = i).card =
      (Finset.univ.filter fun i : Fin n => b i = i).card := by
  refine Finset.card_bij (fun i _ => a.symm i) ?_ ?_ ?_
  · intro i hi
    have hi' : a (b (a.symm i)) = i := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have := congrArg a.symm hi'
    simpa using this
  · intro i _ j _ h
    exact a.symm.injective h
  · intro j hj
    have hj' : b j = j := (Finset.mem_filter.1 hj).2
    refine ⟨a j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    show a (b (a.symm (a j))) = a j
    simp [hj']

theorem sigWords_letters : ∀ w ∈ sigWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6 := by decide

theorem sigWord_letters {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    ∀ l ∈ sigWord w, 1 ≤ l ∧ l ≤ 6 := by
  intro l hl
  obtain ⟨u, hu, hlu⟩ := List.mem_flatten.1 hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  have hmem : sigWords.getD (a - 1) [] ∈ sigWords := by
    obtain ⟨ha1, ha2⟩ := hw a ha
    have : a - 1 < sigWords.length := by
      have : sigWords.length = 6 := rfl
      omega
    rw [List.getD_eq_getElem _ _ this]
    exact List.getElem_mem _
  exact sigWords_letters _ hmem l hlu

section Words


theorem hsGens_map_rho : hsGens.map harRhoHom = harYs.map (tp 11200) := by
  simp only [hsGens, harYs, List.map_map, Function.comp_def, harRhoHom_of]
  rfl

theorem rep_rho_wordVal (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    Rep 11200 (wordTbl 11200 harYs w) (harRhoHom (wordVal hsGens w)) := by
  have hr := rep_wordTbl'' (n := 11200) (by norm_num) harYs_perm w (by
    rw [harYs_length]
    exact hw)
  rw [map_wordVal, hsGens_map_rho]
  exact hr

end Words

section Sigma


@[expose] noncomputable def sigmaGen (i : Fin 6) : HSCover :=
  wordVal hsGens (sigWords.getD i.val [])

theorem sigWords_getD_mem (i : Fin 6) : sigWords.getD i.val [] ∈ sigWords := by
  have : i.val < sigWords.length := by
    have : sigWords.length = 6 := rfl
    omega
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem _

theorem rep_sigmaGen (i : Fin 6) : Rep 11200 (sigY i) (harRhoHom (sigmaGen i)) :=
  rep_rho_wordVal _ (sigWords_letters _ (sigWords_getD_mem i))

theorem rho_lift {ι : Type} (f : ι → HSCover) (x : FreeGroup ι) :
    harRhoHom (FreeGroup.lift f x) = FreeGroup.lift (fun i => harRhoHom (f i)) x := by
  have : harRhoHom.comp (FreeGroup.lift f) = FreeGroup.lift (fun i => harRhoHom (f i)) :=
    FreeGroup.ext_hom _ _ (fun i => by simp)
  exact DFunLike.congr_fun this x

theorem sigPerm_relators (h : sigmaOK = true) :
    (∀ i, ∀ r ∈ wordSet hsRels,
      ⁅harRhoHom (sigmaGen i), FreeGroup.lift (fun j => harRhoHom (sigmaGen j)) r⁆ = 1) ∧
      ∀ i, FreeGroup.lift (fun j => harRhoHom (sigmaGen j)) (hsCommW i) =
        harRhoHom (sigmaGen i) := by
  simp only [sigmaOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨hperm, hrel⟩, hcomm⟩, -⟩, -⟩ := h
  have hn : (11200 : ℕ) < 2 ^ 32 := by norm_num
  have hinv : ∀ i, Rep 11200 (sigYI i) (harRhoHom (sigmaGen i))⁻¹ := fun i =>
    Rep.inv_of_invOK (rep_sigmaGen i) (hperm i).2
  constructor
  · intro i r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have := rep_evalW hn (g := sigY) (gi := sigYI) (f := fun j => harRhoHom (sigmaGen j))
      rep_sigmaGen hinv w
    have hc := (commTT_iff (rep_sigmaGen i) this).1 (hrel w hw i)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc
  · intro i
    have := rep_evalW hn (g := sigY) (gi := sigYI) (f := fun j => harRhoHom (sigmaGen j))
      rep_sigmaGen hinv (hsCommWord i)
    exact (tblEq_iff_eq this (rep_sigmaGen i)).1 (hcomm i)

theorem HSCtx.sigma_relators (hΛ : HSCtx) (h : sigmaOK = true) :
    ∀ r ∈ coverRelators (wordSet hsRels) hsCommW, FreeGroup.lift sigmaGen r = 1 := by
  rw [lift_coverRelators_eq_one_iff]
  obtain ⟨h1, h2⟩ := sigPerm_relators h
  constructor
  · intro i r hr
    apply hΛ.rho_injective
    rw [map_one, map_commutatorElement, rho_lift]
    exact h1 i r hr
  · intro i
    apply hΛ.rho_injective
    rw [rho_lift]
    exact h2 i

@[expose] noncomputable def HSCtx.sigma (hΛ : HSCtx) : HSCover →* HSCover :=
  PresentedGroup.toGroup (f := sigmaGen) (hΛ.sigma_relators Certificates.certificate26750)

theorem HSCtx.sigma_of (hΛ : HSCtx) (i : Fin 6) :
    hΛ.sigma (PresentedGroup.of i) = sigmaGen i := PresentedGroup.toGroup.of _

theorem HSCtx.sigma_wordVal (hΛ : HSCtx) (w : List ℕ) :
    hΛ.sigma (wordVal hsGens w) = wordVal hsGens (sigWord w) := by
  have hlen : hsGens.length = 6 := by simp [hsGens]
  have hlen' : sigWords.length = 6 := rfl
  have hl : ∀ l : ℕ,
      hΛ.sigma (hsGens.getD (l - 1) 1) = wordVal hsGens (sigWords.getD (l - 1) []) := by
    intro l
    by_cases hlt : l - 1 < 6
    · have e1 : hsGens.getD (l - 1) 1 = PresentedGroup.of (⟨l - 1, hlt⟩ : Fin 6) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [hsGens]
      rw [e1, hΛ.sigma_of]
      rfl
    · have e1 : hsGens.getD (l - 1) 1 = 1 := List.getD_eq_default _ _ (by omega)
      have e2 : sigWords.getD (l - 1) [] = [] := List.getD_eq_default _ _ (by omega)
      rw [e1, e2, map_one]
      rfl
  unfold wordVal
  rw [map_list_prod, List.map_map]
  simp only [sigWord, List.map_flatten, List.prod_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  exact hl l

theorem HSCtx.sigma_sigma (hΛ : HSCtx) (x : HSCover) : hΛ.sigma (hΛ.sigma x) = x := by
  have hs := Certificates.certificate26750
  simp only [sigmaOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hs
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hsq⟩, -⟩ := hs
  have : hΛ.sigma.comp hΛ.sigma = MonoidHom.id HSCover := by
    apply PresentedGroup.ext
    intro i
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [hΛ.sigma_of]
    unfold sigmaGen
    rw [hΛ.sigma_wordVal]
    apply hΛ.rho_injective
    have h1 := rep_rho_wordVal (sigWord (sigWords.getD i.val []))
      (sigWord_letters (sigWords_letters _ (sigWords_getD_mem i)))
    have h2 : Rep 11200 (harY i) (harRhoHom (PresentedGroup.of i)) := by
      rw [harRhoHom_of]
      exact (rep_harY i).1
    exact (tblEq_iff_eq h1 h2).1 (hsq i)
  exact DFunLike.congr_fun this x

@[expose] noncomputable def HSCtx.sigmaAut (hΛ : HSCtx) : MulAut HSCover where
  toFun := hΛ.sigma
  invFun := hΛ.sigma
  left_inv := hΛ.sigma_sigma
  right_inv := hΛ.sigma_sigma
  map_mul' := map_mul _

theorem HSCtx.sigma_not_inner (hΛ : HSCtx) : ¬ ∃ l : HSCover, ∀ x, hΛ.sigma x = l * x * l⁻¹ := by
  rintro ⟨l, hl⟩
  have hs := Certificates.certificate26750
  simp only [sigmaOK, Bool.and_eq_true] at hs
  obtain ⟨-, hne⟩ := hs
  have hx : Rep 11200 (wordTbl 11200 harYs outerWord) (harRhoHom (wordVal hsGens outerWord)) :=
    rep_rho_wordVal _ (by decide)
  have hsx : Rep 11200 (wordTbl 11200 harYs (sigWord outerWord))
      (harRhoHom (hΛ.sigma (wordVal hsGens outerWord))) := by
    rw [hΛ.sigma_wordVal]
    exact rep_rho_wordVal _ (sigWord_letters (by decide))
  have hc : harRhoHom (hΛ.sigma (wordVal hsGens outerWord)) =
      harRhoHom l * harRhoHom (wordVal hsGens outerWord) * (harRhoHom l)⁻¹ := by
    rw [hl]
    simp [map_mul, map_inv]
  rw [fixCnt_eq hx, fixCnt_eq hsx, hc, card_fix_conj] at hne
  simp at hne

end Sigma

end CFSG.EvenSporadicStandard.TwoHS
