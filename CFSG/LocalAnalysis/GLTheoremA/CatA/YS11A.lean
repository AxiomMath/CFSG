module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.L514BBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator

section LBalanceHelpers

variable {G : Type} [Group G] [Finite G]

private theorem layerLayerInf_eq {p : ℕ} (hp : p.Prime) (M E : Subgroup G)
    (hbal : GLAPLayer p (M ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer p M) :
    GLAPLayer p (GLAPLayer p M ⊓ Subgroup.centralizer (E : Set G)) =
      GLAPLayer p (M ⊓ Subgroup.centralizer (E : Set G)) := by
  set A : Subgroup G := M ⊓ Subgroup.centralizer (E : Set G) with hA
  set B : Subgroup G := GLAPLayer p M ⊓ Subgroup.centralizer (E : Set G) with hB
  have hBA : B ≤ A := le_inf (inf_le_left.trans (i183_glaPLayer_le p M)) inf_le_right
  have hnorm : (B.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    exact fun g hg => i183_mem_normalizer_inf (i183v_le_normalizer_glaPLayer p M hg.1)
      (Subgroup.le_normalizer hg.2)
  apply le_antisymm
  · refine sSup_le fun J hJ => le_sSup ?_
    exact i183v_comp_up hp hJ hBA
      (isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hBA hnorm))
  · refine sSup_le fun J hJ => le_sSup ?_
    exact glaPComponent_of_le hp hJ
      (le_inf ((le_sSup hJ).trans hbal) (hJ.1.trans inf_le_right)) hBA

private theorem glaPLayer_centralizer_le_top {p : ℕ} (hp : p.Prime)
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hKP : CFSG.Open.IsKProper G) {P : Subgroup G} (hP : IsPGroup p ↥P) :
    GLAPLayer p (Subgroup.centralizer (P : Set G)) ≤ GLAPLayer p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hKP' : CFSG.IsKProper G :=
    CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hKP)
  rw [i183_glaPLayer_eq, i183_glaPLayer_eq]
  refine l514b_lBalancePLayer_centralizer_le (fun M x hxM hx => ?_) P hP
  by_cases hM : M = ⊤
  · subst hM
    rw [top_inf_eq]
    exact i183v_lBalancePLayer_centralizer_element_le hS hKP' hx
  · have hK : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper hKP hM
    have hEp : IsPGroup p ↥(Subgroup.zpowers x) := by
      obtain ⟨n, hn⟩ := hx
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hn)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
        Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h := i183_glaPLayer_inf_centralizer_le hS hK hp (Subgroup.zpowers_le.2 hxM) hEp
    rw [hcz] at h
    rwa [i183_glaPLayer_eq, i183_glaPLayer_eq] at h

end LBalanceHelpers

section LBalanceEqInput


theorem lBalanceEqAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) : LBalanceEqAt G p := by
  intro hp hKP D E _ hE hDE
  have hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  by_cases hM : Subgroup.centralizer (D : Set G) = ⊤
  · rw [hM]
    refine layerLayerInf_eq hp ⊤ E ?_
    rw [top_inf_eq]
    exact glaPLayer_centralizer_le_top hp hS hKP hE
  · have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D : Set G)) :=
      isKGroup_of_isKProper hKP hM
    have hEX : E ≤ Subgroup.centralizer (D : Set G) := fun e he =>
      Subgroup.mem_centralizer_iff.2 fun d hd => hDE d hd e he
    exact layerLayerInf_eq hp _ E (i183_glaPLayer_inf_centralizer_le hS hK hp hEX hE)

end LBalanceEqInput

section LevelTwoInput


private theorem ys11a_hOrd : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
  CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

private theorem ys11a_pp_two_one (q : TauCeti.PrimePower) (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [h] at hc
  have hdvd : q.p ∣ 2 := by
    rw [hc]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hc
  exact Nat.pow_right_injective (le_refl 2)
    (show 2 ^ q.exponent = 2 ^ 1 by rw [pow_one]; exact hc.symm)

private theorem ys11a_lieModel_tA {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU (r + 1) q.p q.exponent := by
  have h := CFSG.Models.lieModel_twistedA r q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ =
      q.p := TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  rw [hc, hf] at h
  exact CFSG.Models.LieModel.toBlueprint (by decide) h

private theorem ys11a_lieModel_D4 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.POmegaPlus 4 2 1 := by
  obtain ⟨hp, hf⟩ := ys11a_pp_two_one q hq
  have h := CFSG.Models.lieModel_D 4 q hv e
  rw [hp, hf] at h
  exact CFSG.Models.LieModel.toBlueprint (by decide) h

private theorem ys11a_lieModel_U5 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU 5 2 1 := by
  obtain ⟨hp, hf⟩ := ys11a_pp_two_one q hq
  have h : CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU (4 + 1) q.p q.exponent :=
    ys11a_lieModel_tA 4 q hv e
  rw [hp, hf] at h
  exact h

private theorem ys11a_lieModel_U6 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 5 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU 6 2 1 := by
  obtain ⟨hp, hf⟩ := ys11a_pp_two_one q hq
  have h : CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU (5 + 1) q.p q.exponent :=
    ys11a_lieModel_tA 5 q hv e
  rw [hp, hf] at h
  exact h

private theorem ys11a_card_L28 {Y : Type} [Group Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 8)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group) :
    Nat.card Y = 504 := by
  have hY : CFSG.Blueprint.LieModel Y CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 1 q hv e)
  have hord := (ys11a_hOrd Y _ 2 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
  rw [← TauCeti.PrimePower.card_def q, hq] at hord
  have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
      CFSG.Open.StatedLieTag.PSL 2 8 = 1 := by decide
  have h2 : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
      CFSG.Open.StatedLieTag.PSL 2 8 = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem ys11a_card_U42 {Y : Type} [Group Y] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group) :
    Nat.card Y = 25920 := by
  have hY : CFSG.Blueprint.LieModel Y CFSG.Open.StatedLieTag.PSU 4 q.p q.exponent :=
    ys11a_lieModel_tA 3 q hv e
  have hord := (ys11a_hOrd Y _ 4 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hY) hY).2.1
  rw [← TauCeti.PrimePower.card_def q, hq] at hord
  have h1 : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor
      CFSG.Open.StatedLieTag.PSU 4 2 = 1 := by decide
  have h2 : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator
      CFSG.Open.StatedLieTag.PSU 4 2 = 25920 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

private theorem ys11a_card_ambig3 {Y : Type} [Group Y] (d1 : TauCeti.LieTypeIndex)
    (hv : d1.Valid)
    (hP : CFSG.Yardstones.Md0ec50421ce4.ambiguousChev 3 (TauCeti.CFSGIndex.lie ⟨d1, hv⟩))
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨d1, hv⟩).Group) :
    Nat.card Y = 504 ∨ Nat.card Y = 25920 := by
  cases d1 <;> try (simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP; done)
  case A r q =>
    rcases r with _ | _ | _ | r
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
    · exact Or.inl (ys11a_card_L28 q hv
        (by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hP) e)
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
  case twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP
    · exact Or.inr (ys11a_card_U42 q hv
        (by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hP) e)
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hP

private theorem ys11a_not_chev3 {S : Type} [Group S]
    (h : catalogIs S (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i)) :
    ¬ IsChevSimple 3 S := by
  intro hC
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  have key : ∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f ∧
      ((t = CFSG.Open.StatedLieTag.POmegaPlus ∧ n = 4 ∧ f = 1) ∨
        (t = CFSG.Open.StatedLieTag.PSU ∧ n = 5 ∧ f = 1) ∨
        (t = CFSG.Open.StatedLieTag.PSU ∧ n = 6 ∧ f = 1)) := by
    cases i with
    | cyclic p hp => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi
    | alternating m hm => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi
    | sporadic s => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      cases d1 <;> try (simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi; done)
      case D r q =>
        rcases r with _ | _ | _ | _ | _ | r <;>
          simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi
        exact ⟨_, _, _, ys11a_lieModel_D4 q hv (by simpa using hi) e, Or.inl ⟨rfl, rfl, rfl⟩⟩
      case twistedA r q =>
        rcases r with _ | _ | _ | _ | _ | _ | r <;>
          simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at hi
        · exact ⟨_, _, _, ys11a_lieModel_U5 q hv (by simpa using hi) e,
            Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
        · exact ⟨_, _, _, ys11a_lieModel_U6 q hv (by simpa using hi) e,
            Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  obtain ⟨t, n, f, hL, hcase⟩ := key
  have hord := (ys11a_hOrd S t n 2 f (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
  rcases hC with hA | hB
  ·
    obtain ⟨j, hj, ⟨e'⟩⟩ := hA
    have hodd : CFSG.Blueprint.OddLieType S := by
      cases j with
      | cyclic p hp => simp [onLie] at hj
      | alternating m hm => simp [onLie] at hj
      | sporadic s => simp [onLie] at hj
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        have hc3 : d1.characteristic = 3 := by simpa [onLie] using hj
        obtain ⟨t', n', f', hY⟩ :=
          CFSG.HardMathSupport.Dickson.Sec6.exists_blueprint_lieModel_of_odd ⟨d1, hv⟩
            (by change d1.characteristic ≠ 2; omega) e'
        have hY3 : CFSG.Blueprint.LieModel S t' n' 3 f' := by
          have h3 := hY
          change CFSG.Blueprint.LieModel S t' n' d1.characteristic f' at h3
          rw [hc3] at h3
          exact h3
        exact ⟨t', n', 3, f', Nat.prime_three, by decide, CFSG.Blueprint.LieModel.admissible hY3, hY3⟩
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two ys11a_hOrd hL
        (by decide) (by decide) (by decide) hodd
  ·
    obtain ⟨j, hj, ⟨e'⟩⟩ := hB
    have hc : Nat.card S = 360 ∨ Nat.card S = 504 ∨ Nat.card S = 25920 := by
      cases j with
      | cyclic p hp => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hj
      | alternating m hm =>
        have hm6 : m = 6 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hj
        subst hm6
        have e6 : S ≃* alternatingGroup (Fin 6) := e'
        haveI : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.2 (by norm_num)
        left
        rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
      | sporadic s => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hj
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases ys11a_card_ambig3 d1 hv hj e' with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    rcases hc with hc | hc | hc <;> rw [hc] at hord <;>
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      revert hord <;> decide

private theorem ys11a_k2_of_small (i : TauCeti.CFSGIndex)
    (h : S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) :
    CFSG.Yardstones.Md0ec50421ce4.k2 3 i := by
  cases i with
  | cyclic p hp => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at h
  | alternating m hm => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at h
  | sporadic s => simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at h
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 <;> try (simp [S9.isD4two, S9.isU5two, S9.isU6two, onLie] at h; done)
    case D r q =>
      rcases r with _ | _ | _ | _ | _ | r <;>
        simp_all [S9.isD4two, S9.isU5two, S9.isU6two, onLie,
          CFSG.Yardstones.Md0ec50421ce4.k2, CFSG.Yardstones.Md0ec50421ce4.k2Lie]
    case twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;>
        simp_all [S9.isD4two, S9.isU5two, S9.isU6two, onLie,
          CFSG.Yardstones.Md0ec50421ce4.k2, CFSG.Yardstones.Md0ec50421ce4.k2Lie]

theorem levelTwoAt_holds (G : Type) [Group G] [Finite G] : LevelTwoAt G := by
  intro X L hL hcat
  have hM : ListedMultiplierBound 3 :=
    listedMultiplierBound_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      sporadicMultiplierTable_holds 3
  have hH : HatOddMultiplierBound := hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds
  rw [fullCoverLevel_pQuot_eq hM hH Nat.prime_three (by norm_num) hL]
  have hk2 : catalogIs (PSimple 3 L) (CFSG.Yardstones.Md0ec50421ce4.k2 3) := by
    obtain ⟨i, hi, he⟩ := hcat
    exact ⟨i, ys11a_k2_of_small i hi, he⟩
  have hnc : ¬ IsChevSimple 3 (PSimple 3 L) := ys11a_not_chev3 hcat
  unfold kLevel
  rw [if_neg hnc, if_pos hk2]

end LevelTwoInput

end CFSG.LocalAnalysis.GLTheoremA
