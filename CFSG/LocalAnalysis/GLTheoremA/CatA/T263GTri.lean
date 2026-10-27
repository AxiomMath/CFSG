module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TNoTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPDich
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.D4T
open CFSG.LocalAnalysis.GLTheoremA.D4Y

section Certs

set_option linter.unusedSectionVars false


variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem t263_d4RankCase
    {S B : Subgroup Ω} (hSn : S.Normal) (hB : GLAIsBmax 3 B)
    (hT : ∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) :
    D4RankCase S B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBcard, -, -, -⟩ :
      CFSG.Open.IsElemAbelian 3 B ∧ Nat.card ↥B = 3 ^ GLATwoLocalRank 3 Ω ∧
        ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  obtain ⟨T, hTne, hT2, -, hBT⟩ := hT
  right
  refine ⟨fun P W hP hW2 hWne hPW => ?_, T, hT2, hTne, hBT, ?_⟩
  · rw [hBcard, glaTwoLocal_eq]
    exact card_le_of_normalizes hWne hW2 hP hPW
  · rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact le_top

private theorem t263_exists_D4
    {i : TauCeti.CFSGIndex} (hi : isD4any i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧
      i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact ⟨q, hv, hi, rfl⟩
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

private theorem t263_center_bot_d4
    {S : Subgroup Ω} (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore 3 ↥S = ⊥) (hD4 : catalogIs (↥S ⧸ Subgroup.center ↥S) isD4any) :
    Subgroup.center ↥S = ⊥ := by
  have eS : PQuot 3 S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hodd : Odd (Nat.card (Subgroup.center ↥S)) := by
    have h := FP.odd_card_center_pQuot (G := Ω) Nat.prime_three (by norm_num) S
    have hc : Nat.card (Subgroup.center ↥S) = Nat.card (Subgroup.center (PQuot 3 S)) := by
      rw [← Subgroup.map_center_eq eS]
      exact Subgroup.card_map_of_injective (f := (eS : PQuot 3 S →* ↥S)) eS.injective
    rwa [← hc] at h
  obtain ⟨i, hi, ⟨f⟩⟩ := hD4
  obtain ⟨q, hv, hp2, rfl⟩ := t263_exists_D4 hi
  have hm := CFSG.Models.lieModel_D 4 q hv f
  have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 q.p q.exponent = (1, 1) := by
    have hev : Even (q.p ^ q.exponent) := by
      rw [hp2, Nat.even_pow]
      exact ⟨even_two, q.exponent_pos.ne'⟩
    simp [CFSG.Blueprint.Multiplier.genericOrders, hev]
  have hdvd : Nat.card (Subgroup.center ↥S) ∣ 4 := by
    by_cases hex : q.exponent = 1
    · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 q.p q.exponent = (2, 2) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        rw [hp2, hex]
        rfl
      have h := card_center_dvd_of_table CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        hSq hm hg he (by norm_num)
      simpa using h
    · have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 q.p q.exponent = (1, 1) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        rw [hp2]
        split <;> simp_all
      have h := card_center_dvd_of_table CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        hSq hm hg he (by norm_num)
      have h1 : Nat.card (Subgroup.center ↥S) ∣ 1 := by simpa using h
      exact h1.trans (one_dvd _)
  have h1 : Nat.card (Subgroup.center ↥S) = 1 := by
    have h4 : Nat.card (Subgroup.center ↥S) ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [hj, h0, pow_zero]
    · exfalso
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h0.ne'⟩)
  exact Subgroup.eq_bot_of_card_eq _ h1

open CFSG.LocalAnalysis.GLTheoremA.S9 CFSG.LocalAnalysis.GLTheoremA.MI CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.FP in
theorem t263NoTri_holds
    : T263NoTri := by
  intro Ω _ _ S B hSn hSq hSp hSc hD4 hB hT c hc hnon
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hBel : CFSG.Open.IsElemAbelian 3 B := hB.1
  have hAN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact le_top
  have hcN : c ∈ Subgroup.normalizer (S : Set Ω) := hnon.1
  have hZ : Subgroup.center ↥S = ⊥ := t263_center_bot_d4 hSq hSp hD4
  let eS : PQuot 3 S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := hSq.of_mulEquiv eS
  let ez : ↥S ⧸ Subgroup.center ↥S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e₆ : PSimple 3 S ≃* ↥S ⧸ Subgroup.center ↥S :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  let e1 : PSimple 3 S ≃* ↥S := e₆.trans ez
  have hchev : IsChevSimple 2 (PSimple 3 S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  have hcomp : GLAPComponent 3 S S := glaPComponent_self_p hSq hSp
  have hD4S : catalogIs ↥S isD4any := (catalogIs_congr ez).1 hD4
  have hKc : ∀ k ∈ S, (∀ y ∈ S, y * k = k * y) → k = 1 := by
    intro k hk hcomm
    have hmem : (⟨k, hk⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hrank : D4RankCase S B := t263_d4RankCase hSn hB hT
  by_cases hn1 : catalogIs ↥S S9.isD4two
  ·
    exfalso
    have hF : D4TwoFacts ↥S :=
      (CFSG.LocalAnalysis.GLTheoremA.D4XF.d4TwoFactsAt_of_residual
        CFSG.LocalAnalysis.GLTheoremA.D4YB.d4TwoAutNormInn_holds) ↥S hn1
    have hinner : ∃ k ∈ S, ∀ y ∈ S, c * y * c⁻¹ = k * y * k⁻¹ := by
      by_contra hcon
      push Not at hcon
      exact noTriality_core hF hKc hBel hAN
        ⟨c, hc, fun k hk hall => by
          obtain ⟨y, hy, hne⟩ := hcon k hk
          exact hne (hall y hy)⟩ hrank
    obtain ⟨k, hk, hk'⟩ := hinner
    have hinn : InducesInnerMod 3 S c := by
      refine ⟨k, hk, fun y hy => ?_⟩
      have hy' : c⁻¹ * y * c ∈ S := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcN) y).1 hy
        simpa using this
      have h1 := hk' (c⁻¹ * y * c) hy'
      have h2 : c⁻¹ * y * c = k⁻¹ * y * k := by
        have e : y = k * (c⁻¹ * y * c) * k⁻¹ := by
          calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
            _ = k * (c⁻¹ * y * c) * k⁻¹ := h1
        calc c⁻¹ * y * c = k⁻¹ * (k * (c⁻¹ * y * c) * k⁻¹) * k := by group
          _ = k⁻¹ * y * k := by rw [← e]
      rw [h2, inv_mul_cancel]
      exact one_mem _
    exact hnon.2 (MI.inner_innDiag_any hcomp hchev hcN hinn)
  ·
    have hnD4 : ¬ catalogIs (PSimple 3 S) S9.isD4two := fun h => hn1 ((catalogIs_congr e1).1 h)
    have hD4P : catalogIs (PSimple 3 S) isD4any := (catalogIs_congr e₆).2 hD4
    have hcinv : c⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hcN
    have hcong : MulAut.congr e1 (indAut 3 S c hcN) = conjAut S c⁻¹ hcinv := by
      ext k
      obtain ⟨s, rfl⟩ := e1.surjective k
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl' : (c⁻¹ * (l : Ω) * c) ∈ S := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcN) (l : Ω)).1 l.2
        simpa using this
      have hrel : indRel 3 S c (QuotientGroup.mk l) (QuotientGroup.mk ⟨c⁻¹ * (l : Ω) * c, hl'⟩) :=
        ⟨l, ⟨c⁻¹ * (l : Ω) * c, hl'⟩, rfl, rfl, rfl⟩
      have he1mk : ∀ x : ↥S, e1 (QuotientGroup.mk (QuotientGroup.mk x)) = x := by
        intro x
        simp [e1, e₆, ez, eS]
        rfl
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [indAut_apply_mk hcN hrel, he1mk, he1mk]
      simp [conjAut]
    have hcentral : ∀ γ : MulAut (PSimple 3 S),
        γ * indAut 3 S c hcN * γ⁻¹ * (indAut 3 S c hcN)⁻¹ ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) := by
      intro γ
      by_contra hγ
      refine d4BigCoreAt_holds Ω S B hD4S hn1 hKc hBel hAN
        ⟨c⁻¹, inv_mem hc, hcinv, MulAut.congr e1 γ, fun hmem => hγ ?_⟩ hrank
      rw [← hcong] at hmem
      have h1 : MulAut.congr e1 (γ * indAut 3 S c hcN * γ⁻¹ * (indAut 3 S c hcN)⁻¹) ∈
          innerAut ↥S := by
        simpa only [map_mul, map_inv] using hmem
      have h2 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e1
      have h3 : MulAut.congr e1 (γ * indAut 3 S c hcN * γ⁻¹ * (indAut 3 S c hcN)⁻¹) ∈
          (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S)).map
            (MulAut.congr e1).toMonoidHom := by
        rw [h2]
        exact h1
      obtain ⟨y, hy, hyx⟩ := h3
      have : y = γ * indAut 3 S c hcN * γ⁻¹ * (indAut 3 S c hcN)⁻¹ :=
        (MulAut.congr e1).injective hyx
      exact this ▸ hy
    obtain ⟨i, hi, ⟨f⟩⟩ := hD4P
    have hi2 : ¬ S9.isD4two i := fun h => hnD4 ⟨i, h, ⟨f⟩⟩
    obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv f
    rw [hp2] at hmodel
    have h0 := Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 (t := .POmegaPlus) (n := 4)
      (f := q.exponent) (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩)
    have h1 := canon_marking_and_labelAll_simple (P' := RawInnBody 3)
      (fun lab hlab => canonRawInn' hp3 (by norm_num) hlab) h0
    have hM : CFSG.Assembly.LargeEvenMarking (PQuot 3 S) fun lab R _ I F θ =>
        ∀ φ : MulAut R, LargeEvenInduces θ (indRel 3 S c) φ → FP.CentralMod I φ := by
      refine Canonical.largeEvenMarking_mono ?_ h1
      rintro lab R _ I F θ ⟨-, hmul, hinv, hinn, -⟩ φ hφ
      have hφe := (induces_indRel_iff hcN θ).1 hφ
      intro γ
      set α := indAut 3 S c hcN with hα
      have hγ : γ = MulAut.congr θ (MulAut.congr θ.symm γ) := by ext x; simp [MulAut.congr_apply]
      have h1' : γ * φ * γ⁻¹ * φ⁻¹ = MulAut.congr θ ((MulAut.congr θ.symm γ) * α *
          (MulAut.congr θ.symm γ)⁻¹ * α⁻¹) := by
        rw [hφe]
        conv_lhs => rw [hγ]
        simp only [map_mul, map_inv]
      rw [h1']
      have hmem := hcentral (MulAut.congr θ.symm γ)
      have h2 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr θ
      have h3 : MulAut.congr θ ((MulAut.congr θ.symm γ) * α * (MulAut.congr θ.symm γ)⁻¹ * α⁻¹) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
        rw [← h2]
        exact ⟨_, hmem, rfl⟩
      obtain ⟨r, hr⟩ := h3
      rw [← hr]
      exact hinn r
    rcases fieldOn_or_td4_of_central hp3 (by norm_num) hcN (hBel.2 c hc) hnon.2 hM with hF | ⟨-, hTD4⟩
    · exact Or.inl hF
    · exact Or.inr hTD4

theorem t263Out_holds
    : T263Out := t263Out_of_noTri t263NoTri_holds

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
