module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2Odd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangG2EvenData
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Lang.Proving.SLTwoThreePrime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.SeitzGeneration GL83.I713
  CFSG.RankThree.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.OutStructure

section Three


private theorem three_dvd_card_g2ShortSL2 {K : Type} [Field K] [Finite K] :
    3 ∣ Nat.card (KS11Lie4Proof.g2ShortSL2 K) := by
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.HardMathSupport.Lang.Proving.three_dvd_card_specialLinearGroup_two

theorem exists_perfect_le_centralizer_G2_three {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK : 4 ≤ Nat.card K) {z : adjointGroup Tag.G2 K} (hz : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    ∃ P : Subgroup (adjointGroup Tag.G2 K),
      P ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 K)) ∧ ⁅P, P⁆ = P ∧
        3 ∣ Nat.card P := by
  obtain ⟨g, hgS | hgL⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK z hz hz1
  · have hperf : ⁅KS11Lie4Proof.g2LongSL2 K, KS11Lie4Proof.g2LongSL2 K⁆ =
        KS11Lie4Proof.g2LongSL2 K := by
      haveI : Group.IsPerfect ↥(KS11Lie4Proof.g2LongSL2 K) :=
        KS11Lie4Proof.isPerfect_g2LongSL2 hK
      exact Subgroup.commutator_eq_self
    have hcent : KS11Lie4Proof.g2LongSL2 K ≤
        Subgroup.centralizer ({g * z * g⁻¹} : Set (adjointGroup Tag.G2 K)) := by
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (KS11Lie4Proof.g2Short_commute_g2Long hgS hm).symm
    have hdvd : 3 ∣ Nat.card (KS11Lie4Proof.g2LongSL2 K) := by
      rw [KS11Lie4Proof.card_g2LongSL2_eq]
      exact three_dvd_card_g2ShortSL2
    obtain ⟨P, hPc, hPp, hPd⟩ := exists_perfect_le_centralizer_of_conj (g := g⁻¹)
      (x := g * z * g⁻¹) ⟨KS11Lie4Proof.g2LongSL2 K, hcent, hperf, hdvd⟩
    refine ⟨P, ?_, hPp, hPd⟩
    have hz' : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [hz'] at hPc
  · have hperf : ⁅KS11Lie4Proof.g2ShortSL2 K, KS11Lie4Proof.g2ShortSL2 K⁆ =
        KS11Lie4Proof.g2ShortSL2 K := by
      haveI : Group.IsPerfect ↥(KS11Lie4Proof.g2ShortSL2 K) :=
        (KS11Lie4Proof.isQuasisimple_g2ShortSL2 hK).1
      exact Subgroup.commutator_eq_self
    have hcent : KS11Lie4Proof.g2ShortSL2 K ≤
        Subgroup.centralizer ({g * z * g⁻¹} : Set (adjointGroup Tag.G2 K)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact KS11Lie4Proof.g2Short_commute_g2Long hs hgL
    have hdvd : 3 ∣ Nat.card (KS11Lie4Proof.g2ShortSL2 K) := three_dvd_card_g2ShortSL2
    obtain ⟨P, hPc, hPp, hPd⟩ := exists_perfect_le_centralizer_of_conj (g := g⁻¹)
      (x := g * z * g⁻¹) ⟨KS11Lie4Proof.g2ShortSL2 K, hcent, hperf, hdvd⟩
    refine ⟨P, ?_, hPp, hPd⟩
    have hz' : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [hz'] at hPc

end Three

section AddOne

variable {K : Type} [Field K] [Finite K]


theorem perfectCentralizerPlanes_adjointGroup_G2_of_dvd_add_one {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.G2 K) := by
  classical
  let β : Fin Tag.G2.rank → ℤ := Pi.single ⟨0, by decide⟩ 1
  have hβ : IsRoot Tag.G2 β := IsRoot.basis _
  by_cases hodd : Odd (Nat.card K)
  · obtain ⟨K₂, hF₂, hfin₂, Γ, E, hframe, ⟨e⟩⟩ :=
      exists_langFrame_G2_odd K hodd hp hp5 hpK
    letI : Field K₂ := hF₂
    letI : Finite K₂ := hfin₂
    have hplanes : PerfectCentralizerPlanes p ↥Γ :=
      perfectCentralizerPlanes_of_isLangFrame hp hframe hβ
    exact PerfectCentralizerPlanes.of_mulEquiv e.symm hplanes
  · have heven : Even (Nat.card K) := Nat.not_odd_iff_even.mp hodd
    haveI : Fintype K := Fintype.ofFinite K
    have h2 : ringChar K = 2 := by
      rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card,
        ← Nat.dvd_iff_mod_eq_zero]
      exact even_iff_two_dvd.mp heven
    haveI : CharP K 2 := h2 ▸ ringChar.charP K
    obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := K)
    letI : Field K₂ := hF₂
    letI : Finite K₂ := hfin₂
    letI : Algebra K K₂ := hAlg
    obtain ⟨P, g, -, ⟨S₀, hS₀⟩, -, ⟨E, hEmem, hEle, hEcard⟩, hρ, hcent⟩ :=
      even_lang_setup (X := K) (K₂ := K₂) hp (by omega) hpK hdeg σ hσ
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (ModGL Tag.G2 K₂) := finite_modGL
    haveI : Finite ↥(conjEntrywiseImage K g) := Subtype.finite
    have hsylow : ∀ F : Subgroup (ModGL Tag.G2 K₂), F ≤ conjEntrywiseImage K g →
        (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
        ∃ h ∈ conjEntrywiseImage K g, F.map (MulAut.conj h).toMonoidHom ≤ E :=
      fun F hF hFp _ => exists_conj_le_of_sylow_torsion_modGL S₀ hS₀
        (fun x hx hxp => (hEmem x).2 ⟨hx.1, hxp⟩) hF hFp
    have hcomp : ∀ β : Fin Tag.G2.rank → ℤ, IsRoot Tag.G2 β →
        ∀ a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit Tag.G2 a ∈ E →
          rootDiagUnit Tag.G2 a ≠ 1 → rootChar a β = 1 →
          ∃ L : Subgroup (ModGL Tag.G2 K₂),
            L ≤ conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a} ∧
              CFSG.IsQuasisimple L ∧ ¬ Nat.Coprime p (Nat.card L) :=
      fun β hβ a h1 h2 h3 => by
        obtain ⟨L, -, hLle, hLq, -, hLnc⟩ := component_of_rankOneCentralizers hp hpK
          (fun α _ => rootSL2_injective_of_field α) hEmem hEle hρ
          (fun a ha haord hne => (hcent a ha haord).2 hne) β hβ a h1 h2 h3
        exact ⟨L, hLle, hLq, hLnc⟩
    have hplanes : PerfectCentralizerPlanes p ↥(conjEntrywiseImage K g) :=
      perfectCentralizerPlanes_of_conj_le_of_components hp (hEle.trans inf_le_left) hsylow
        hcomp hβ
    let ψ : ModGL Tag.G2 K →* ModGL Tag.G2 K₂ :=
      (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))
    have hψ : Function.Injective ψ :=
      (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap K K₂))
    exact PerfectCentralizerPlanes.of_mulEquiv
      (Subgroup.equivMapOfInjective (adjointGroup Tag.G2 K) ψ hψ).symm hplanes

end AddOne

section Catalogue


theorem perfectCentralizerPlanes_cat_G2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) : PerfectCentralizerPlanes p (Cat ⟨.G2 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.G2 K) := Subtype.finite
  have hplanes : PerfectCentralizerPlanes p (adjointGroup Tag.G2 K) := by
    rcases eq_or_ne p 3 with rfl | hp3
    · have hp3K : ringChar K ≠ 3 := by
        intro h3
        exact hpq (CharP.eq K hKchar (h3 ▸ ringChar.charP K)).symm
      have h3K : ¬ 3 ∣ Nat.card K := by
        rw [hK]
        exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_three hpq
      have h4 : 4 ≤ Nat.card K := by
        have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
          ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
        have hqne3 : q.card ≠ 3 := by
          intro h
          apply h3K
          rw [hK, h]
        rw [hK]
        have hq4 : 3 < q.card := lt_of_le_of_ne hq3 (Ne.symm hqne3)
        omega
      intro E hE hEcard
      have h1 : 1 < Nat.card E := by rw [hEcard]; norm_num
      haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp h1
      obtain ⟨x, hx1⟩ := exists_ne (1 : E)
      have hxne : (x : adjointGroup Tag.G2 K) ≠ 1 := fun h => hx1 (Subtype.ext h)
      obtain ⟨P, hPc, hPp, hPd⟩ :=
        exists_perfect_le_centralizer_G2_three hp3K h4 (hE.2 x x.2) hxne
      exact ⟨x, x.2, hxne, P, hPc, hPp, hPd⟩
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      by_cases hdvd : p ∣ Nat.card K ^ 2 - 1
      · have hfac : p ∣ (Nat.card K - 1) * (Nat.card K + 1) := by
          rwa [CFSG.RankThree.PartOne.K128.sq_sub_one_eq (Nat.card K)
            (Nat.card_pos (α := K))] at hdvd
        rcases hp.dvd_mul.mp hfac with hsub | hadd
        · exact perfectCentralizerPlanes_of_conj_into_torus hp hp2 hsub
            (fun A hA hAp => exists_conj_into_torus_G2 hp hp5 hsub hA hAp)
        · exact perfectCentralizerPlanes_adjointGroup_G2_of_dvd_add_one hp hp5 hadd
      · have hnd : ¬ p ∣ q.card ^ 2 - 1 := by rwa [← hK]
        exact PerfectCentralizerPlanes.of_rankLE1 hp
          (RankLE1.of_mulEquiv e
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_G2 q hv hp hp5 hpq hnd))
  exact PerfectCentralizerPlanes.of_mulEquiv e.symm hplanes

theorem outPNice_cat_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {p : ℕ} (hp : p.Prime) : OutPNice p (Cat ⟨.G2 q, hv⟩) := by
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (Cat ⟨.G2 q, hv⟩) .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (MulEquiv.refl _)⟩
  haveI : Finite (Cat ⟨.G2 q, hv⟩) :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .G2 q.p q.exponent hm
  exact outPNice_of_isCyclic_outer hp
    (isCyclic_outer_of_untwistedModel_G2 q.prime_p q.exponent_pos hq3 hm.2)

theorem innGoodAt_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    InnGoodAt p (.G2 q) (Cat ⟨.G2 q, hv⟩) := by
  obtain ⟨K, hF, hFin, -, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.G2 K) := Subtype.finite
  haveI : Finite (Cat ⟨.G2 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center (Cat ⟨.G2 q, hv⟩) = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  exact innGoodAt_of_outPNice hp hZ (outPNice_cat_G2 q hv hp)
    (perfectCentralizerPlanes_cat_G2 q hv hp hp2 hpq) (.G2 q)

theorem lieInnGood_G2 : LieInnGood fun d => ∃ q, d = .G2 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_G2 q hv hp hp2 ?_
  rwa [TauCeti.LieTypeIndex.characteristic_G2 q] at hpc

end Catalogue
