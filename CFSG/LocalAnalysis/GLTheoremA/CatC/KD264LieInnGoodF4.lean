module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodF4Cyc
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamF4
public import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4Six

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartOne.KE
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.K133H GL83.I713
  CFSG.RankThree.PartOne.OutStructure

section NegTorus

open CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem exists_conj_into_langTorus_F4_neg (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K + 1) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg ∧
        ∀ A : Subgroup (adjointGroup Tag.F4 K), (∀ x ∈ A, x ^ p = 1) →
          ∃ c : adjointGroup Tag.F4 K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data_F4 K
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.F4 K).subtype with hι
  have hιinj : Function.Injective ι :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K L)).comp
      (Subgroup.subtype_injective _)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨ζu, hord, hζpow⟩ :=
    exists_orderOf_eq_of_dvd_add_one (K := K) (L := L) (N := Nat.card K + 1) dvd_rfl
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    (rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec) f4Neg_smul hFr
    hζpow
  rw [hord] at hH₀card
  set X := H₀.map (MulAut.conj g0).toMonoidHom with hX
  have hXι : X ≤ ι.range := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      ← (G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl) K L Fr hFr).1,
      ← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono (hH₀T.trans (twistedTorus_le_twModel n Fr))
  set S : Subgroup (adjointGroup Tag.F4 K) := X.comap ι with hS
  have hScard : Nat.card S = (Nat.card K + 1) ^ Tag.F4.rank := by
    have hmap : S.map ι = X := by
      rw [hS, Subgroup.map_comap_eq, inf_eq_right.2 hXι]
    rw [← Subgroup.card_map_of_injective hιinj, hmap, hX,
      Subgroup.card_map_of_injective (MulAut.conj g0).injective, hH₀card]
  have hfac : (Nat.card (adjointGroup Tag.F4 K)).factorization p =
      (Nat.card S).factorization p := by
    rw [card_adjointGroup_F4, factorization_ordF4_of_dvd_add_one hp hp5 hq2 hpd, hScard,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, show Tag.F4.rank = 4 from rfl]
  refine ⟨Fr, hFr, g0, hg0C, hg0, fun A hA => ?_⟩
  have hord : (Nat.card (⊤ : Subgroup (adjointGroup Tag.F4 K))).factorization p =
      (Nat.card S).factorization p := by
    rw [Subgroup.card_top]
    exact hfac
  obtain ⟨c, -, hc⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (p := p)
    (H := S) (Y := ⊤) (A := A) le_top le_top hA hord
  have hc' : ∀ x ∈ A, c * x * c⁻¹ ∈ S := fun x hx =>
    hc (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hx)
  refine ⟨c, fun x hx => ?_⟩
  have hmem : ι (c * x * c⁻¹) ∈ X := Subgroup.mem_comap.1 (hc' x hx)
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hmem
  change ι (c * x * c⁻¹) ∈ (twistedTorusOf n (Units.map (entrywiseHom Fr))).map
    (MulAut.conj g0).toMonoidHom
  rw [← hyeq]
  exact Subgroup.mem_map_of_mem _ (hH₀T hy)

end NegTorus

section AddOne


open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem perfectCentralizerPlanes_adjointGroup_F4_of_dvd_add_one (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
  have hK4 : 4 ≤ Nat.card K := by
    have hle : p ≤ Nat.card K + 1 := Nat.le_of_dvd (by norm_num) hpd
    omega
  refine perfectCentralizerPlanes_adjointGroup_neg (Or.inl rfl) (w := f4Neg) f4Neg_smul K hp
    (by omega) hpd hK4 ?_
  intro A hA hAcard
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ := exists_conj_into_langTorus_F4_neg K hp hp5 hpd
  exact ⟨Fr, hFr, g0, hg0C, hg0, hconj A hA⟩

end AddOne

section CatPlanes

open CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows


theorem perfectCentralizerPlanes_cat_F4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    PerfectCentralizerPlanes p (Cat ⟨.F4 q, hv⟩) := by
  classical
  obtain ⟨K, hF, hFin, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hplanes : PerfectCentralizerPlanes p (adjointGroup Tag.F4 K) := by
    rcases eq_or_ne p 3 with rfl | hp3
    ·
      have h3K : ¬ 3 ∣ Nat.card K := hpK
      have hK4 : 4 ≤ Nat.card K := by
        have h2 : 1 < Nat.card K := Finite.one_lt_card
        have hne2 : Nat.card K ≠ 2 := fun h => h32 ⟨rfl, by rw [hK] at h; exact h⟩
        have hne3 : Nat.card K ≠ 3 := fun h => h3K (h.symm ▸ dvd_rfl)
        omega
      exact perfectCentralizerPlanes_adjointGroup_three (Or.inl rfl)
        CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K h3K hK4
    ·
      have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      by_cases hcnt : 2 ≤ degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p))
      · rcases degCount_F4_ge_two hcnt with h1 | h2' | h3' | h4' | h6
        · have hd : p ∣ Nat.card K - 1 :=
            CFSG.HardMathSupport.Timmesfeld.LocalTwo.dvd_sub_one_of_orderOf_eq_one Nat.card_pos h1
          exact perfectCentralizerPlanes_of_conj_into_torus hp hp2 hd
            (fun A hA hAp => exists_conj_into_torus_F4 hp hp5 hd hA hAp)
        · exact perfectCentralizerPlanes_adjointGroup_F4_of_dvd_add_one K hp hp5
            (CFSG.LieType.SeitzGeneration.ExcHigh.dvd_add_one_of_orderOf_eq_two hp h2')
        · exact perfectCentralizerPlanes_adjointGroup_F4_three K hp (by omega)
            (dvd_sq_add_self_add_one_of_orderOf_eq_three hp h3')
        · exact perfectCentralizerPlanes_adjointGroup_F4_four K hp hp5
            (dvd_sq_add_one_of_orderOf_eq_four hp h4')
        · exact perfectCentralizerPlanes_adjointGroup_F4_six K hp (by omega)
            (dvd_sq_sub_self_add_one_of_orderOf_eq_six hp h6)
      ·
        exact PerfectCentralizerPlanes.of_rankLE1 hp (rankLE1_F4 K hp hpK (by omega))
  exact PerfectCentralizerPlanes.of_mulEquiv e.symm hplanes

end CatPlanes

section OutCyclic


theorem outPNice_cat_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) : OutPNice p (Cat ⟨.F4 q, hv⟩) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (Cat ⟨.F4 q, hv⟩) .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (MulEquiv.refl _)⟩
  haveI : Finite (Cat ⟨.F4 q, hv⟩) :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .F4 q.p q.exponent hm
  exact outPNice_of_isCyclic_outer hp
    (isCyclic_outer_of_untwistedModel_F4 q.prime_p q.exponent_pos hm.2)

end OutCyclic

section Catalogue


theorem innGoodAt_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (h32 : ¬ (p = 3 ∧ q.card = 2)) :
    InnGoodAt p (.F4 q) (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, hF, hFin, -, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Finite (Cat ⟨.F4 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center (Cat ⟨.F4 q, hv⟩) = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, center_adjointGroup_eq_bot, Subgroup.map_bot]
  exact innGoodAt_of_outPNice hp hZ (outPNice_cat_F4 q hv hp)
    (perfectCentralizerPlanes_cat_F4 q hv hp hp2 hpq h32) (.F4 q)

theorem lieInnGood_F4 : LieInnGood fun d => ∃ q, d = .F4 q := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  refine innGoodAt_F4 q hv hp hp2 ?_ h3
  rwa [TauCeti.LieTypeIndex.characteristic_F4 q] at hpc

end Catalogue

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
