module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympA6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_isComponent_of_le_layer)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem nonempty_equiv_alt6_of_isA6 {Q : Type} [Group Q] (h : catalogIs Q S8.isA6) :
    Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have hn6 : n = 6 := hi
      subst hn6
      exact ⟨e⟩
    | _ => exact hi.elim
  · cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · have hq : q.card = 9 := hi
          have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
          exact (hdup (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩)).elim
        · exact hi.elim
      | _ => exact hi.elim
    | _ => exact hi.elim

theorem hasLabel_b2der {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)]
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    HasLabel X (· = ⟨.B2der, 0, 1⟩) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₆⟩ := CFSG.StandardType.nonempty_b2der_equiv_alternatingGroup hK
  have hnab := CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  let θ := e.trans e₆.symm
  refine ⟨hX, ⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, CFSG.StandardType.nonabelian_of_mulEquiv θ hnab, θ, rfl⟩

theorem isQuasisimple_of_mulEquiv_target {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : CFSG.Open.IsQuasisimple K) : CFSG.Open.IsQuasisimple H := by
  obtain ⟨hc, hs⟩ := h
  haveI : Group.IsPerfect K := ⟨hc⟩
  refine ⟨(Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective).commutator_eq_top, ?_⟩
  exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr (Subgroup.center H) (Subgroup.center K) e
    (Subgroup.map_center_eq e))).mpr hs

theorem commutator_eq_top_of_commutator_self {G : Type*} [Group G] {J : Subgroup G}
    (hJ : ⁅J, J⁆ = J) : commutator J = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Symp


theorem false_of_symp_a6 {S : Type} [Group S] [Finite S] {labK : GLALabel}
    (hcen : Subgroup.center S = ⊥) (hFam : FamSymp labK) (hlab : HasLabel S (· = labK))
    (hn1 : (canonLabel labK).n ≠ 1)
    (h32 : ¬((canonLabel labK).n = 3 ∧ (canonLabel labK).rank = 2)) {τ : MulAut S}
    (hτ : τ ^ 3 = 1) {A : Subgroup S} (hA : GLAPComponent 3 (fixSubgroup τ) A)
    (hT : S8.IsTypeWithCenter 3 A S8.isA6 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e6⟩ := nonempty_equiv_alt6_of_isA6 hT.1
  haveI : Nontrivial (PSimple 3 A) := e6.toEquiv.nontrivial
  have hlabA : CFSG.Open.IsQuasisimple ↥A → HasLabel ↥A (· = ⟨.B2der, 0, 1⟩) := by
    intro hq
    obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hq inferInstance
    haveI : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hq.2
    exact hasLabel_b2der hq.1 (φ.trans e6)
  have hcanon : canonLabel (⟨.B2der, 0, 1⟩ : GLALabel) = ⟨.B, 2, 1⟩ := rfl
  rcases ClsSymp_holds S 3 τ labK hFam Nat.prime_three (by norm_num) hcen hlab hτ with hin | hfk
  ·
    have hq : CFSG.Open.IsQuasisimple ↥A := by
      rcases Y10GInnSympMark.innDiagKind_symp_data hcen hFam hin with h1 |
        ⟨K, hK, hKf, m, hm, hcard, e, B, hαB⟩
      · exact (hn1 h1).elim
      have hn : 1 ≤ (canonLabel labK).n := by
        rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
        · exfalso
          rw [h0, pow_zero] at hcard
          have : 1 < Nat.card K := Finite.one_lt_card
          omega
        · exact h0
      have h2 : (2 : K) = 0 := by
        haveI := Fintype.ofFinite K
        obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
        have hc := hcard
        rw [Nat.card_eq_fintype_card, hqcard] at hc
        have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
          rw [← hc]
          exact dvd_pow_self q (PNat.ne_zero k)
        have hq2 : q = 2 :=
          (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
        subst hq2
        exact_mod_cast CharP.cast_eq_zero K 2
      obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 B
      have hMEq : MulAut.congr e τ = MulAut.conj (proj m K x) := by
        rw [← hx]
        ext r
        have h1 := hαB (e.symm r)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1
      have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have hz' : e.symm z ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff] at hz ⊢
          intro g
          apply e.injective
          simp only [map_mul, MulEquiv.apply_symm_apply]
          exact hz (e g)
        rw [hcen, Subgroup.mem_bot] at hz'
        rw [Subgroup.mem_bot]
        simpa using congrArg e hz'
      have hpow : MulAut.conj (proj m K x) ^ 3 = 1 := by
        rw [← hMEq, ← map_pow, hτ, map_one]
      have hxp : x ^ 3 = 1 := Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
      have hJ' : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj m K x)))
          (A.map e.toMonoidHom) := by
        rw [← hMEq]
        exact glaPComponent_transport e τ hA
      obtain ⟨hPIL, -⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
          (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
          Nat.prime_three (by norm_num) Nat.prime_two hn hcard (by omega) (by norm_num)
          (fun h => h.elim) x hxp
      have hJle := hPIL _ hJ'.1 (glaPComponent_perfect hJ')
      have hJc := (glaPComponent_isComponent_of_le_layer hJ' hJle).1
      exact isQuasisimple_of_mulEquiv_target
        (A.equivMapOfInjective e.toMonoidHom e.injective) hJc.2.2
    have hdvd := innDiagSymp_holds S 3 τ A labK ⟨.B2der, 0, 1⟩ hFam Nat.prime_three
      (by norm_num) hcen hin hτ (hlabA hq) hA
    rw [hcanon] at hdvd
    exact hn1 (Nat.dvd_one.1 hdvd)
  ·
    obtain ⟨K, hK, hKf, m, hm, hn1', hcardK, hTag, hRank, e, u, hαu, huE, huD⟩ :=
      Y10GFldSympMark.fieldKind_symp_data hcen hFam hfk
    have hMEq : MulAut.congr e τ = u := by
      ext r
      have h1 := hαu (e.symm r)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    have hpow : u ^ 3 = 1 := by
      rw [← hMEq, ← map_pow, hτ, map_one]
    have hu1 : u ≠ 1 := fun h1 => huD (h1 ▸ (spLinearAutGroup m K).one_mem)
    have hord : orderOf u = 3 := orderOf_eq_prime hpow hu1
    obtain ⟨hpn, σ, hσ, hσcard, h, -, hu⟩ :=
      (CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
        Nat.prime_two hn1' hm hcardK).2.2.2.2.2.2.2.2.2 3 Nat.prime_three u huE huD hord
    let e' : S ≃* StatedProj (StatedSp m K) := e.trans (h⁻¹ : MulAut _)
    have hcongr : MulAut.congr e' τ = fieldAut m K σ := by
      have h1 : MulAut.congr e' τ = h⁻¹ * u * h := by
        ext r
        change h⁻¹ (e (τ (e.symm (h r)))) = h⁻¹ (u (h r))
        rw [hαu, MulEquiv.apply_symm_apply]
      rw [h1, hu]
      group
    have hJ' : GLAPComponent 3 (fixSubgroup (fieldAut m K σ)) (A.map e'.toMonoidHom) := by
      rw [← hcongr]
      exact glaPComponent_transport e' τ hA
    have hσp : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
    have hk : Nat.card (descentField σ) = 2 ^ ((canonLabel labK).n / 3) := hσcard
    by_cases h22 : m = 2 ∧ Nat.card (descentField σ) = 2
    ·
      obtain ⟨hm2, hk2⟩ := h22
      apply h32
      have hnp : (canonLabel labK).n / 3 = 1 := by
        have h2 : 2 ^ ((canonLabel labK).n / 3) = 2 ^ 1 := by rw [← hk, hk2, pow_one]
        exact Nat.pow_right_injective le_rfl h2
      refine ⟨?_, hRank.trans hm2⟩
      have := Nat.mul_div_cancel' hpn
      omega
    · obtain ⟨φ⟩ :=
        Y10GFldSympComp.nonempty_quotCenter_equiv_of_glaPComponent_fieldAut hm (by decide) hσp
          h22 hJ'
      haveI : IsSimpleGroup (StatedProj (StatedSp m (descentField σ))) :=
        (CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := descentField σ) hm
          h22).1
      have hqJ : CFSG.Open.IsQuasisimple ↥(A.map e'.toMonoidHom) :=
        ⟨commutator_eq_top_of_commutator_self (glaPComponent_perfect hJ'), φ.isSimpleGroup⟩
      have hq : CFSG.Open.IsQuasisimple ↥A :=
        isQuasisimple_of_mulEquiv_target (A.equivMapOfInjective e'.toMonoidHom e'.injective) hqJ
      obtain ⟨hn3, -, hrk⟩ := fldSymp_holds S 3 τ A labK ⟨.B2der, 0, 1⟩ hFam Nat.prime_three
        (by norm_num) hcen hfk hτ (hlabA hq) hA
      rw [hcanon] at hn3 hrk
      exact h32 ⟨hn3, hrk⟩

end Symp

section Table


theorem i1431InspSp68_holds : I1431InspSp68 := by
  intro Y _ _ hY hO hcat τ hτ A hA hT
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · exact hi.elim
  · exact hi.elim
  · cases d with
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · have hq8 : q.card = 8 := hi
        obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
          (s := 3) (by norm_num) (hq8.trans (by norm_num))
        rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
        · rw [h1, h2] at hm
          have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm (a := 1)
            (b := 1) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
          have hZ : Subgroup.center Y = ⊥ :=
            Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hdvd.trans (by norm_num)))
          obtain ⟨-, hsc | ⟨h0, -⟩⟩ := hm
          · have hlab := hasLabel_of_statedClassicalModel_PSp
              ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Y).1 hY)
              hsc
            exact false_of_symp_a6 hZ (Or.inl rfl) hlab (by decide) (by decide) hτ hA hT
          · exact absurd h0 (by norm_num)
        · rw [h1, h2] at hm
          exact absurd hm.admissible.2.2.2 (by norm_num)
      · exact hi.elim
    | _ => exact hi.elim
  · exact hi.elim

theorem i1431InspSp492_holds : I1431InspSp492 := by
  intro Y _ _ hY hO hcat τ hτ A hA hT
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · exact hi.elim
  · exact hi.elim
  · cases d with
    | B n q =>
      rcases n with _ | _ | _ | n
      · exact hi.elim
      · exact hi.elim
      · have hq : q.card = 2 ^ 9 := hi
        obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
          (s := 9) (by norm_num) hq
        rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm
        · rw [h1, h2] at hm
          have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm (a := 1)
            (b := 1) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
          have hZ : Subgroup.center Y = ⊥ :=
            Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hdvd.trans (by norm_num)))
          obtain ⟨-, hsc | ⟨h0, -⟩⟩ := hm
          · have hlab := hasLabel_of_statedClassicalModel_PSp
              ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Y).1 hY)
              hsc
            exact false_of_symp_a6 hZ (Or.inl rfl) hlab (by decide) (by decide) hτ hA hT
          · exact absurd h0 (by norm_num)
        · rw [h1, h2] at hm
          exact absurd hm.admissible.2.2.2 (by norm_num)
      · exact hi.elim
    | _ => exact hi.elim
  · exact hi.elim

end Table

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
