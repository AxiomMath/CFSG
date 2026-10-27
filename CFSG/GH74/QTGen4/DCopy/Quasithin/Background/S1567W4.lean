module

public import CFSG.Quasithin.Background.S1567W4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Skeleton
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1531Stage1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

@[expose] def Input15368PsiL3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
      ↥(StatedSL 3 (ZMod 2))) →
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)

@[expose] def Stage1531InspectBCatNoTwo_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    F6.F618ConclusionCat
      (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
      (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) →
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) ∨
      ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

section Top

theorem stage1531InspectBCatNoTwo_of_inputs_F4 (h113 : StageLemma14113) (h56 : AsB56)
    (hI1 : InspectListF618) (hNP : InspectRemainingNP) (hΨ : Input15368PsiL3_F4) :
    Stage1531InspectBCatNoTwo_F4 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hconc
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, L, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  have hT := isSylowTwoOf_TE_G0_NT c L r66 r67 gl r68
  have hSQ : SQTKGroup ↥(G0_153 T Mc M E s) := sqtkGroup_G0_NT c r68
  have hA : IsGoldschmidtAmalgam
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) := by
    rcases r68.triple.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, -, hcyc⟩
    · exact hA
    · exfalso
      apply hcyc
      have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
        Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
      have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
      rw [hbot]
      infer_instance
  have hD : Open.pCore 2 (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) = ⊥ :=
    hA.pCore_eq_bot
  have hXEJ := XE_le_thompsonJ_NT c L r66 r67 gl r68
  have hXI : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hV0 : IsElemAbelian 2 (V0_153 T Mc M E s) := isElemAbelian_V0_NoTwo c r46 L r66 r67 gl r68
  have hIN : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hVI : V0_153 T Mc M E s ≤ G0_153 T Mc M E s := V0_le_G0_NT r68
  obtain ⟨ρ, hρ, hρα⟩ := exists_faithful_rho h113 k r67 gl r68

  have hJα := thompsonJ_G0_le_ker_alpha c L r66 r67 gl r68
  have hJ : ∀ g : ↥(G0_153 T Mc M E s), (g : G) ∈ thompsonJ (G0_153 T Mc M E s) →
      S1567.alpha153 T Mc M E s r68.le_normalizer g = 1 := by
    intro g hg
    obtain ⟨y, hy, hyg⟩ := hJα hg
    have : y = g := Subtype.ext hyg
    subst this
    exact hy
  have hB53 := b53Hyp_autI_thompsonJ_of_faithful hV0 hIN hVI _ ρ hρ
    (fun g => S1567.alpha153 T Mc M E s r68.le_normalizer g = 1) hρα hJ hD
    (sqtkGroup_of_le hSQ (B6.thompsonJ_le _))
  have hmapN := map_barQ_eq_autI hV0 hIN _ ρ
    (fun g => S1567.alpha153 T Mc M E s r68.le_normalizer g = 1) hρα
    (B6.thompsonJ_le (G0_153 T Mc M E s)) hJ
  have hNne : autI hV0 (thompsonJ (G0_153 T Mc M E s)) ≠ ⊥ := by
    rw [← hmapN]
    intro h
    have h' := (Subgroup.map_eq_bot_iff_of_injective _ hρ).mp h
    exact barQ_XE_ne_bot_NT r67 r68 hXI (le_bot_iff.mp ((barQ_mono hXEJ).trans h'.le))
  have hcases := h56 (IntMod (V0_153 T Mc M E s) hV0) (fun v => IntMod.sq_eq_one v) _ hNne hB53

  have hJI : thompsonJ (TE153 T E) ≤ G0_153 T Mc M E s := (B6.thompsonJ_le _).trans hT.1
  have hJD₁ : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (TE153 T E)) ≤
      barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s) :=
    barQ_mono ((B6.thompsonJ_le _).trans le_sup_right)
  have hJp : IsPGroup 2 ↥(barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (TE153 T E))) :=
    isPGroup_barQ hJI (hT.2.1.to_le (B6.thompsonJ_le _))
  have hD₁N : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (G1_153 T Mc M E s) ≤ Subgroup.normalizer
        (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
          (thompsonJ (TE153 T E)) : Set (↥(G0_153 T Mc M E s) ⧸
            CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) :=
    barQ_le_normalizer (G1_le_normalizer_thompsonJ_TE c L r67 gl)
  have hcomm : ⁅oTwoUpper (barQ (G0_153 T Mc M E s)
        (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)),
      barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (thompsonJ (TE153 T E))⁆ =
      oTwoUpper (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (G2_153 T E)) := by
    have hG2I : G2_153 T E ≤ G0_153 T Mc M E s := le_sup_right
    rw [← barQ_oTwoUpper hG2I, oTwoUpper_G2_153 r67 hT.2.1, ← barQ_commutator hXI hJI]
    congr 1
    rw [← thompsonJ_R_eq r67 L]
    exact r67.XE_comm.symm
  have hN : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (G0_153 T Mc M E s)) =
      Subgroup.normalClosure (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (thompsonJ (TE153 T E)) : Set (↥(G0_153 T Mc M E s) ⧸
          CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
    apply le_antisymm
    · exact barQ_thompsonJ_le_of_normal hT Subgroup.subset_normalClosure
    · have := barQ_thompsonJ_normal (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      exact Subgroup.normalClosure_le_normal (barQ_mono (B6.thompsonJ_le_of_sylow hT))
  have hres := hI1 _ _ _ _ _ hA hconc hJD₁ hJp hD₁N hcomm hN (IntMod (V0_153 T Mc M E s) hV0)
    (fun v => IntMod.sq_eq_one v) ρ hρ (by rw [hmapN]; exact hB53)
    (by rw [hmapN]; exact hcases)
  by_cases hS3 : Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3))
  · exact Or.inl (XE_eq_oTwoUpper_of_S3_NT c L r66 r67 gl r68 hS3)
  · rcases hres with h | ⟨hlist, hO2⟩
    · exact absurd h hS3
    · by_cases hL3 : Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
          ↥(StatedSL 3 (ZMod 2)))
      · exfalso
        obtain ⟨e⟩ := hL3
        have h2 := hΨ G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 ⟨e⟩
        have h5 : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
            (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s) := by
          rw [r68.pCore_eq]
          exact (Subgroup.comap_map_eq_self_of_injective
            (G0_153 T Mc M E s).subtype_injective _).symm
        exact S1567.oTwoUpper_ne_top_of_pCore_le_centralizer h113 k r68.le_normalizer h2 h5
          (oTwoUpper_top_eq_top_of_equiv_L32 e)
      · have hscope : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) ∨
            ¬ IrrShape153 T Mc M E s := by
          by_cases hA : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)
          · exact Or.inl hA
          · exact Or.inr fun hirr => caseB_false_of_irr h113 k r67 gl r68 hO2 hA hirr
        exact Or.inr (hNP G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2
          hL3 hscope)

end Top

section Geometry

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem closing_153CNoTwo_F4 (hF : F6.TheoremF618Cat) (hI : Stage1531InspectBCatNoTwo_F4)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (r50 : Res15350 T M) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) : False := by
  have hne : pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := pCoreOf_G0_ne_bot_NT c r68
  have hq := stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke hne
  have hk := kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian hne
  rcases r68.triple.f6_18Cat hF hq hk with ⟨-, -, -, hconc⟩ | ⟨-, -, -, -, hcyc⟩
  · rcases hI G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl r68 hconc with hA | hB
    · exact false_of_XE_eqB c r46 L r66 r67 gl hA
    · exact false_of_nonsolvable c r45 r49 r67 hB
  · apply hcyc
    have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
      Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
    have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
    rw [hbot]
    infer_instance

end Geometry

theorem stageTheorem1531_of_inputsNoTwo_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618Cat) (i44 : Stage15344_F4) (i46 : Stage15346Four) (i49c : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (i67r : Stage15367Rest)
    (iI : Stage1531InspectBCatNoTwo_F4) : StageTheorem1531_F4 := by
  have i46' : Stage15346 := stage15346_of_four i46
  have i47 : Stage15347 := stage15347
  have i48 : Stage15348 := stage15348 h11 h113
  have i49 : Stage15349 := stage15349_of_core h11 h113 i49c
  have i62 : Stage15362 := stage15362 h11
  have i63 : Stage15363 := stage15363
  have i66 : Stage15366B := stage15366B h11 h113
  have i67 : Stage15367B := stage15367B_of_rest h113 i67r
  intro G _ _ T Mc M hq hMf hO
  have h : Hyp153 G T Mc M := ⟨hq, hMf, hO⟩
  obtain ⟨V₁, V₂, t, D⟩ := h.exists_decomp
  have c : Ctx153 G T Mc M V₁ V₂ t := ⟨h, D⟩
  have r45 := lemma_15_3_45_F4 i44 h113 c
  have r46 := i46' G T Mc M V₁ V₂ t c r45
  have r47 := i47 G T Mc M V₁ V₂ t c r45 r46
  have r48 := i48 G T Mc M V₁ V₂ t c r45 r46 r47
  have r49 := i49 G T Mc M V₁ V₂ t c r45 r46 r47 r48
  have hF91 : ∀ H : Subgroup G, IsHTM153 T M H →
      HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H :=
    fun H hH => hypF91_of_stage15348 i48 c r45 r46 r47 r49 hH
  have r50 := i50 G T Mc M V₁ V₂ t c r45 r46 r47 r49 hF91
  have r62 := i62 G T Mc M V₁ V₂ t c r45 r46 r50
  have r63 := i63 G T Mc M V₁ V₂ t c r45 r46 r50 r62
  have r64 := lemma_15_3_64 c r47 r62
  have r65 := i65 G T Mc M V₁ V₂ t c r45 r46 r50 r49 r62 r63 r64
  have r65two := lemma_15_3_65_two c r46 r63 r65
  obtain ⟨E, L⟩ := exists_lineData153 c r46 r65two
  have r66 := i66 G T Mc M V₁ V₂ E t c r45 r46 r49 L
  have r67 := i67 G T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66
  obtain ⟨s, gl⟩ := exists_goldLine153B h D r66
  have r68 := res15368NoTwo_of_proved h113 c r45 r49 L r66 r67 gl
  exact (closing_153CNoTwo_F4 hF iI c r45 r46 r49 r50 L r66 r67 gl r68).elim

end CFSG.Quasithin
