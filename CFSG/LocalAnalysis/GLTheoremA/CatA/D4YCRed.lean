module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Count
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TI117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TNoTri

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T
  CFSG.Blueprint.Multiplier

theorem exists_D4_of_isD4any_not_two {i : TauCeti.CFSGIndex} (hi : isD4any i)
    (hn : ¬ S9.isD4two i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧ 2 ≤ q.exponent ∧
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
      · have hp : q.p = 2 := hi
        refine ⟨q, hv, hp, ?_, rfl⟩
        by_contra hlt
        have he : q.exponent = 1 := by
          have := q.exponent_pos
          omega
        apply hn
        show q.card = 2
        rw [TauCeti.PrimePower.card_def, hp, he]
        norm_num
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem center_pQuot_eq_bot_of_d4big (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type}
    [Group G] [Finite G] {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple (PQuot 3 J))
    (hD4 : catalogIs (PSimple 3 J) isD4any) (hn : ¬ catalogIs (PSimple 3 J) S9.isD4two) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hD4
  have hi2 : ¬ S9.isD4two i := fun h => hn ⟨i, h, ⟨f⟩⟩
  obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
  have hm := CFSG.Models.lieModel_D 4 q hv f
  have hg : genericOrders .POmegaPlus 4 q.p q.exponent = (1, 1) := by
    have hev : Even (q.p ^ q.exponent) := by
      rw [hp2, Nat.even_pow]
      exact ⟨even_two, by omega⟩
    simp [genericOrders, hev]
  have he : exceptionalOrders .POmegaPlus 4 q.p q.exponent = (1, 1) := by
    unfold exceptionalOrders
    rw [hp2]
    split <;> simp_all
  have hdvd := card_center_dvd_of_table hGA hq hm hg he (by norm_num)
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (by simpa using hdvd))

section Red

set_option linter.unusedSectionVars false



open scoped commutatorElement

open CFSG.LocalAnalysis.GLTheoremA.S9 CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.FP

variable {G : Type} [Group G] [Finite G]

theorem noTrialityBigAt_of_core (hcore : D4BigCoreAt) (h112 : D4BigNormalizes G)
    (hGA : CFSG.Open.GriessAllModelsStatement) : NoTrialityBigAt G := by
  classical
  intro B x L hS hKG hchev hD4 hnD4 b hb
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hBcard : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hS.1.2.1
  have hxB : x ∈ B := hS.2.1.1
  have hBC : B ≤ C := isElemAbelian_le_centralizer hBel hxB
  have hcomp : GLAPComponent 3 C L := hS.2.2
  have hLC : L ≤ C := hcomp.1
  have hLsn : CFSG.Open.IsSubnormal L C := hcomp.2.1
  have hBrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (le_refl B) hBel hS.1.2.1
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    h112 C B L hKG hBel hBC
      ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp3 C).trans hBrank)
      hcomp hD4 hnD4
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hcomp
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := center_pQuot_eq_bot_of_d4big hGA hq hD4 hnD4
  set Kb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C L with hKb
  set Bb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C B with hBb
  let e : PQuot 3 L ≃* ↥Kb := quotEquivBarX hp3 hLC hLsn
  let e0 : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcatK : catalogIs ↥Kb isD4any := (catalogIs_congr (e0.trans e)).1 hD4
  have hnotK : ¬ catalogIs ↥Kb S9.isD4two := fun h => hnD4 ((catalogIs_congr (e0.trans e)).2 h)
  haveI : Finite ↥Kb := inferInstance
  have hKc : ∀ k ∈ Kb, (∀ y ∈ Kb, y * k = k * y) → k = 1 := by
    intro k hk hcomm
    obtain ⟨q, hq⟩ := e.surjective ⟨k, hk⟩
    have hqc : q ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q'
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      rw [hq]
      exact hcomm _ (e q').2
    rw [hZ, Subgroup.mem_bot] at hqc
    subst hqc
    have := congrArg Subtype.val hq
    simpa using this.symm
  have hBO : B ⊓ GLAPPrimeCoreOf 3 C = ⊥ := by
    have hOcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) :=
      (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 C)
    have hcopB : Nat.Coprime (Nat.card B) (Nat.card (GLAPPrimeCoreOf 3 C)) := by
      rw [hBcard]
      exact Nat.Coprime.pow_left _ hOcop
    have h1 := Nat.eq_one_of_dvd_coprimes hcopB (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  have hBbel : IsElemAbelian 3 Bb := l94t_isElemAbelian_barX hBel hBC
  have hBbcard : Nat.card Bb = Nat.card B := l94t_card_barX hBC hBO
  have hBbK : Bb ≤ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    l94t_barX_le_normalizer (p := 3) hLC hBL
  have hcase : D4RankCase Kb Bb := by
    by_cases hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 C))
    · right
      refine ⟨fun P W hP hW2 hWne hPW => ?_, ?_⟩
      · have := l94_card_le_of_quot (C := C) hP hW2 hWne hPW
        rw [hBbcard, hBcard]
        exact this
      · obtain ⟨-, -, T₀, hT₀C, hT₀2, hBT₀, hne, -⟩ := hS.2.1
        obtain ⟨hTT₀, hT'2, hT'B, -⟩ := l94t_commutator_facts hBel hT₀2 hBT₀
        have hT'X : ⁅T₀, B⁆ ≤ C := hTT₀.trans hT₀C
        have hTN : ⁅T₀, B⁆ ≤ Subgroup.normalizer (L : Set G) := by
          refine Subgroup.commutator_le.2 fun t ht b' hb' => ?_
          have htC : t ∈ C := hT₀C ht
          have hconj : GLAPComponent 3 C (GLBConj t L) :=
            CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_gLBConj_of_mem hcomp htC
          have hconjcat : catalogIs (PSimple 3 (GLBConj t L)) isD4any :=
            CFSG.LocalAnalysis.GLTheoremA.S8.L84.catalogIs_pSimple_conj t hD4
          have hconjnot : ¬ catalogIs (PSimple 3 (GLBConj t L)) S9.isD4two := by
            intro h
            apply hnD4
            have := CFSG.LocalAnalysis.GLTheoremA.S8.L84.catalogIs_pSimple_conj t⁻¹ h
            rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
          have hBn : B ≤ Subgroup.normalizer ((GLBConj t L : Subgroup G) : Set G) :=
            h112 C B (GLBConj t L) hKG hBel hBC
              ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp3 C).trans
                hBrank) hconj hconjcat hconjnot
          have h1 : t * b' * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro z
            have h2 := Subgroup.mem_normalizer_iff.1 (hBn hb') (t⁻¹ * z * t)
            rw [mem_gLBConj, mem_gLBConj] at h2
            have e1 : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
            have e2 : t * (b' * (t⁻¹ * z * t) * b'⁻¹) * t⁻¹ =
                t * b' * t⁻¹ * z * (t * b' * t⁻¹)⁻¹ := by group
            rw [e1, e2] at h2
            exact h2
          have e3 : ⁅t, b'⁆ = t * b' * t⁻¹ * b'⁻¹ := by
            rw [commutatorElement_def]
          rw [e3]
          exact Subgroup.mul_mem _ h1 (inv_mem (hBL hb'))
        exact ⟨barX 3 C ⁅T₀, B⁆, l94t_isPGroup_barX hT'X hT'2,
          l94t_barX_ne_bot hT'X hT'2 hne hodd, l94t_barX_le_normalizer (p := 3) hT'X hT'B,
          l94t_barX_le_normalizer (p := 3) hLC hTN⟩
    · left
      have heven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
        even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
      intro P hP
      have := card_le_of_quot_even (G := G) (C := C) heven hP
      rw [hBbcard, hBcard]
      exact this
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
  have hbC : b ∈ C := hBC hb
  set π : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hbBb : π ⟨b, hbC⟩ ∈ Bb := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have hbNK : (π ⟨b, hbC⟩)⁻¹ ∈ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    Subgroup.inv_mem _ (hBbK hbBb)
  let e1 : PSimple 3 L ≃* ↥Kb := e0.trans e
  have hcong : MulAut.congr e1 (indAut 3 L b hbN) = conjAut Kb (π ⟨b, hbC⟩)⁻¹ hbNK := by
    ext k
    obtain ⟨s, rfl⟩ := e1.surjective k
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl' : (b⁻¹ * (l : G) * b) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbN) (l : G)).1 l.2
      simpa using this
    have hrel : indRel 3 L b (QuotientGroup.mk l) (QuotientGroup.mk ⟨b⁻¹ * (l : G) * b, hl'⟩) :=
      ⟨l, ⟨b⁻¹ * (l : G) * b, hl'⟩, rfl, rfl, rfl⟩
    change (((e1 (indAut 3 L b hbN (e1.symm (e1 (QuotientGroup.mk (QuotientGroup.mk l)))))) : ↥Kb) :
        ↥C ⧸ GLAPPrimeCore 3 ↥C) = _
    rw [MulEquiv.symm_apply_apply, indAut_apply_mk hbN hrel]
    change π ⟨b⁻¹ * (l : G) * b, hLC hl'⟩ =
      (π ⟨b, hbC⟩)⁻¹ * π ⟨(l : G), hLC l.2⟩ * ((π ⟨b, hbC⟩)⁻¹)⁻¹
    have : (⟨b⁻¹ * (l : G) * b, hLC hl'⟩ : ↥C) = ⟨b, hbC⟩⁻¹ * ⟨(l : G), hLC l.2⟩ * ⟨b, hbC⟩ :=
      Subtype.ext (by simp)
    rw [this, map_mul, map_mul, map_inv, inv_inv]
  have hcentral : ∀ γ : MulAut (PSimple 3 L),
      γ * indAut 3 L b hbN * γ⁻¹ * (indAut 3 L b hbN)⁻¹ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 L) := by
    intro γ
    by_contra hγ
    refine hcore (↥C ⧸ GLAPPrimeCore 3 ↥C) Kb Bb hcatK hnotK hKc hBbel hBbK
      ⟨(π ⟨b, hbC⟩)⁻¹, Subgroup.inv_mem _ hbBb, hbNK, MulAut.congr e1 γ, fun hmem => hγ ?_⟩ hcase
    rw [← hcong] at hmem
    have h1 : MulAut.congr e1 (γ * indAut 3 L b hbN * γ⁻¹ * (indAut 3 L b hbN)⁻¹) ∈ innerAut ↥Kb := by
      simpa only [map_mul, map_inv] using hmem
    have h2 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e1
    have h3 : MulAut.congr e1 (γ * indAut 3 L b hbN * γ⁻¹ * (indAut 3 L b hbN)⁻¹) ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 L)).map
          (MulAut.congr e1).toMonoidHom := by
      rw [h2]
      exact h1
    obtain ⟨y, hy, hyx⟩ := h3
    have : y = γ * indAut 3 L b hbN * γ⁻¹ * (indAut 3 L b hbN)⁻¹ := (MulAut.congr e1).injective hyx
    exact this ▸ hy
  obtain ⟨i, hi, ⟨f⟩⟩ := hD4
  have hi2 : ¬ S9.isD4two i := fun h => hnD4 ⟨i, h, ⟨f⟩⟩
  obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv f
  rw [hp2] at hmodel
  have h0 := Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 (t := .POmegaPlus) (n := 4)
    (f := q.exponent) (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩)
  have h1 := canon_marking_and_labelAll_simple (P' := RawInnBody 3)
    (fun lab hlab => canonRawInn' hp3 (by norm_num) hlab) h0
  refine Canonical.largeEvenMarking_mono ?_ h1
  rintro lab R _ I F θ ⟨-, hmul, hinv, hinn, -⟩ φ hφ
  have hφe := (induces_indRel_iff hbN θ).1 hφ
  intro γ
  set α := indAut 3 L b hbN with hα
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

end Red

end CFSG.LocalAnalysis.GLTheoremA.D4Y
