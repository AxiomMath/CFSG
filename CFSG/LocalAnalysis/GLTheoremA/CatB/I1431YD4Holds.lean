module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinZ
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Holds
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1210

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB
  CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4 CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5
  CFSG.HardMathSupport.Solomon.LocalBalance

set_option linter.unusedSectionVars false


theorem i1431YD4Two_holds : I1431YD4Two := by
  intro Q _ _ σ A I T hQ hZ hcat hσ3 hAσ hA6 hIs hIt hT0 hT2 hTσ hAN
  have hcat9 : catalogIs (Q ⧸ Subgroup.center Q) S9.isD4two := hcat
  obtain ⟨eS⟩ := bridge_d4two hcat9
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hcardOm : Nat.card ↥CFSG.AGLEmbedding.Om8 = 3 ^ 5 * 716800 := by
    rw [← Nat.card_congr eS.toEquiv]
    exact CFSG.LocalAnalysis.GLTheoremA.card_o8p2 hcat9
  haveI : IsSimpleGroup ↥CFSG.AGLEmbedding.Om8 := CatB.U42Cat.isSimple_om8
  let π : Q →* ↥CFSG.AGLEmbedding.Om8 :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hπs : Function.Surjective π := eS.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : ∀ x, π x = 1 → x ∈ Subgroup.center Q := by
    intro x hx
    have h1 : eS (QuotientGroup.mk x) = 1 := hx
    have h2 : (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) = 1 :=
      (map_eq_one_iff eS eS.injective).1 h1
    exact (QuotientGroup.eq_one_iff x).1 h2
  let ū : MulAut (Q ⧸ Subgroup.center Q) := u4AutQuot Q σ
  have hū3 : ū ^ 3 = 1 := by
    have h : u4AutQuotHom Q (σ ^ 3) = 1 := by rw [hσ3, map_one]
    rw [map_pow] at h
    exact h
  let u' : MulAut ↥CFSG.AGLEmbedding.Om8 := MulAut.congr eS ū
  have hu3 : u' ^ 3 = 1 := by rw [← map_pow, hū3, map_one]
  have hu' : ∀ x : Q, u' (π x) = π (σ x) := by
    intro x
    show eS (ū (eS.symm (eS (QuotientGroup.mk x)))) = eS (QuotientGroup.mk (σ x))
    rw [MulEquiv.symm_apply_apply]
    show eS (u4AutQuot Q σ (QuotientGroup.mk x)) = _
    rw [u4AutQuot_mk]
  have hTinj : ∀ t ∈ T, π t = 1 → t = 1 := by
    intro t htT ht1
    have hcen := hπk t ht1
    obtain ⟨j, hj⟩ := hT2 ⟨t, htT⟩
    obtain ⟨k, hk⟩ := pow_three_of_mem_center hZ hcen
    exact eq_one_of_pow_two_three (by simpa using congrArg Subtype.val hj) hk
  have hT0' : T.map π ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨t, htT⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
    have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
    have : π t ∈ T.map π := Subgroup.mem_map_of_mem π htT
    rw [hbot, Subgroup.mem_bot] at this
    exact ht1 (hTinj t htT this)
  have hT2' : IsPGroup 2 ↥(T.map π) := hT2.map π
  obtain ⟨A₀, S₆, hS₆g, f, hA₀A, hSc, hf⟩ := hA6
  obtain ⟨hSsimp, hS360⟩ := isA6_isSimpleGroup hSc
  haveI : IsSimpleGroup S₆ := hSsimp
  have hS₆nc : ¬ ∀ a b : S₆, a * b = b * a :=
    U4Sp8.not_comm_of_simple_of_card (by rw [hS360]; norm_num)
  obtain ⟨φh, hφh, -⟩ := descend_simple hS₆nc π hπk f hf
  have hA6H : I2016.HasA6Quot (π.comp A₀.subtype).range :=
    ⟨(π.comp A₀.subtype).range, S₆, hS₆g, φh, le_rfl, hSc, hφh⟩
  have hHN : (π.comp A₀.subtype).range ≤ Subgroup.normalizer ((T.map π : Subgroup _) : Set _) := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.le_normalizer_map π ⟨(a : Q), hAN (hA₀A a.2), rfl⟩
  have hIcat : catalogIs (PSimple 3 I) S9.isU4two := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hIt.1
    exact ⟨i, isU4two_of_isPSp43 hi, ⟨e⟩⟩
  haveI hT4s : IsSimpleGroup (PSimple 3 I) :=
    CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two hIcat
  have hT4c : Nat.card (PSimple 3 I) = 25920 := card_of_catalogIs_u4two hIcat
  have hT4nc := not_comm_of_card_25920 hT4c
  let Ψ : ↥I →* PSimple 3 I :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 I))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I))
  have hΨ : Function.Surjective Ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨φI, hφI, -⟩ := descend_simple hT4nc π hπk Ψ hΨ
  have hIfix : ∀ x ∈ I, σ x = x := fun x hx => hIs.le hx
  have hq : HasU4Quot (u4Fix u') := by
    refine HasU4Quot.of_surj (A := (π.comp I.subtype).range) ?_ hT4c φI hφI
    rintro _ ⟨x, rfl⟩
    show u' (π x) = π x
    rw [hu', hIfix x x.2]
  have hcatOm : catalogIs ↥CFSG.AGLEmbedding.Om8 S9.isD4two := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat9
    exact ⟨i, hi, ⟨eS.symm.trans e⟩⟩
  by_cases hinner : ∃ g : ↥CFSG.AGLEmbedding.Om8, MulAut.conj g = u'
  swap
  · exact u4InnOuter_d4two hcatOm hu3 (fun a ha => hinner ⟨a, ha⟩) hq
  obtain ⟨g, hg⟩ := hinner
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg]; exact hu3
    have hc : g ^ 3 ∈ Subgroup.center ↥CFSG.AGLEmbedding.Om8 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := DFunLike.congr_fun h1 y
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * g ^ 3 = (g ^ 3 * y * (g ^ 3)⁻¹) * g ^ 3 := by rw [h2]
        _ = g ^ 3 * y := by group
    rw [CFSG.LocalAnalysis.GLTheoremA.HSubT.center_aglOm8_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  have hgπ : ∀ x : Q, g * π x * g⁻¹ = π (σ x) := by
    intro x
    have h2 := DFunLike.congr_fun hg (π x)
    rw [MulAut.conj_apply] at h2
    rw [h2, hu']
  by_cases hg1 : g = 1
  ·
    subst hg1
    have hσ1 : σ = 1 := by
      refine mulAut_eq_one_of_central hQ.1 σ fun x => hπk _ ?_
      have h := hgπ x
      simp only [one_mul, inv_one, mul_one] at h
      rw [map_mul, map_inv, ← h, inv_mul_cancel]
    have hfix : I2016.fixSub σ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      show σ x = x
      rw [hσ1]
      rfl
    rw [hfix] at hIs
    have hIs' : CFSG.Open.IsSubnormal (I.map π) ⊤ := by
      have h := CFSG.Open.IsSubnormal.map π hIs
      rwa [Subgroup.map_top_of_surjective π hπs] at h
    haveI : Finite (PSimple 3 I) := Nat.finite_of_card_ne_zero (by rw [hT4c]; norm_num)
    rcases CFSG.Open.IsSubnormal.eq_bot_or_top hIs' with hbot | htop
    · apply hT4nc
      intro s t
      obtain ⟨a, rfl⟩ := hΨ s
      obtain ⟨b, rfl⟩ := hΨ t
      have haI : π (a : Q) = 1 := by
        have : π (a : Q) ∈ I.map π := Subgroup.mem_map_of_mem π a.2
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have ha : (a : Q) ∈ Subgroup.center Q := hπk _ haI
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.1 ha b).symm
    · have hrt : (π.comp I.subtype).range = ⊤ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
        exact htop
      haveI : IsSimpleGroup ↥(π.comp I.subtype).range := by
        rw [hrt]
        exact Subgroup.topEquiv.isSimpleGroup
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φI.ker with hk | hk
      · have hinj : Function.Injective φI := (MonoidHom.ker_eq_bot_iff φI).1 hk
        have hc1 : Nat.card ↥(π.comp I.subtype).range = Nat.card (PSimple 3 I) :=
          Nat.card_congr (Equiv.ofBijective φI ⟨hinj, hφI⟩)
        have hc2 : Nat.card ↥(π.comp I.subtype).range = Nat.card ↥CFSG.AGLEmbedding.Om8 := by
          rw [hrt]
          exact Subgroup.card_top
        rw [hT4c, hcardOm] at *
        omega
      · have hsub : Subsingleton (PSimple 3 I) := by
          refine ⟨fun s t => ?_⟩
          obtain ⟨x, rfl⟩ := hφI s
          obtain ⟨y, rfl⟩ := hφI t
          have h1 : φI x = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)
          have h2 : φI y = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top y)
          rw [h1, h2]
        have := Finite.card_le_one_iff_subsingleton.2 hsub
        omega
  · refine noT_inner_om8 hcardOm hg3 hg1 (H := (π.comp A₀.subtype).range) (T := T.map π) ?_ hA6H
      hT0' hT2' ?_ hHN
    · rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hgπ (a : Q)
      rw [hAσ (hA₀A a.2)] at h1
      show π (a : Q) * g = g * π (a : Q)
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    · rintro _ ⟨s, hs, rfl⟩
      have hsσ : s ∈ T.map σ.toMonoidHom := by rw [hTσ]; exact hs
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hsσ
      refine ⟨x, hx, ?_⟩
      have h1 := hgπ x
      show π x = g⁻¹ * π (σ x) * g
      rw [← h1]
      group

end CFSG.LocalAnalysis.GLTheoremA.I1431Y

end
