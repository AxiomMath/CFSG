module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2C
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD91
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147c
public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActor_one fieldActor_mul
  ringEquiv_cube_apply_eq fixSubfield)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4)
open CFSG.LocalAnalysis.GLTheoremA.CatB (barAut barAut_mk barAut_pow_three conjL conjL_apply)


theorem td4g2_mem_centralizer_of_conj {G : Type} [Group G] {g x : G}
    (h : g⁻¹ * x * g⁻¹⁻¹ = x) : x ∈ Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * g = g * (g⁻¹ * x * g⁻¹⁻¹) := by group
    _ = g * x := by rw [h]

theorem td4g2_fixed_of_comm {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) (hx : (x : G) ∈ Subgroup.centralizer ({b} : Set G)) :
    barAut L b hb (QuotientGroup.mk x) = QuotientGroup.mk x := by
  rw [barAut_mk]
  congr 1
  apply Subtype.ext
  rw [conjL_apply]
  have hx' : b * (x : G) = (x : G) * b := Subgroup.mem_centralizer_iff.1 hx b (Set.mem_singleton b)
  calc b⁻¹ * (x : G) * b = b⁻¹ * ((x : G) * b) := by group
    _ = b⁻¹ * (b * (x : G)) := by rw [hx']
    _ = (x : G) := by group

theorem td4g2_lift_fixed {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (y : PQuot 3 L)
    (hy : barAut L b hb y = y) (x₀ : ↥L) (hx₀ : (QuotientGroup.mk x₀ : PQuot 3 L) = y) :
    (conjL L b hb x₀ : G)⁻¹ * (x₀ : G) ∈ GLAPPrimeCoreOf 3 L := by
  rw [← hx₀, barAut_mk] at hy
  exact (td4g2_mk_eq_iff _ _).1 hy

theorem td4G2At_holds (G : Type) [Group G] [Finite G] : TD4G2At G := by
  intro X L b' hL hchev hTD4 hb'N hb'3 hNI hcent a haN ha3 hab
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨q, hv, hq2c, hq3c, ⟨eS⟩⟩ := td4g2_td4_of_catalog hTD4
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  have hm : CFSG.Models.LieModel (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) .trialityD4 0 q.p
      q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  obtain ⟨eQS⟩ : Nonempty (PQuot 3 L ≃* PSimple 3 L) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm⟩
  obtain ⟨eQC⟩ : Nonempty (PQuot 3 L ≃* td4g2C K σ) := ⟨eQS.trans (eS.trans eC)⟩
  have hZ0 : ∀ z : td4g2C K σ, (∀ x, z * x = x * z) → z = 1 := by
    intro z hz
    have hw : eQC.symm z ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply eQC.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hz (eQC y)).symm
    rw [hcenter, Subgroup.mem_bot] at hw
    calc z = eQC (eQC.symm z) := (eQC.apply_symm_apply z).symm
      _ = 1 := by rw [hw, map_one]
  obtain ⟨-, hfac⟩ := td4g2_order hv eS
  rw [hq2] at hfac
  have hcard2 : card2 3 L = 2 ^ (12 * q.exponent) := by
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  have hsq : Nat.sqrt (card2 3 L) = (2 ^ q.exponent) ^ 6 := by
    rw [hcard2, show (2 : ℕ) ^ (12 * q.exponent) = ((2 ^ q.exponent) ^ 6) ^ 2 by ring]
    exact Nat.sqrt_eq' _
  have hβ3 : (MulAut.congr eQC (barAut L b' hb'N)) ^ 3 = 1 := by
    rw [← map_pow, barAut_pow_three L b' hb'N hb'3, map_one]
  have hα3 : (MulAut.congr eQC (barAut L a haN)) ^ 3 = 1 := by
    rw [← map_pow, barAut_pow_three L a haN ha3, map_one]
  have hβout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (MulAut.congr eQC (barAut L b' hb'N)) := by
    rintro ⟨y, hy⟩
    apply hNI
    apply CFSG.LocalAnalysis.GLTheoremA.CatB.inducesInnerMod_of_inner hb'N
    refine ⟨eQC.symm y, MulEquiv.ext fun w => ?_⟩
    apply eQC.injective
    have key := congrArg (fun φ : MulAut (td4g2C K σ) => φ (eQC w)) hy
    simp only [MulAut.conj_apply] at key
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← td4g2_congr_apply]
    exact key
  have hcomm_bar : barAut L a haN * barAut L b' hb'N = barAut L b' hb'N * barAut L a haN := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : a⁻¹ * b'⁻¹ = b'⁻¹ * a⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hab]
    simp only [MulAut.mul_apply, barAut_mk]
    congr 1
    apply Subtype.ext
    simp only [CFSG.LocalAnalysis.GLTheoremA.CatB.conjL_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show a⁻¹ * (b'⁻¹ * (x : G) * b') * a = (a⁻¹ * b'⁻¹) * x * (b' * a) by group,
      show b'⁻¹ * (a⁻¹ * (x : G) * a) * b' = (b'⁻¹ * a⁻¹) * x * (a * b') by group, h1, hab]
  have hcomm : MulAut.congr eQC (barAut L a haN) * MulAut.congr eQC (barAut L b' hb'N) =
      MulAut.congr eQC (barAut L b' hb'N) * MulAut.congr eQC (barAut L a haN) := by
    rw [← map_mul, ← map_mul, hcomm_bar]
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ2 : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  obtain ⟨k, v, hkv⟩ := td4g2_normal_form q.exponent_pos hK2 hσ2 hβ3 hβout hα3
  obtain ⟨hβv, hv3⟩ := td4g2_commute hZ0 hβ3 hkv hcomm hα3
  have hfixEq : ∀ z : PQuot 3 L, barAut L b' hb'N z = lemma102_conjQ 3 hb'N z := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [CFSG.LocalAnalysis.GLTheoremA.CatB.barAut_mk, lemma102_conjQ_mk]
    congr 1
  have hfixSub : CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N) =
      lemma102_fixSub 3 hb'N := by
    ext z
    show barAut L b' hb'N z = z ↔ z ∈ lemma102_fixSub 3 hb'N
    rw [hfixEq z]
    exact Iff.rfl
  have htw : twoPart (Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix
      (MulAut.congr eQC (barAut L b' hb'N)))) = (2 ^ q.exponent) ^ 6 := by
    rw [Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv eQC
      (barAut L b' hb'N)).toEquiv, ← hsq, ← hcent, lemma102_centCard2_eq_fixSub 3 hb'N, hfixSub]
  have hcatβ := td4g2_catalog_of_fix hq2 ⟨hq2c, hq3c⟩ hK hσ hβ3 hβout htw
  have hcatS : catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N))
      (onLie isG2Big) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcatβ
    exact ⟨i, hi, ⟨(CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv eQC (barAut L b' hb'N)).symm.trans e⟩⟩
  obtain ⟨hsimpleS, hnabS, h3S⟩ := (kd91_holds (PSimple 3 L) hTD4).2.2 _ hcatS
  haveI := hsimpleS
  have hnab : ¬ IsMulCommutative ↥(CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N)) := by
    rintro ⟨h⟩
    obtain ⟨x, y, hxy⟩ := hnabS
    exact hxy (h.comm x y)
  have hQS : CFSG.Open.IsQuasisimple ↥(CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N)) :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.isQuasisimple_of_simple_nonabelian hnab
  have hcore := td4g2_core_bot h3S
  have hQS' : CFSG.Open.IsQuasisimple (↥(CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N)) ⧸
      GLAPPrimeCore 3 ↥(CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N))) :=
    hQS.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)
  obtain ⟨vb, hvb⟩ : ∃ w : PQuot 3 L, eQC w = v := ⟨eQC.symm v, eQC.apply_symm_apply v⟩
  have hvbS : barAut L b' hb'N vb = vb := by
    apply eQC.injective
    rw [← td4g2_congr_apply, hvb]
    exact hβv
  have hvb3 : vb ^ 3 = 1 := eQC.injective (by rw [map_pow, hvb, hv3, map_one])
  have hformula : ∀ y : PQuot 3 L, barAut L b' hb'N y = y →
      barAut L a haN y = vb * y * vb⁻¹ := by
    intro y hy
    apply eQC.injective
    have hβy : MulAut.congr eQC (barAut L b' hb'N) (eQC y) = eQC y := by
      rw [td4g2_congr_apply, hy]
    have hαy : MulAut.congr eQC (barAut L a haN) (eQC y) = v * eQC y * v⁻¹ := by
      rw [hkv]
      exact td4g2_fix_apply hβv hβy k
    rw [map_mul, map_mul, map_inv, hvb, ← td4g2_congr_apply]
    exact hαy
  set Sb := CFSG.RankThree.PartTwo.Sec4.autFix (barAut L b' hb'N) with hSb
  have hvbS' : vb ∈ Sb := CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 hvbS
  set z : ↥Sb := ⟨vb, hvbS'⟩ with hz
  have hz3 : z ^ 3 = 1 := Subtype.ext (by simpa [hz] using hvb3)
  set F : Subgroup (PQuot 3 L) := (Subgroup.centralizer ({z} : Set ↥Sb)).map Sb.subtype with hF
  obtain ⟨K', hK'F, hK'ne⟩ : ∃ K' : Subgroup (PQuot 3 L), GLAPComponent 3 F K' ∧ K' ≠ ⊥ := by
    by_cases hz1 : z = 1
    · have hC : Subgroup.centralizer ({z} : Set ↥Sb) = ⊤ := by
        rw [hz1]
        ext x
        simp [Subgroup.mem_centralizer_iff]
      have hF' : F = Sb := by
        rw [hF, hC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      obtain ⟨I, hI, hbar⟩ := exists_glaPComponent_of_isQuasisimple hQS'
      refine ⟨I, by rw [hF']; exact hI, ?_⟩
      intro hI0
      have hbot : barX 3 Sb ⊥ = ⊥ := by simp [barX]
      rw [hI0, hbot] at hbar
      haveI := isQuasisimple_nontrivial hQS'
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥Sb ⧸ GLAPPrimeCore 3 ↥Sb)
      have hxT : x ∈ (⊤ : Subgroup (↥Sb ⧸ GLAPPrimeCore 3 ↥Sb)) := Subgroup.mem_top x
      rw [← hbar, Subgroup.mem_bot] at hxT
      exact hx hxT
    · have hz3' : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      have hker : Nat.Coprime 3
          (Nat.card ↥((Subgroup.centralizer ({z} : Set ↥Sb)) ⊓ Sb.subtype.ker)) := by
        rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.subtype_injective Sb), inf_bot_eq, Subgroup.card_bot]
        exact Nat.coprime_one_right 3
      obtain ⟨K, hK, hKne⟩ := td4g2_comp_ne_bot (kd147_clause_c ↥Sb hcatS z hz3')
      refine ⟨K.map Sb.subtype, glaPComponent_map hp3 Sb.subtype hker hK, ?_⟩
      intro h
      apply hKne
      apply Subgroup.map_injective (f := Sb.subtype) (Subgroup.subtype_injective Sb)
      rw [h, Subgroup.map_bot]
  have hNL : GLAPPrimeCoreOf 3 L ≤ L := by
    intro n hn
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 (show n ∈ (GLAPPrimeCore 3 ↥L).map L.subtype from hn)
    exact m.2
  have hJF : barX 3 L (L ⊓ cx b' ⊓ cx a) = F := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨⟨-, hxb⟩, hxa⟩ := Subgroup.mem_subgroupOf.1 hx
      have hfb : barAut L b' hb'N (QuotientGroup.mk x) = QuotientGroup.mk x :=
        td4g2_fixed_of_comm hb'N x hxb
      have hfa : barAut L a haN (QuotientGroup.mk x) = QuotientGroup.mk x :=
        td4g2_fixed_of_comm haN x hxa
      have hcomm' : vb * QuotientGroup.mk x = QuotientGroup.mk x * vb := by
        have h1 := hformula _ hfb
        rw [hfa] at h1
        calc vb * QuotientGroup.mk x = (vb * QuotientGroup.mk x * vb⁻¹) * vb := by group
          _ = QuotientGroup.mk x * vb := by rw [← h1]
      have hSmem : (QuotientGroup.mk x : PQuot 3 L) ∈ Sb :=
        CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 hfb
      refine Subgroup.mem_map.2 ⟨⟨QuotientGroup.mk x, hSmem⟩, Subgroup.mem_centralizer_iff.2 ?_, rfl⟩
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact Subtype.ext hcomm'
    · intro hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
      have hsc : vb * (s : PQuot 3 L) = (s : PQuot 3 L) * vb :=
        congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hs z (Set.mem_singleton z))
      have hsS : barAut L b' hb'N (s : PQuot 3 L) = s :=
        CFSG.RankThree.PartTwo.Sec4.mem_autFix.1 s.2
      have hsA : barAut L a haN (s : PQuot 3 L) = s := by
        rw [hformula _ hsS, hsc, mul_inv_cancel_right]
      obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective (s : PQuot 3 L)
      have hu1 := td4g2_lift_fixed hb'N _ hsS x₀ hx₀
      have e1 : (x₀ : G)⁻¹ * (b'⁻¹ * (x₀ : G) * b'⁻¹⁻¹) =
          (((conjL L b' hb'N x₀ : ↥L) : G)⁻¹ * (x₀ : G))⁻¹ := by
        rw [conjL_apply]
        group
      have hc1 : (x₀ : G)⁻¹ * (b'⁻¹ * (x₀ : G) * b'⁻¹⁻¹) ∈ GLAPPrimeCoreOf 3 L := by
        rw [e1]
        exact Subgroup.inv_mem _ hu1
      obtain ⟨n, hn, hnfix⟩ := td4g2_fix_lift (GLAPPrimeCoreOf 3 L)
        (not_dvd_card_glaPPrimeCoreOf hp3 L) (g := b'⁻¹) (x := (x₀ : G))
        (by rw [inv_pow, hb'3, inv_one])
        (normalizer_le_normalizer_glaPPrimeCoreOf 3 L (Subgroup.inv_mem _ hb'N))
        (le_normalizer_glaPPrimeCoreOf 3 L x₀.2) hc1
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥L, (x₁ : G) = (x₀ : G) * n :=
        ⟨⟨(x₀ : G) * n, mul_mem x₀.2 (hNL hn)⟩, rfl⟩
      have hmk1 : (QuotientGroup.mk x₁ : PQuot 3 L) = QuotientGroup.mk x₀ := by
        rw [td4g2_mk_eq_iff, hx₁]
        have e : ((x₀ : G) * n)⁻¹ * (x₀ : G) = n⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ hn
      have hcbx1 : (x₁ : G) ∈ Subgroup.centralizer ({b'} : Set G) := by
        apply td4g2_mem_centralizer_of_conj (g := b')
        rw [hx₁]
        exact hnfix
      have hαx1 : barAut L a haN (QuotientGroup.mk x₁) = QuotientGroup.mk x₁ := by
        rw [hmk1, hx₀]
        exact hsA
      rw [barAut_mk] at hαx1
      have hu2 : ((conjL L a haN x₁ : ↥L) : G)⁻¹ * (x₁ : G) ∈ GLAPPrimeCoreOf 3 L :=
        (td4g2_mk_eq_iff _ _).1 hαx1
      have hgab : a⁻¹ * b' = b' * a⁻¹ := by
        calc a⁻¹ * b' = a⁻¹ * (b' * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * b') * a⁻¹ := by rw [hab]
          _ = b' * a⁻¹ := by group
      have haC : a ∈ Subgroup.centralizer ({b'} : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hab.symm
      have hT'card : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({b'} : Set G)) :=
        fun h => not_dvd_card_glaPPrimeCoreOf hp3 L (h.trans (Subgroup.card_dvd_of_le inf_le_left))
      have hgT' : a⁻¹ ∈ Subgroup.normalizer
          ((GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({b'} : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf (normalizer_le_normalizer_glaPPrimeCoreOf 3 L (Subgroup.inv_mem _ haN))
          (td4g2_normalizer_centralizer hgab)
      have hx1b : (x₁ : G) * b' = b' * (x₁ : G) :=
        (Subgroup.mem_centralizer_iff.1 hcbx1 b' (Set.mem_singleton b')).symm
      have hxT' : (x₁ : G) ∈ Subgroup.normalizer
          ((GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({b'} : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf (le_normalizer_glaPPrimeCoreOf 3 L x₁.2)
          (td4g2_normalizer_centralizer hx1b)
      have hc2 : (x₁ : G)⁻¹ * (a⁻¹ * (x₁ : G) * a⁻¹⁻¹) ∈
          GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({b'} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have e2 : (x₁ : G)⁻¹ * (a⁻¹ * (x₁ : G) * a⁻¹⁻¹) =
              (((conjL L a haN x₁ : ↥L) : G)⁻¹ * (x₁ : G))⁻¹ := by
            rw [conjL_apply]
            group
          rw [e2]
          exact Subgroup.inv_mem _ hu2
        · exact mul_mem (inv_mem hcbx1) (mul_mem (mul_mem (inv_mem haC) hcbx1)
            (inv_mem (inv_mem haC)))
      obtain ⟨n', hn', hfix2⟩ := td4g2_fix_lift
        (GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({b'} : Set G)) hT'card (g := a⁻¹)
        (x := (x₁ : G)) (by rw [inv_pow, ha3, inv_one]) hgT' hxT' hc2
      obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥L, (x₂ : G) = (x₁ : G) * n' :=
        ⟨⟨(x₁ : G) * n', mul_mem x₁.2 (hNL (Subgroup.mem_inf.1 hn').1)⟩, rfl⟩
      have hx2b : (x₂ : G) ∈ Subgroup.centralizer ({b'} : Set G) := by
        rw [hx₂]
        exact mul_mem hcbx1 (Subgroup.mem_inf.1 hn').2
      have hx2a : (x₂ : G) ∈ Subgroup.centralizer ({a} : Set G) := by
        apply td4g2_mem_centralizer_of_conj (g := a)
        rw [hx₂]
        exact hfix2
      have hmk2 : (QuotientGroup.mk x₂ : PQuot 3 L) = QuotientGroup.mk x₁ := by
        rw [td4g2_mk_eq_iff]
        have e3 : (x₂ : G)⁻¹ * (x₁ : G) = n'⁻¹ := by
          rw [hx₂]
          group
        rw [e3]
        exact Subgroup.inv_mem _ (Subgroup.mem_inf.1 hn').1
      refine Subgroup.mem_map.2 ⟨x₂, Subgroup.mem_subgroupOf.2 ⟨⟨x₂.2, hx2b⟩, hx2a⟩, ?_⟩
      show (QuotientGroup.mk x₂ : PQuot 3 L) = _
      rw [hmk2, hmk1, hx₀]
      rfl
  have hX0L : L ⊓ cx b' ⊓ cx a ≤ L := inf_le_left.trans inf_le_left
  rw [← hJF] at hK'F
  obtain ⟨J, hJ, hJbar, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_lift hX0L hK'F
  intro hbot
  have hle : J ≤ GLAPLayer 3 (L ⊓ cx b' ⊓ cx a) := le_sSup hJ
  rw [hbot, le_bot_iff] at hle
  apply hK'ne
  rw [← hJbar, hle]
  simp [barX]

end CFSG.LocalAnalysis.GLTheoremA

end
