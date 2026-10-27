module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Model
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S265

set_option linter.unusedSectionVars false

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem not_three_dvd_card_primeCore (J : Subgroup Ω) :
    ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three J
  unfold GLAPPrimeCoreOf at h
  rwa [Subgroup.card_map_of_injective J.subtype_injective] at h

private theorem map_inf_eq_bot_of_center {J D : Subgroup Ω}
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) {E : Subgroup ↥J} (hE : IsPGroup 3 E)
    (hEZ : E.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) ⊓ Subgroup.center (PQuot 3 J) = ⊥) :
    E.map J.subtype ⊓ D = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨j, hjE, rfl⟩, hjD⟩
  have hjc : j ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 (hDJ hjD) y y.2)
  have hzc : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j : PQuot 3 J) ∈
      Subgroup.center (PQuot 3 J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.1 hjc y]
  have hq : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j : PQuot 3 J) ∈
      E.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) ⊓ Subgroup.center (PQuot 3 J) :=
    ⟨⟨j, hjE, rfl⟩, hzc⟩
  rw [hEZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (GLAPPrimeCore 3 ↥J)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_three_dvd_card_primeCore J))
  have hj : j ∈ E ⊓ GLAPPrimeCore 3 ↥J := ⟨hjE, hq⟩
  rw [Subgroup.inf_eq_bot_of_coprime hcop, Subgroup.mem_bot] at hj
  rw [Subgroup.mem_bot, hj, map_one]

theorem pow_mul_card_le_of_torusLift_pQuot {J D : Subgroup Ω} (hJ : commutator (PQuot 3 J) = ⊤)
    {R : Type} [Group R] (θ : PQuot 3 J ⧸ Subgroup.center (PQuot 3 J) ≃* R) {r : ℕ}
    (hT : CFSG.StandardType.GGTorusLift 3 r R) (hD : IsElemAbelian 3 D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) :
    3 ^ r * Nat.card D ≤ 3 ^ GLATwoLocalRank 3 Ω := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : PQuot 3 J →* R :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))) with hψ
  have hψs : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ψ.ker = Subgroup.center (PQuot 3 J) := by
    ext g
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker⟩ := hT (PQuot 3 J) ψ hψs hψk.le hJ
  rw [hψk] at hEker
  have hcore := not_three_dvd_card_primeCore J
  obtain ⟨E', hE'el, hE'map, hE'card⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift (GLAPPrimeCore 3 ↥J) hcore hE
  have hEN' : E'.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) ≤
      Subgroup.normalizer (U : Set (PQuot 3 J)) := by
    rw [hE'map]
    exact hEU
  obtain ⟨U', hU'2, hE'U', hU'map, -, -⟩ := CFSG.LocalAnalysis.GLTheoremA.S267.exists_twoGroup_lift
    Nat.prime_three (by norm_num) (GLAPPrimeCore 3 ↥J) hcore hU2 hE'el.isPGroup hEN'
  have hcomm : ∀ d ∈ D, ∀ j ∈ J, j * d = d * j := fun d hd j hj =>
    Subgroup.mem_centralizer_iff.1 (hDJ hd) j hj
  have hdisj : Disjoint (E'.map J.subtype) D := by
    rw [disjoint_iff]
    exact map_inf_eq_bot_of_center hDJ hE'el.isPGroup (by rw [hE'map]; exact hEker)
  have hDN : D ≤ Subgroup.normalizer ((E'.map J.subtype : Subgroup Ω) : Set Ω) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => by
      obtain ⟨e, -, rfl⟩ := hg
      exact hcomm d hd e e.2)
  have hcard : Nat.card (E'.map J.subtype ⊔ D : Subgroup Ω) = 3 ^ r * Nat.card D := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hDN hdisj,
      Subgroup.card_map_of_injective J.subtype_injective, hE'card, hEcard]
  have hel : IsElemAbelian 3 (E'.map J.subtype ⊔ D) := by
    refine IsElemAbelian.sup_of_commute (hE'el.map J.subtype) hD ?_
    rintro _ ⟨e, -, rfl⟩ d hd
    exact hcomm d hd e e.2
  have hUne : U'.map J.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective]
    intro h0
    apply hU
    rw [← hU'map, h0, Subgroup.map_bot]
  have hle : E'.map J.subtype ⊔ D ≤
      Subgroup.normalizer ((U'.map J.subtype : Subgroup Ω) : Set Ω) := by
    refine sup_le ((Subgroup.map_mono hE'U').trans (Subgroup.le_normalizer_map _)) fun d hd => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => by
      obtain ⟨u, -, rfl⟩ := hg
      exact hcomm d hd u u.2)
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_three hel hUne (hU'2.map _) hle
  rwa [hcard] at h1


theorem three_pow_six_le_card_of_isTE6two {S B T : Subgroup Ω} {x b : Ω} (h : QUNL 3 S B T x b)
    (hJcat : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isTE6two) : 3 ^ 6 ≤ Nat.card B := by
  have cfg := h.cfg
  have hN := h.nlAct
  have hDJ : Dgrp b x ≤ Subgroup.centralizer ((Ipart 3 S b : Subgroup Ω) : Set Ω) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_,
      Set.singleton_subset_iff.2 (Subgroup.mem_centralizer_iff.2 fun y _ => cfg.xcen y)⟩)
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (hN.comp.1 hy).2 b (Set.mem_singleton b)).symm
  obtain ⟨-, hDel, hDcard⟩ := S10.card_Dgrp cfg.elem Nat.prime_three cfg.hb cfg.xB cfg.x1 cfg.hbx
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 (Ipart 3 S b)) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hN.comp
  obtain ⟨K₀, _, _, σ₀, hK₀, hσ₀, ⟨e₀⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_twistedE6RootGroup_of_catalogIs_isTE6two hJcat
  have hK₀' : Nat.card K₀ = (2 ^ 1) ^ 2 := by rw [hK₀]; norm_num
  obtain ⟨ε₀, -, -⟩ := CFSG.StandardType.TwE6FieldCore.exists_recipeConj_field (n := 1) le_rfl hK₀'
    σ₀ (fun c => by rw [hσ₀, pow_one])
  have hT := CFSG.StandardType.ggTorusLift_twE6Add_holds (n := 1) le_rfl hK₀' Nat.prime_three
    (by norm_num)
  have hlr : CFSG.StandardType.TwE6Delta.liftRank 3 = 4 := by
    simp [CFSG.StandardType.TwE6Delta.liftRank]
  rw [hlr] at hT
  have h1 := pow_mul_card_le_of_torusLift_pQuot hq.1 (e₀.trans ε₀) hT hDel hDJ
  rw [hDcard, ← pow_add] at h1
  exact h1.trans cfg.rank

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
