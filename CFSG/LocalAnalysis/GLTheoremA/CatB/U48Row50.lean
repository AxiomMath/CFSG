module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Syl
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48LayerY
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U48
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 equivSU4)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)

section Sylow

variable {G : Type} [Group G] [Finite G] {L P : Subgroup G}

theorem sylow_image (hPL : P ≤ L) (hP : IsPGroup 3 P)
    (hmax : ∀ Q : Subgroup G, P ≤ Q → Q ≤ L → IsPGroup 3 Q → Q = P)
    {M : Type} [Group M] [Finite M] (φ : ↥L →* M) (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) :
    ∃ S : Sylow 3 M, (S : Subgroup M) = (P.subgroupOf L).map φ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set PL : Subgroup ↥L := P.subgroupOf L with hPLdef
  have hPLp : IsPGroup 3 PL := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hmaxL : ∀ Q : Subgroup ↥L, IsPGroup 3 Q → PL ≤ Q → Q = PL := by
    intro Q hQ hle
    have hQG : IsPGroup 3 (Q.map L.subtype) := hQ.map L.subtype
    have h1 : P ≤ Q.map L.subtype := fun x hx =>
      ⟨⟨x, hPL hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have h3 := hmax _ h1 (Subgroup.map_subtype_le Q) hQG
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ Q.map L.subtype := ⟨x, hx, rfl⟩
      rw [h3] at this
      exact Subgroup.mem_subgroupOf.2 this
    · exact hle
  let SL : Sylow 3 ↥L :=
    { toSubgroup := PL
      isPGroup' := hPLp
      is_maximal' := fun {Q} hQ hle => hmaxL Q hQ hle }
  have hcardPL : Nat.card PL = 3 ^ (Nat.card ↥L).factorization 3 := SL.card_eq_multiplicity
  have hcardL : Nat.card ↥L = Nat.card M * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  have hfact : (Nat.card ↥L).factorization 3 = (Nat.card M).factorization 3 := by
    rw [hcardL, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, add_zero]
  have hinj : Function.Injective (φ.domRestrict PL) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : ↥L) ∈ φ.ker := hx
    obtain ⟨n, hn⟩ := hPLp x
    have h1 : orderOf (x : ↥L) ∣ 3 ^ n := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf (x : ↥L) ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨(x : ↥L), hx1⟩ : φ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ n) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hker)
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact Subtype.ext (orderOf_eq_one_iff.1 h3)
  have hcard : Nat.card (PL.map φ) = 3 ^ (Nat.card M).factorization 3 := by
    rw [← hfact, ← hcardPL, ← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

variable {X : Subgroup G}

section Griess


theorem center_pquot_eq_bot_of_u48 (hL : GLAPComponent 3 X L)
    (hcat : catalogIs (PSimple 3 L) S9.isU4eight) : Subgroup.center (PQuot 3 L) = ⊥ := by
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  obtain ⟨q, hv, hq8, ⟨e⟩⟩ := lieIndex_isU4eight hcat
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hQ hm
    (a := 1) (b := 1) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
  have hz : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := Nat.dvd_one.mp (by simpa using hdvd)
  exact Subgroup.card_eq_one.mp hz

end Griess

@[expose] noncomputable def pqModelP (hZ : Subgroup.center (PQuot 3 L) = ⊥)
    (hcat : catalogIs (PSimple 3 L) S9.isU4eight) : PQuot 3 L ≃* SU4 :=
  (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (bridge_u4eight hcat).some).trans equivSU4

theorem not_three_dvd_card_ker_piOf {M : Type*} [Group M] (e : PQuot 3 L ≃* M) :
    ¬ 3 ∣ Nat.card (piOf L e).ker := by
  rw [piOf_ker]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L))

theorem exists_conj_of_central (φ : ↥L →* SU4) (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) {y : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyc : IsCentralIn 3 y L) :
    ∃ (g : SU4) (t : μ3), (t : Kˣ) ≠ 1 ∧ g * φ ⟨y, hyc.1⟩ * g⁻¹ = yStd t := by
  obtain ⟨hyL, P, hPL, hP3, hyP, hPc, hPmax⟩ := hyc
  obtain ⟨S, hS⟩ := sylow_image hPL hP3 hPmax φ hφ hker
  have hy' : φ ⟨y, hyL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hne : φ ⟨y, hyL⟩ ≠ 1 := by
    intro h
    have hmem : (⟨y, hyL⟩ : ↥L) ∈ φ.ker := h
    have h1 : orderOf (⟨y, hyL⟩ : ↥L) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hy3)
    have h2 : orderOf (⟨y, hyL⟩ : ↥L) ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨⟨y, hyL⟩, hmem⟩ : φ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime 3 (Nat.card φ.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hker
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact hy1 (congrArg Subtype.val (orderOf_eq_one_iff.1 h3))
  refine exists_conj_yStd hy' hne S ?_ ?_
  · rw [hS]
    exact ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 hyP, rfl⟩
  · rw [hS]
    rintro _ ⟨x, hx, rfl⟩
    have hxc : (x : G) * y = y * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPc (Subgroup.mem_subgroupOf.1 hx))
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hxc)

end Sylow

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3)

section Row


theorem u48Cent3At_holds (G : Type) [Group G] [Finite G] : U48Cent3At G := by
  intro X L y hL hcat hy3 hy1 hyc
  have hZ := center_pquot_eq_bot_of_u48 hL hcat
  let e := pqModelP hZ hcat
  have hφs : Function.Surjective (piOf L e) := piOf_surjective L e
  obtain ⟨g, t, ht, hgt⟩ := exists_conj_of_central (piOf L e) hφs (not_three_dvd_card_ker_piOf e)
    hy3 hy1 hyc
  let φ' : ↥L →* SU4 := (MulAut.conj g).toMonoidHom.comp (piOf L e)
  have hφ's : Function.Surjective φ' := (MulAut.conj g).surjective.comp hφs
  have hker' : ¬ 3 ∣ Nat.card φ'.ker := by
    have : φ'.ker = (piOf L e).ker :=
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
    rw [this]
    exact not_three_dvd_card_ker_piOf e
  have hφ'y : φ' ⟨y, hyc.1⟩ = yStd t := hgt
  obtain ⟨J, hJ, hJl, -, ⟨ε⟩⟩ := layerY φ' hφ's hker' ht hyc.1 hy3 hφ'y
  subst hJl
  exact ⟨hJ, catalogIs_psimple_of_pquot ε⟩

end Row

end CFSG.LocalAnalysis.GLTheoremA
