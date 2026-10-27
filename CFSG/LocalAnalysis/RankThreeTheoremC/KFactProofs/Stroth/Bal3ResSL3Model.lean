module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Covers
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier Subgroup
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)

section Scalars

variable {F : Type} [Field F] [Finite F]

theorem card_scalars_dvd_three' {p f : ℕ} {H : Subgroup (GL (Fin 3) F)}
    (hH : (Nat.card F = p ^ f ∧ H = StatedSL 3 F) ∨
      (Nat.card F = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) F)) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf H) ∣ 3 :=
  SectionRank.OddCover.card_scalars_dvd (by norm_num) H fun x c hc => by
    have hdet := SectionRank.OddCover.det_eq_one_of_linUni hH x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])

end Scalars

theorem isPerfect_statedSL_three (F : Type) [Field F] : Group.IsPerfect (StatedSL 3 F) := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
    (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 F).toMonoidHom)
    (specialLinearGroupEquivStatedSL 3 F).surjective

theorem exists_mulEquiv_statedSL_of_cover (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) (hc : Nat.card (center K) = 3) {r f : ℕ}
    (hcl : StatedClassicalModel (K ⧸ center K) .PSL 3 r f) (hd : 3 ∣ r ^ f - 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ^ f ∧
      Nonempty (K ≃* StatedSL 3 F) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hcl
  have hga : (genericOrders .PSL 3 r f).1 = Nat.gcd 3 (r ^ f - 1) := rfl
  have ha : 3 ∣ (genericOrders .PSL 3 r f).1 := by rw [hga]; exact Nat.dvd_gcd dvd_rfl hd
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSL 3 F)) .PSL 3 r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
  have hdv : (genericOrders .PSL 3 r f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :=
    dvd_card_scalars (q := r ^ f) (by norm_num) hq0
      (Or.inl ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL 3 F)))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2 hdv 3
  have hHperf := isPerfect_statedSL_three F
  set D := (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) with hD
  have hDc : D ≤ Subgroup.center (StatedSL 3 F) := scalars_le_center _
  let α : StatedSL 3 F →* StatedProj (StatedSL 3 F) := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  let β : K →* StatedProj (StatedSL 3 F) := CFSG.GH74.Generic.centralQuotientMap e'
  have hβ : Function.Surjective β := CFSG.GH74.Generic.centralQuotientMap_surjective e'
  have hβk : β.ker = Subgroup.center K := CFSG.GH74.Generic.centralQuotientMap_ker e'
  have hZp : IsPGroup 3 (Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  obtain ⟨φ, hφs, -⟩ := exists_hom_of_cover hHperf hperf α hα (hαk ▸ hDc) β hβ hβk.le hp
    (by rw [hβk]; exact hZp) (by rw [hαk]; exact hM)
  have hbij := (CFSG.QuasithinUnique.Ch1.bijective_of_scalar_cover e' hc
    (card_scalars_dvd_three' (p := r) (f := f) (Or.inl ⟨hF, rfl⟩)) hφs).2
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩

theorem exists_mulEquiv_statedSU_of_cover (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) (hc : Nat.card (center K) = 3) {r f : ℕ}
    (hcl : StatedClassicalModel (K ⧸ center K) .PSU 3 r f) (hd : 3 ∣ r ^ f + 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (r ^ f) ^ 2 ∧
      Nonempty (K ≃* StatedSU 3 (r ^ f) F) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm := hcl.1
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hcl
  have hga : (genericOrders .PSU 3 r f).1 = Nat.gcd 3 (r ^ f + 1) := rfl
  have ha : 3 ∣ (genericOrders .PSU 3 r f).1 := by rw [hga]; exact Nat.dvd_gcd dvd_rfl hd
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU 3 (r ^ f) F)) .PSU 3 r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
  have hdv : (genericOrders .PSU 3 r f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (r ^ f) F)) :=
    dvd_card_scalars (q := r ^ f) (by norm_num) hq0
      (Or.inr ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU 3 (r ^ f) F)))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf
        (StatedSU 3 (r ^ f) F))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2 hdv 3
  haveI : Fact r.Prime := ⟨hr⟩
  have hHperf : Group.IsPerfect (StatedSU 3 (r ^ f) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (by norm_num) hadm.2.2.2
  set D := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (r ^ f) F) with hD
  have hDc : D ≤ Subgroup.center (StatedSU 3 (r ^ f) F) := scalars_le_center _
  let α : StatedSU 3 (r ^ f) F →* StatedProj (StatedSU 3 (r ^ f) F) := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  let β : K →* StatedProj (StatedSU 3 (r ^ f) F) := CFSG.GH74.Generic.centralQuotientMap e'
  have hβ : Function.Surjective β := CFSG.GH74.Generic.centralQuotientMap_surjective e'
  have hβk : β.ker = Subgroup.center K := CFSG.GH74.Generic.centralQuotientMap_ker e'
  have hZp : IsPGroup 3 (Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  obtain ⟨φ, hφs, -⟩ := exists_hom_of_cover hHperf hperf α hα (hαk ▸ hDc) β hβ hβk.le hp
    (by rw [hβk]; exact hZp) (by rw [hαk]; exact hM)
  have hbij := (CFSG.QuasithinUnique.Ch1.bijective_of_scalar_cover e' hc
    (card_scalars_dvd_three' (p := r) (f := f) (Or.inr ⟨hF, rfl⟩)) hφs).2
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩

theorem isSLThreePi_of_cover (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hc : Nat.card (center K) = 3)
    (hd : ∃ d : TauCeti.ValidLieTypeIndex, Bal3IsLinThreeCover d ∧
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    CFSG.RankThree.PartTwo.Sec4.IsSLThreePi K := by
  have hperf : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨⟨d, hv⟩, hdc, ⟨e⟩⟩ := hd
  rcases hdc with ⟨q, hq', h3⟩ | ⟨q, hq', h3⟩
  ·
    have hq'' : d = .A 2 q := hq'
    subst hq''
    have hm : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group .PSL 3 q.p
        q.exponent := lieModel_typeA 2 q hv
    have hmK := models_lieModel_of_mulEquiv e.symm hm
    have hcl : StatedClassicalModel (K ⧸ center K) .PSL 3 q.p q.exponent := by
      rcases hmK.2 with h | ⟨h0, -⟩
      · exact h
      · exact absurd h0 (by norm_num)
    have h3' : 3 ∣ q.p ^ q.exponent - 1 := by simpa only [TauCeti.PrimePower.card_def] using h3
    obtain ⟨F, _, _, hF, ⟨iso⟩⟩ := exists_mulEquiv_statedSL_of_cover hGA hperf hc hcl h3'
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    exact ⟨q.p ^ q.exponent, F, inferInstance, inferInstance, Or.inl ⟨hF, by omega, ⟨iso⟩⟩⟩
  ·
    have hq'' : d = .twistedA 2 q := hq'
    subst hq''
    have hcl : StatedClassicalModel (K ⧸ center K) .PSU 3 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have h3' : 3 ∣ q.p ^ q.exponent + 1 := by simpa only [TauCeti.PrimePower.card_def] using h3
    obtain ⟨F, _, _, hF, ⟨iso⟩⟩ := exists_mulEquiv_statedSU_of_cover hGA hperf hc hcl h3'
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    exact ⟨q.p ^ q.exponent, F, inferInstance, inferInstance, Or.inr ⟨hF, by omega, ⟨iso⟩⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
