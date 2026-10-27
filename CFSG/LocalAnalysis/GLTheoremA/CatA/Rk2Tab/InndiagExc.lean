module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner
public import CFSG.RankThree.PartTwo.Sec21.CurtisTitsBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I161a
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.StandardType
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


private theorem isPGroup_le_inn_of_isPGroup_outer_two {R : Type} [Group R] [Finite R]
    (h2 : IsPGroup 2 (Outer R)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut R)} (hEp : IsPGroup p E) :
    E ≤ (MulAut.conj : R →* MulAut R).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : MulAut R →* Outer R := QuotientGroup.mk' _
  have hmap : IsPGroup p (E.map π) := hEp.map π
  have hdisj : Disjoint (E.map π) (⊤ : Subgroup (Outer R)) :=
    IsPGroup.disjoint_of_ne p 2 hp2 (E.map π) ⊤ hmap (h2.of_equiv Subgroup.topEquiv.symm)
  have hbot : E.map π = ⊥ := by
    rw [disjoint_top] at hdisj
    exact hdisj
  intro x hx
  have hxker : π x = 1 := by
    have : π x ∈ E.map π := ⟨x, hx, rfl⟩
    rw [hbot] at this
    simpa using this
  exact (QuotientGroup.eq_one_iff x).mp hxker

private theorem isPGroup_le_inn_of_pow_three_mem {R : Type} [Group R]
    {I N : Subgroup (MulAut R)} [N.Normal] (hNI : N ≤ I)
    (h3 : ∀ x ∈ I, x ^ 3 ∈ N) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {E : Subgroup (MulAut R)} (hE : E ≤ I) (hEp : IsPGroup p E) : E ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (I ⧸ N.subgroupOf I) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H d =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact h3 d d.2
  let π : I →* I ⧸ N.subgroupOf I := QuotientGroup.mk' _
  have hEsub : IsPGroup p (E.subgroupOf I) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  have hmap : IsPGroup p (Subgroup.map π (E.subgroupOf I)) := hEsub.map π
  have hdisj : Disjoint (Subgroup.map π (E.subgroupOf I)) (⊤ : Subgroup (I ⧸ N.subgroupOf I)) :=
    IsPGroup.disjoint_of_ne p 3 hp3 _ _ hmap (hP3.of_equiv Subgroup.topEquiv.symm)
  have hbot : Subgroup.map π (E.subgroupOf I) = ⊥ := by
    rw [disjoint_top] at hdisj
    exact hdisj
  intro e he
  have hy : (⟨e, hE he⟩ : I) ∈ E.subgroupOf I := by
    rw [Subgroup.mem_subgroupOf]
    exact he
  have hmem : π ⟨e, hE he⟩ ∈ Subgroup.map π (E.subgroupOf I) :=
    Subgroup.mem_map.mpr ⟨(⟨⟨e, hE he⟩, hy⟩ : ↥(E.subgroupOf I)), hy, rfl⟩
  rw [hbot] at hmem
  rw [Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff _).mp hmem)

private theorem chevIDImage_E6_odd_subset
    {n : ℕ} (hodd : Odd n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false) ⊆
      LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, hK]
    exact coprime_two_pow_sub_one_three hodd
  exact chevIDImage_subset_inn_of_top (τ := .E6)
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE6_adj fun s =>
      ⟨(powCoprime hcop).symm s, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩)

theorem rk2_inndiagExc_E6
    {lab : GLALabel} (hlab : GLAInLambda2 lab) (ht : lab.tag = .E6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
  let H := LargeEvenChevH (LargeEvenCartanE 6) K false
  let R := LargeEvenCenterQuot H
  let Isub : Subgroup (MulAut R) :=
    Subgroup.closure (LargeEvenInnSet R ∪ LargeEvenChevDiagImage (LargeEvenCartanE 6) K H)
  let Igrp : Subgroup (MulAut R) :=
    Subgroup.closure ((Isub : Set (MulAut R)) ∪ LargeEvenInnSet R)
  have hIgrp_le : Igrp ≤ Isub := by
    change Subgroup.closure ((Isub : Set (MulAut R)) ∪ LargeEvenInnSet R) ≤ Isub
    rw [Subgroup.closure_le]
    exact Set.union_subset (fun _ hx => hx) (fun _ hx => Subgroup.subset_closure (Or.inl hx))
  have hNI : LargeEvenInnSet R ≤ Igrp := fun x hx => Subgroup.subset_closure (Or.inr hx)
  refine ⟨K, hF, hFin, hK, hQK, ?_⟩
  change ∀ E : Subgroup (MulAut R), E ≤ Igrp → IsPGroup p E →
    E ≤ (MulAut.conj : R →* MulAut R).range
  intro E hE hEp
  by_cases hp3 : p = 3
  · have hpd3 : ¬ 3 ∣ rk2DiagIndex ⟨.E6, l, n⟩ := by simpa [hp3] using hpd
    have h3not : ¬ 3 ∣ 2 ^ n - 1 := by
      intro h3
      apply hpd3
      change 3 ∣ Nat.gcd 3 (2 ^ n - 1)
      exact Nat.dvd_gcd dvd_rfl h3
    have hodd : Odd n := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact h3not (CFSG.RankThree.PartTwo.Sec21.three_dvd_two_pow_sub_one_of_even hev)
    have hI : Igrp ≤ LargeEvenInnSet R := fun x hx =>
      chevIDImage_E6_odd_subset hodd hK (hIgrp_le hx)
    exact hE.trans hI
  · exact isPGroup_le_inn_of_pow_three_mem hNI
      (fun x hx => TableBExc.pow_three_mem_inn_of_mem_recipeID_E6 (hIgrp_le hx)) hp hp3 hE hEp


section TwE6Certs



theorem rk2_inndiagExc_twE6
    {lab : GLALabel} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twE6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
  let H := LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n
  let R := LargeEvenCenterQuot H
  let Isub : Subgroup (MulAut R) :=
    Subgroup.closure (LargeEvenInnSet R ∪ LargeEvenChevDiagImage (LargeEvenCartanE 6) K H)
  let Igrp : Subgroup (MulAut R) :=
    Subgroup.closure ((Isub : Set (MulAut R)) ∪ LargeEvenInnSet R)
  have hIgrp_le : Igrp ≤ Isub := by
    change Subgroup.closure ((Isub : Set (MulAut R)) ∪ LargeEvenInnSet R) ≤ Isub
    rw [Subgroup.closure_le]
    exact Set.union_subset (fun _ hx => hx) (fun _ hx => Subgroup.subset_closure (Or.inl hx))
  have hNI : LargeEvenInnSet R ≤ Igrp := fun x hx => Subgroup.subset_closure (Or.inr hx)
  refine ⟨K, hF, hFin, hK, hQK, ?_⟩
  change ∀ E : Subgroup (MulAut R), E ≤ Igrp → IsPGroup p E →
    E ≤ (MulAut.conj : R →* MulAut R).range
  intro E hE hEp
  by_cases hp3 : p = 3
  · have hpd3 : ¬ 3 ∣ rk2DiagIndex ⟨.twE6, l, n⟩ := by simpa [hp3] using hpd
    have h3not : ¬ 3 ∣ 2 ^ n + 1 := by
      intro h3
      apply hpd3
      change 3 ∣ Nat.gcd 3 (2 ^ n + 1)
      exact Nat.dvd_gcd dvd_rfl h3
    have hev : n % 2 = 0 := by
      by_contra h
      exact h3not (CFSG.LocalAnalysis.GLTheoremA.I161a.three_dvd_two_pow_add_one_of_odd (by omega))
    have hI : Igrp ≤ LargeEvenInnSet R := fun x hx =>
      I161a.chevIDImage_twE6_even_subset hlab.1 hev hK (hIgrp_le hx)
    exact hE.trans hI
  · exact isPGroup_le_inn_of_pow_three_mem hNI
      (fun x hx => TwE6Delta.pow_three_mem_inn hlab.1 hK (hIgrp_le hx)) hp hp3 hE hEp


theorem rk2_inndiagExc_B2der {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (ht : lab.tag = .B2der) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
  let R := LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
  haveI : Finite R := by
    obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
    exact Finite.of_injective (fun x : R => e x) e.injective
  refine ⟨K, hF, hFin, hK, hQK, ?_⟩
  intro E _ hEp
  have hout : IsPGroup 2 (Outer R) := by
    obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
    exact LargeExtraspecial.DW.isPGroup_outer_alt6 e
  exact isPGroup_le_inn_of_isPGroup_outer_two hout hp hp2 hEp

theorem rk2_inndiagExc_G2der
    {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (ht : lab.tag = .G2der) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
  let H := LargeEvenChevH (LargeEvenCartanG2) K true
  let R := LargeEvenCenterQuot H
  haveI : Finite R := by
    obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
    exact Finite.of_injective (fun x : R => e x) e.injective
  refine ⟨K, hF, hFin, hK, hQK, ?_⟩
  intro E _ hEp
  have hR : ∃ x y : R, x * y ≠ y * x := by
    obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
    refine ⟨e.symm ⟨TableBExcSmallRest.su3X, TableBExcSmallRest.su3X_mem⟩,
      e.symm ⟨TableBExcSmallRest.su3Y, TableBExcSmallRest.su3Y_mem⟩, ?_⟩
    intro h
    apply TableBExcSmallRest.su3X_mul_su3Y_ne
    simpa using congrArg e h
  have hout : IsPGroup 2 (Outer R) := LargeExtraspecial.DW.isPGroup_outer_psu
    (lieModel_g2der K hK hR)
  exact isPGroup_le_inn_of_isPGroup_outer_two hout hp hp2 hEp

theorem rk2_inndiagExc_twF4der {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (ht : lab.tag = .twF4der) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨-, hn1⟩ := hlab.2
  subst hn1
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  have h0 : (1 - 1) / 2 = 0 := by norm_num
  rw [h0] at hQ
  dsimp only [LargeEvenRecipeTwF4Inherited] at hQ
  obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
  have hK2 : Nat.card K = 2 := by
    rw [hK]
    norm_num
  let R := LargeEvenCenterQuot (LargeEvenTwF4H 0 K)
  haveI : Finite R := by
    have hm : CFSG.Blueprint.ReeTitsModel R .Tits 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK2⟩
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
    exact Finite.of_equiv _ e.symm.toEquiv
  refine ⟨K, hF, hFin, hK, hQK, ?_⟩
  intro E _ hEp
  exact isPGroup_le_inn_of_isPGroup_outer_two
    (RawAutSmall.isPGroup_outer_twF4der rfl hK2) hp hp2 hEp

theorem rk2_inndiagExc {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  rcases htag with ht | ht | ht | ht | ht
  · exact rk2_inndiagExc_E6 hlab ht hp hp2 hpd
  · exact rk2_inndiagExc_twE6 hlab ht hp hp2 hpd
  · exact rk2_inndiagExc_B2der hlab ht hp hp2 hpd
  · exact rk2_inndiagExc_G2der hlab ht hp hp2 hpd
  · exact rk2_inndiagExc_twF4der hlab ht hp hp2 hpd

end TwE6Certs

end CFSG.LocalAnalysis.GLTheoremA
