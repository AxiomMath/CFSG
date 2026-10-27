module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourU3
import CFSG.RankThree.PartOne.K159.RowFourType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem i167COrth_numerics {p a k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : a ∣ k) (hpk : p ∣ 2 ^ k + 1)
    (hhs : p ∣ 2 ^ a - 1 ∨ p ∣ 2 ^ a + 1) : p ∣ 2 ^ a + 1 := by
  rcases hhs with h | h
  · exfalso
    obtain ⟨c, rfl⟩ := hdiv
    have h1 : p ∣ 2 ^ (a * c) - 1 := h.trans (by simpa [pow_mul] using Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 c)
    have h3 : p ∣ (2 ^ (a * c) + 1) - (2 ^ (a * c) - 1) := Nat.dvd_sub hpk h1
    have h4 : (2 ^ (a * c) + 1) - (2 ^ (a * c) - 1) = 2 := by
      have := Nat.one_le_two_pow (n := a * c)
      omega
    rw [h4] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  · exact h

private theorem i167COrth_hm4_aux1 {G : Type} [Group G] (hq : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hs
  haveI := hs
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := G ⧸ Subgroup.center G)).2 inferInstance
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact hab (hcomm a b)

private theorem i167COrth_hm4_aux2 (hFnot : ¬ 4 ≤ Nat.card F) : Nat.card F = 2 := by
  obtain ⟨f, hf, hcard⟩ := CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_natCard_eq_two_pow F
  have hf1 : f = 1 := by
    by_contra hne
    have h2 : 2 ≤ f := by omega
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    exact absurd (by rw [hcard]; exact h4) hFnot
  rw [hcard, hf1]; norm_num

theorem i167COrth_hm4 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {g : ↥(orthDerived Q)} (hg : orderOf g = p) {h : F[X]}
    (hh : h ∈ primaryFactors (g : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (g : V ≃ₗ[F] V) h)) :
    4 ≤ primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h ∨
      ((primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h = 2 ∨
        primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h = 3) ∧ 4 ≤ Nat.card F) := by
  by_contra hcon
  rw [not_or] at hcon
  have hmle : primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h ≤ 3 := by omega
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ g hg
  have hm2 : 2 ≤ primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h :=
    CFSG.StandardType.SevOmSmall.two_le_primaryMultiplicity hx hh hq
  have hm23 : primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h = 2 ∨
      primaryMultiplicity (g : V ≃ₗ[F] V).toLinearMap h = 3 := by omega
  have hF2 : Nat.card F = 2 := i167COrth_hm4_aux2 (fun h4 => hcon.2 ⟨hm23, h4⟩)
  have hns := i167COrth_hm4_aux1 hq
  rcases hm23 with hm | hm
  · obtain ⟨E, hEfield, hEfin, hEcard, ⟨e⟩⟩ :=
      CFSG.StandardType.SevOmSmall.exists_specialBlock_equiv_SL2 hx hp hp2 hpq hh hne hm
    letI instE : Field E := hEfield
    letI instFin : Finite E := hEfin
    have hE2 : Nat.card E = 2 := by rw [hEcard, hF2]
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) :=
      CFSG.StandardType.SevOmSmall.isSolvable_SL_two hE2
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · have hself : h = reciprocalPolynomial h :=
      (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne).symm
    have hdeg2 : h.natDegree = 2 :=
      CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hne
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    haveI : Group.IsSolvable ↥(specialBlock Q (g : V ≃ₗ[F] V) h) :=
      hx.isSolvable_specialBlock_three_two (hp.odd_of_ne_two hp2) hh hne hself hdeg2 hm hF2
    exact hns inferInstance

private theorem i167COrth_catalogIs_minus_six_aux1 {f p : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ f) ^ 2) (hpq : p ∣ 2 ^ f + 1) :
    p ∣ Nat.card ↥(StatedSU 4 (2 ^ f) E) := by
  obtain ⟨p0, f0, hU, hq0⟩ := CFSG.GH74.Generic.S1.rcard_exists_unitaryFieldData hE
  have hcard := CFSG.GH74.Generic.S1.rcard_card_statedSU hU (n := 4) (by norm_num)
  have hpZ : (p : ℤ) ∣ (((p0 ^ f0 : ℕ) : ℤ) + 1) := by
    have := hpq
    rw [hq0] at this
    exact_mod_cast this
  have hfac : (p : ℤ) ∣ ((((p0 ^ f0 : ℕ) : ℤ) ^ 2) - (-1 : ℤ) ^ 2) := by
    obtain ⟨k, hk⟩ := hpZ
    refine ⟨k * ((((p0 ^ f0 : ℕ) : ℤ) - 1)), ?_⟩
    have h : ((((p0 ^ f0 : ℕ) : ℤ) ^ 2) - (-1 : ℤ) ^ 2) =
        ((((p0 ^ f0 : ℕ) : ℤ) + 1) * ((((p0 ^ f0 : ℕ) : ℤ) - 1))) := by ring
    rw [h, hk]
    ring
  have hmem : 2 ∈ Finset.Icc 2 4 := by norm_num
  have hdvdInt : (p : ℤ) ∣ (Nat.card ↥(StatedSU 4 (2 ^ f) E) : ℤ) := by
    rw [hq0, hcard]
    exact Dvd.dvd.mul_left (dvd_trans (by simpa only [Nat.cast_pow] using hfac)
      (Finset.dvd_prod_of_mem (fun i : ℕ =>
        (((p0 ^ f0 : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i)) hmem)) _
  exact_mod_cast hdvdInt

private theorem i167COrth_catalogIs_minus_six_aux2 {f : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ f) ^ 2) : CFSG.IsQuasisimple ↥(StatedSU 4 (2 ^ f) E) := by
  have hnq : (4, 2 ^ f) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) (F := E) (n := 4) hE (by norm_num) hnq).1

private theorem i167COrth_catalogIs_minus_six_aux3 {f p : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ f) ^ 2) (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E))) (isUnA 4 (2 ^ f)) := by
  have hdvd : p ∣ Nat.card ↥(StatedSU 4 (2 ^ f) E) :=
    i167COrth_catalogIs_minus_six_aux1 hE hpq
  have hqTopC : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E)) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E)))
      (i167COrth_catalogIs_minus_six_aux2 hE)
  have hqTop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E)) :=
    ⟨@Group.IsPerfect.commutator_eq_top _ _ hqTopC.1, hqTopC.2.1⟩
  have hJ := H81Orth.centerQuotEquivPSimple_of_dvd_card (G := ↥(StatedSU 4 (2 ^ f) E))
    hp (J := ⊤) hqTop (by rwa [Subgroup.card_top])
  let eTop : ↥(⊤ : Subgroup (StatedSU 4 (2 ^ f) E)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (StatedSU 4 (2 ^ f) E)) ≃*
      ↥(StatedSU 4 (2 ^ f) E) ⧸ Subgroup.center ↥(StatedSU 4 (2 ^ f) E) :=
    QuotientGroup.congr _ _ (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E)))
      (Subgroup.map_center_eq (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E))))
  haveI : Fintype E := Fintype.ofFinite E
  have hK : Fintype.card E = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  obtain ⟨q', hv, -, hq'c, ⟨χ⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := 4) (q := 2 ^ f) hK (by norm_num) (by
        intro h
        exact absurd (congrArg Prod.fst h) (by norm_num))
  let i : TauCeti.CFSGIndex := .lie ⟨.twistedA 3 q', hv⟩
  have hi : isUnA 4 (2 ^ f) i := Or.inl ⟨rfl, hq'c⟩
  exact ⟨i, hi, ⟨(hJ.symm.trans eTop).trans χ⟩⟩

theorem i167COrth_catalogIs_minus_six (hR : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 6) (hminus : ¬ IsPlusType Q) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived Q))) (isUnA 4 (Nat.card F)) := by
  classical
  obtain ⟨f, -, hf⟩ := CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_natCard_eq_two_pow F
  have hpq' : p ∣ 2 ^ f + 1 := by rwa [hf] at hpq
  have hts : ∀ U : Submodule F V, Module.finrank F U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hminus ⟨U, by rw [hU, hdim], hcon⟩
  obtain ⟨E, hEfield, hEfin, hEcard, ⟨θ⟩⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six hf hR hdim hts
  letI instE : Field E := hEfield
  letI instFin : Finite E := hEfin
  have hcatSU : catalogIs (PSimple p (⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E)))
      (isUnA 4 (2 ^ f)) := i167COrth_catalogIs_minus_six_aux3 hEcard hp hpq'
  have hθ : ↥(orthDerived Q) ≃* ↥(StatedSU 4 (2 ^ f) E) := θ
  let e := (Subgroup.topEquiv (G := ↥(orthDerived Q))).trans
      (hθ.trans (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E))).symm)
  have hmain := (CFSG.LocalAnalysis.GLTheoremA.S172B.Cent.catalogIs_pSimple_congr_mulEquiv
    e p (isUnA 4 (2 ^ f))).2 hcatSU
  simpa [hf] using hmain

end CFSG.LocalAnalysis.GLTheoremA.I167

end
