module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSetup
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClNum
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClRank
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitary
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher


private theorem su_arith {q m g : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m) (hg : g ∣ q + 1)
    {P : ℤ} (h : (q : ℤ) ^ (m * (m - 1) / 2) * P = 60 * g) : False := by
  have hcop : Nat.Coprime q g := by
    refine Nat.Coprime.coprime_dvd_right hg ?_
    simp
  have hcopZ : IsCoprime ((q : ℤ) ^ (m * (m - 1) / 2)) (g : ℤ) :=
    (Nat.isCoprime_iff_coprime.2 hcop).pow_left
  have hdvdZ : ((q : ℤ) ^ (m * (m - 1) / 2)) ∣ 60 :=
    hcopZ.dvd_of_dvd_mul_right (Dvd.intro _ h)
  have hdvd : q ^ (m * (m - 1) / 2) ∣ 60 := by
    exact_mod_cast hdvdZ
  have hk : 3 ≤ m * (m - 1) / 2 := by
    have : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have h3 : q ^ 3 ∣ 60 := (pow_dvd_pow q hk).trans hdvd
  have hq4 : q ≤ 3 := by
    by_contra hcon
    have h4 : 4 ≤ q := by omega
    have h1 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h4 3
    have h2 : q ^ 3 ≤ 60 := Nat.le_of_dvd (by norm_num) h3
    omega
  interval_cases q <;> revert h3 <;> decide

open CFSG.ClassicalGroups.UnitaryFlag in
private theorem su_a5_false {E : Type} [Field E] [Finite E] {p f m : ℕ} (hU : UnitaryFieldData p f E)
    (hm : 3 ≤ m)
    (h60 : Nat.card (↥(StatedSU m (p ^ f) E) ⧸ Subgroup.center ↥(StatedSU m (p ^ f) E)) = 60) :
    False := by
  have hmul :=
    (Subgroup.center ↥(StatedSU m (p ^ f) E)).card_eq_card_quotient_mul_card_subgroup
  rw [h60] at hmul
  have hq : 2 ≤ p ^ f := by
    have := Nat.one_lt_pow (by have := hU.one_le; omega : f ≠ 0) hU.prime.one_lt
    omega
  have hform := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := m) (by omega)
  have hNat : Nat.card E = (p ^ f) ^ 2 := hU.card_eq_sq
  haveI : Fact p.Prime := ⟨hU.prime⟩
  by_cases hmq : (m, p ^ f) = (3, 2)
  · obtain ⟨rfl, h2⟩ := Prod.mk.inj hmq
    have h216 : (Nat.card ↥(StatedSU 3 (p ^ f) E) : ℤ) = 216 := by
      rw [hform, h2, show Finset.Icc 2 3 = {2, 3} by decide]
      norm_num
    have h216' : Nat.card ↥(StatedSU 3 (p ^ f) E) = 216 := by exact_mod_cast h216
    omega
  · have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat hm hmq
    have hZ : Nat.card (Subgroup.center ↥(StatedSU m (p ^ f) E)) = Nat.gcd m (p ^ f + 1) := by
      rw [hQ.2]
      exact (CFSG.LinearGroups.unitary_scalar_kernel hU.prime hNat (by omega)).2.2
    rw [hZ] at hmul
    rw [hmul] at hform
    exact su_arith (q := p ^ f) (m := m) (g := Nat.gcd m (p ^ f + 1)) hq hm (Nat.gcd_dvd_right _ _)
      (P := ∏ i ∈ Finset.Icc 2 m, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i))
      (by push_cast at hform ⊢; linarith)

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem card_quotient_center_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) :
    Nat.card (Y ⧸ Subgroup.center Y) = Nat.card (Z ⧸ Subgroup.center Z) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

private theorem prime_pow_eq_four {ℓ n : ℕ} (hℓ : ℓ.Prime) (h : ℓ ^ n = 4) : ℓ = 2 ∧ n = 2 := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have h1 : ℓ ∣ 2 ^ 2 := by
    have : ℓ ∣ ℓ ^ n := dvd_pow_self ℓ hn
    rw [h] at this
    simpa using this
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h1)
  subst hℓ2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by simpa using h)⟩

private theorem prime_pow_eq_five {ℓ n : ℕ} (hℓ : ℓ.Prime) (h : ℓ ^ n = 5) : ℓ = 5 := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have h1 : ℓ ∣ 5 := by
    have : ℓ ∣ ℓ ^ n := dvd_pow_self ℓ hn
    rwa [h] at this
  exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 h1

section Block

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

private theorem good_block_a5 (hℓ5 : ℓ ≠ 5) (hq : 2 ≤ ℓ ^ f) (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {Y : Type} [Group Y] (e : Y ≃* ↥(specialBlock B x (a : K[X])))
    (hY : Nat.card (Y ⧸ Subgroup.center Y) = 60) :
    dualPoly hK.bar (a : K[X]) = a ∧ (a : K[X]).natDegree = 1 ∧ ℓ ^ f = 4 ∧
      primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by
  classical
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  haveI : Fact ℓ.Prime := ⟨hK.prime⟩
  have hirr : Irreducible (a : K[X]) := irreducible_of_mem_primaryFactors a.2
  haveI : Fact (Irreducible (a : K[X])) := ⟨hirr⟩
  have hd : 1 ≤ (a : K[X]).natDegree := Irreducible.natDegree_pos hirr
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  have h0 := coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree a.2
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e'⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    have hodd := (selfDualPrimaryBlock H a hself).odd_natDegree
    have hnum := isGoodBlock_numeric hq hself ha
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hm2' : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
      have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := hm2'
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      have hcardF : Nat.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) :=
        hE.card_fixedField
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) hE.fixedField ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) hE.fixedField)) = 60 := by
        rw [← card_quotient_center_of_mulEquiv (((e.trans e').trans e2)), hY]
      obtain ⟨-, hF45⟩ := sl_a5
        (le_refl 2) hSL
      rw [hcardF] at hF45
      have hF4 : ℓ ^ (f * (a : K[X]).natDegree) = 4 := by
        rcases hF45 with h4 | h5
        · exact h4
        · exact absurd (prime_pow_eq_five hK.prime h5) hℓ5
      obtain ⟨hℓ2, hfd⟩ := prime_pow_eq_four hK.prime hF4
      have hd1 : (a : K[X]).natDegree = 1 := by
        have h2 : f * (a : K[X]).natDegree = 2 := hfd
        rcases hodd with ⟨k, hk⟩
        have : (a : K[X]).natDegree ∣ 2 := ⟨f, by rw [← h2]; ring⟩
        have hle : (a : K[X]).natDegree ≤ 2 := Nat.le_of_dvd (by norm_num) this
        omega
      refine ⟨hself, hd1, ?_, hm2'⟩
      rw [hd1, mul_one] at hF4
      exact hF4
    · exfalso
      obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e'.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hSU : Nat.card (↥(CFSG.Open.StatedSU (primaryMultiplicity (x : Module.End K V)
          (a : K[X])) (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X]))) ⧸
          Subgroup.center ↥(CFSG.Open.StatedSU (primaryMultiplicity (x : Module.End K V)
          (a : K[X])) (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X])))) = 60 := by
        rw [← card_quotient_center_of_mulEquiv (e.trans e4), hY]
      exact su_a5_false hE hm hSU
  · exfalso
    obtain ⟨ep⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hSL : Nat.card (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])))) =
        60 := by
      rw [← card_quotient_center_of_mulEquiv (e.trans ep), hY]
    obtain ⟨-, hE45⟩ := sl_a5 hm2 hSL
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      CFSG.RankThree.PartOne.KCUnitary.natCard_adjoinRoot hK
    rw [hcard] at hE45
    have hE4 : ℓ ^ (2 * (f * (a : K[X]).natDegree)) = 4 := by
      rcases hE45 with h4 | h5
      · exact h4
      · exact absurd (prime_pow_eq_five hK.prime h5) hℓ5
    obtain ⟨hℓ2, h2fd⟩ := prime_pow_eq_four hK.prime hE4
    have hf1 : f = 1 := by
      have := hK.one_le
      have : f * (a : K[X]).natDegree = 1 := by omega
      exact Nat.eq_one_of_mul_eq_one_right this
    have hd1 : (a : K[X]).natDegree = 1 := by
      have : f * (a : K[X]).natDegree = 1 := by omega
      exact Nat.eq_one_of_mul_eq_one_left this
    have hmonic : (a : K[X]).Monic := monic_of_mem_primaryFactors a.2
    have haμ : (a : K[X]) = X - C (-(a : K[X]).coeff 0) := by
      rw [hmonic.eq_X_add_C hd1]
      simp [sub_eq_add_neg]
    have hμ0 : -(a : K[X]).coeff 0 ≠ 0 := neg_ne_zero.2 h0
    have hbar0 : hK.bar (-(a : K[X]).coeff 0) ≠ 0 := (map_ne_zero hK.bar).2 hμ0
    have hKcard : Nat.card K = 4 := by
      rw [hK.card, hℓ2, hf1]
      norm_num
    haveI : Fintype K := Fintype.ofFinite K
    have hμ3 : (-(a : K[X]).coeff 0) ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (-(a : K[X]).coeff 0) hμ0
      rwa [← Nat.card_eq_fintype_card, hKcard] at this
    have hbarμ : hK.bar (-(a : K[X]).coeff 0) = (-(a : K[X]).coeff 0) ^ 2 := by
      rw [hK.bar_apply, hℓ2, hf1]
      norm_num
    have hnorm : hK.bar (-(a : K[X]).coeff 0) * (-(a : K[X]).coeff 0) = 1 := by
      rw [hbarμ, ← pow_succ]
      exact hμ3
    apply hself
    rw [haμ, CFSG.RankThree.PartOne.KCUnitaryBlock.dualPoly_X_sub_C hbar0]
    congr 2
    exact inv_eq_of_mul_eq_one_right hnorm

end Block

section Component

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem unitary_component_a5 {n ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    (hℓ5 : ℓ ≠ 5) (A : primeFormUnitary h (idGram F n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (glA (A : GL (Fin n) F)))
    (J' : Subgroup (primeFormP h (idGram F n)))
    (hJ' : CFSG.Open.IsComponentOf J' (fixSubgroup (primeFormConjHom h (idGram F n) A)))
    (hcard : Nat.card (↥J' ⧸ Subgroup.center ↥J') = 60) :
    ∃ a : {a : primaryFactors (glA (A : GL (Fin n) F) : Module.End F (Fin n → F)) //
        IsGoodBlock h (glA (A : GL (Fin n) F)) a},
      J' = ((specialBlock (idForm h n) (glA (A : GL (Fin n) F)) (a.1 : F[X])).comap
        (UnitaryBlocks.toLinSU h n)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram F n)) n)) ∧
      dualPoly h.bar (a.1 : F[X]) = a.1 ∧ (a.1 : F[X]).natDegree = 1 ∧ ℓ ^ f = 4 ∧
      primaryMultiplicity (glA (A : GL (Fin n) F) : Module.End F (Fin n → F)) (a.1 : F[X]) = 2 := by
  classical
  haveI := h.finite
  obtain ⟨⟨⟨j, hj⟩, hgood⟩, hJeq⟩ :=
    UnitaryBlocks.exists_good_block_of_component (two_le_pow_of h) A rfl H J' hJ'
  refine ⟨⟨⟨j, hj⟩, hgood⟩, hJeq, ?_⟩
  have hFq := UnitaryGlue.isQuasisimple_specialSU h H hj hgood
  let π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram F n)) n)
  set S : Subgroup (gramSU h (idGram F n)) := UnitaryGlue.specialSU h (A : GL (Fin n) F) j with hS
  have hker : (π.subgroupMap S).ker ≤ Subgroup.center ↥S := by
    intro u hu
    have h1 : π (u : gramSU h (idGram F n)) = 1 := congrArg Subtype.val hu
    have h2 : (u : gramSU h (idGram F n)) ∈ normOneScalars h (gramSU h (idGram F n)) n :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 := normOneScalars_le_center h _ n h2
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.1 h3 _
  obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hFq.1.commutator_eq_top (π.subgroupMap S)
    (MonoidHom.subgroupMap_surjective π S) hker
  have hJeq' : J' = S.map π := hJeq
  have hY : Nat.card (↥S ⧸ Subgroup.center ↥S) = 60 := by
    rw [Nat.card_congr eq.toEquiv]
    subst hJeq'
    exact hcard
  let e : ↥S ≃* ↥(specialBlock (idForm h n) (glA (A : GL (Fin n) F)) j) :=
    (Subgroup.equivMapOfInjective S (UnitaryBlocks.toLinSU h n)
      UnitaryBlocks.toLinSU_injective).trans
        (MulEquiv.subgroupCongr (UnitaryGlue.map_specialSU h H hj hgood))
  exact good_block_a5 hℓ5 (two_le_pow_of h) H ⟨j, hj⟩ hgood e hY

end Component

section Main

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem unitary_data {K : Type} [Group K] [Finite K] {n ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hℓ5 : ℓ ≠ 5) (φ : K ≃* primeFormP h (idGram F n))
    {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K}
    (D : Data K Q x J₁ J₂) :
    ℓ ^ f = 4 ∧ 4 ≤ n := by
  classical
  haveI := h.finite
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (φ x)
  let A : primeFormUnitary h (idGram F n) :=
    ⟨(t : GL (Fin n) F), ((mem_gramSU_iff_unitary h).1 t.2).1⟩
  have hconjt : primeFormConjHom h (idGram F n) A = MulAut.conj (t : primeFormP h (idGram F n)) := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, MulAut.conj_apply]
    rfl
  have hβ : primeFormConjHom h (idGram F n) A = MulAut.congr φ (MulAut.conj x) := by
    rw [hconjt, congr_conj_eq]
    congr 1
  have hx5 : (t : primeFormP h (idGram F n)) ^ 5 = 1 := by
    rw [ht, ← map_pow, D.pow_five, map_one]
  obtain ⟨c, -, -, hc⟩ : (t ^ 5) ∈ normOneScalars h (gramSU h (idGram F n)) n := by
    have h1 : ((t ^ 5 : gramSU h (idGram F n)) : primeFormP h (idGram F n)) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hx5
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hA5 : (A : GL (Fin n) F) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    have : ((t ^ 5 : gramSU h (idGram F n)) : GL (Fin n) F) = (A : GL (Fin n) F) ^ 5 := rfl
    rw [← this]
    exact hc
  have hpℓ : 5 ≠ ℓ := Ne.symm hℓ5
  have H := UnitaryBlocks.primaryData_toLin' h A.2 Nat.prime_five hpℓ hA5
  have hlayer : PerfectInLayer (MulAut.congr φ (MulAut.conj x)) := by
    rw [← hβ]
    exact fun P hP hperf =>
      LieSemisimple.perfectInLayer_primeFormConjHom h Nat.prime_five hpℓ A hA5 P hP hperf
  obtain ⟨hc₁, h₁⟩ := five_component_data φ hlayer D.five.comp₁ D.five.quot₁
  obtain ⟨hc₂, h₂⟩ := five_component_data φ hlayer D.five.comp₂ D.five.quot₂
  rw [← hβ] at hc₁ hc₂
  obtain ⟨a₁, ha₁, hs₁, hd₁, hq₁, hm₁⟩ := unitary_component_a5 h hℓ5 A H _ hc₁ h₁
  obtain ⟨a₂, ha₂, hs₂, hd₂, hq₂, hm₂⟩ := unitary_component_a5 h hℓ5 A H _ hc₂ h₂
  refine ⟨hq₁, ?_⟩
  have hne : a₁.1 ≠ a₂.1 := by
    intro heq
    apply D.five.ne
    apply Subgroup.map_injective (f := (φ : K →* primeFormP h (idGram F n))) φ.injective
    have : a₁ = a₂ := Subtype.ext heq
    rw [ha₁, ha₂, this]
  have hsum := finrank_eq_sum_degree_mul_multiplicity
    (x := (glA (A : GL (Fin n) F) : Module.End F (Fin n → F))) H.squarefree
  rw [Module.finrank_fin_fun] at hsum
  have hsub : ({a₁.1, a₂.1} : Finset (primaryFactors (glA (A : GL (Fin n) F) :
      Module.End F (Fin n → F)))) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset (f := fun a : primaryFactors (glA (A : GL (Fin n) F) :
      Module.End F (Fin n → F)) => (a : F[X]).natDegree *
        primaryMultiplicity (glA (A : GL (Fin n) F) : Module.End F (Fin n → F)) (a : F[X])) hsub
  rw [Finset.sum_pair hne, ← hsum] at hle
  rw [hd₁, hm₁, hd₂, hm₂] at hle
  omega

end Main

theorem i1434Cl_PSU {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSU n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂) : ℓ = 2 ∧ f = 2 ∧ n = 4 := by
  obtain ⟨⟨hℓp, hf, hn3, -⟩, F, _, _, hF, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData ℓ f F := ⟨hℓp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h
    (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := n) (K := F))
  let φ : K ≃* primeFormP h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F n) :=
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  obtain ⟨hq4, hn4⟩ := unitary_data h hℓ φ D
  obtain ⟨hℓ2, hf2⟩ := prime_pow_eq_four hℓp hq4
  refine ⟨hℓ2, hf2, ?_⟩
  by_contra hn
  have hn5 : 5 ≤ n := by omega
  have h5 : 5 ∣ ℓ ^ f + 1 := by
    rw [hq4]
  exact false_of_psu_five_le h hn5 h5 eT D.rank D.abelian

theorem i1434Cl_PSU_iso {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSU n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂) :
    Nonempty (K ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 2) := by
  obtain ⟨rfl, rfl, rfl⟩ := i1434Cl_PSU hm hℓ D
  exact CFSG.RankThree.PartOne.projSU_of_statedClassicalModel hm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
