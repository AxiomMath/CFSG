module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FU9UC

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def NoU38Comp (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
    KD264Lie.fieldSize d.1 ≠ 8 →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Subgroup.center S = ⊥ →
      ∀ (labL : GLALabel) (β : MulAut S), Y10GField.InnDiagKind S labL β →
        β ∈ innAutDerived S → β ^ 3 = 1 → β ≠ 1 →
        ∀ T : Subgroup S, IsComponentOf T (fixSubgroup β) →
          Nat.card (↥T ⧸ Subgroup.center ↥T) ≠ 5515776

@[expose] def u9UnitIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => ¬ (r = 8 ∧ q.card = 2)
  | _ => False

@[expose] def u9ClassIdx : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

section Orders

open Matrix

theorem u9_le_nine_of_pow_two_dvd {k : ℕ} (h : 2 ^ k ∣ 5515776) : k ≤ 9 := by
  rw [show (5515776 : ℕ) = 2 ^ 9 * 10773 by norm_num] at h
  have h512 : 2 ^ k ∣ 2 ^ 9 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (by norm_num : Odd 10773))) h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h512

theorem u9_card_centerQuotient_SL_gen {E : Type} [Field E] [Finite E] {m e : ℕ} (hm : 2 ≤ m)
    (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e) {T : Type*} [Group T]
    (g : SpecialLinearGroup (Fin m) E →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hperf : commutator (SpecialLinearGroup (Fin m) E) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) ≠ 5515776 := by
  classical
  intro hN
  have hdvd := KD264Lie.pow_dvd_card_centerQuotient_of_surjective_specialLinear (E := E) (m := m)
    (e := e) (by omega) he hE g hg hker hperf
  rw [hN] at hdvd
  have hle := u9_le_nine_of_pow_two_dvd hdvd
  have htri : 1 ≤ m * (m - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc 1 * 2 = 2 * 1 := by norm_num
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have he9 : e ≤ 9 := by
    have : e * 1 ≤ e * (m * (m - 1) / 2) := Nat.mul_le_mul_left _ htri
    omega
  have hm4 : m ≤ 4 := by
    by_contra hm5
    have h10 : 10 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      calc 10 * 2 = 5 * 4 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : e * 10 ≤ e * (m * (m - 1) / 2) := Nat.mul_le_mul_left _ h10
    omega
  have hZ : Nat.card (Subgroup.center (SpecialLinearGroup (Fin m) E)) =
      Nat.gcd m (Nat.card E - 1) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.RankThree.PartOne.card_scalars (K := E) (n := m) (by omega)]
  have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := E) (n := m)
    (by omega)
  have hcard := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [hZ, hSL, hN, hE] at hcard
  interval_cases m <;> interval_cases e <;> first | omega | (revert hcard; decide)

theorem u9_card_centerQuotient_statedSU {E : Type} [Field E] [Finite E] {m k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hE : Nat.card E = (2 ^ k) ^ 2) (hne : (m, 2 ^ k) ≠ (3, 2))
    {T : Type*} [Group T] (g : ↥(StatedSU m (2 ^ k) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ k) E))
    (hperf : commutator ↥(StatedSU m (2 ^ k) E) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) * Nat.gcd m (2 ^ k + 1) =
      (2 ^ k) ^ (m * (m - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 m, ((((2 ^ k : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := k) hE
  haveI := hchar
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 k E :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE hk
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := k) hE hm hne
  have hZ : Nat.card (Subgroup.center ↥(StatedSU m (2 ^ k) E)) = Nat.gcd m (2 ^ k + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2) (f := k) hE
      (by omega)
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [← hZ, ← hsplit]
  exact KD264Lie.card_statedSU_eq_nat hUF (by omega)

theorem u9_eq_of_card_centerQuotient_statedSU {E : Type} [Field E] [Finite E] {m k : ℕ}
    (hm : 3 ≤ m) (hk : 1 ≤ k) (hE : Nat.card E = (2 ^ k) ^ 2) (hne : (m, 2 ^ k) ≠ (3, 2))
    {T : Type*} [Group T] (g : ↥(StatedSU m (2 ^ k) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ k) E))
    (hperf : commutator ↥(StatedSU m (2 ^ k) E) = ⊤)
    (hN : Nat.card (T ⧸ Subgroup.center T) = 5515776) : m = 3 ∧ k = 3 := by
  classical
  have hc := u9_card_centerQuotient_statedSU hm hk hE hne g hg hker hperf
  rw [hN] at hc
  have hodd : Odd (Nat.gcd m (2 ^ k + 1)) := by
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ]
    exact ⟨2 ^ j, by ring⟩
  have hdvd : 2 ^ (k * (m * (m - 1) / 2)) ∣ 5515776 := by
    have h1 : 2 ^ (k * (m * (m - 1) / 2)) ∣ 5515776 * Nat.gcd m (2 ^ k + 1) := by
      rw [hc, pow_mul]
      exact dvd_mul_right _ _
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)) h1
  have hle := u9_le_nine_of_pow_two_dvd hdvd
  have h3 : 3 ≤ m * (m - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc 3 * 2 = 3 * 2 := rfl
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have hk3 : k ≤ 3 := by
    have : k * 3 ≤ k * (m * (m - 1) / 2) := Nat.mul_le_mul_left _ h3
    omega
  have hm4 : m ≤ 4 := by
    by_contra hm5
    have h10 : 10 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      calc 10 * 2 = 5 * 4 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : k * 10 ≤ k * (m * (m - 1) / 2) := Nat.mul_le_mul_left _ h10
    omega
  interval_cases m <;> interval_cases k <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd rfl hne
    | (exfalso; revert hc; decide)

theorem u9_card_centerQuotient_Sp_ne {K : Type} [Field K] [Finite K] {s n : ℕ} (hs : 2 ≤ s)
    (hK : Nat.card K = 2 ^ n) (hne : ¬(s = 2 ∧ n = 1)) {T : Type*} [Group T]
    (g : ↥(StatedSp s K) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSp s K))
    (hperf : commutator ↥(StatedSp s K) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) ≠ 5515776 := by
  classical
  intro hN
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [Fintype.card_eq_nat_card, hK])
  haveI : Group.IsPerfect ↥(StatedSp s K) := Group.isPerfect_def.mpr hperf
  have hq : Nat.card (↥(StatedSp s K) ⧸ Subgroup.center ↥(StatedSp s K)) =
      Nat.card (T ⧸ Subgroup.center T) :=
    Nat.card_congr
      (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence g hg hker).toEquiv
  have hP := Nat.card_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s K).toEquiv
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hq, hN, hK] at hP
  have hdvd : 2 ^ (n * s ^ 2) ∣ 5515776 := by
    rw [hP, pow_mul]
    exact dvd_mul_right _ _
  have hle := u9_le_nine_of_pow_two_dvd hdvd
  have hs9 : s ^ 2 ≤ 9 := le_trans (Nat.le_mul_of_pos_left _ hn1) hle
  have hs3 : s ≤ 3 := by nlinarith
  have hn2 : n ≤ 2 := by
    have : n * 4 ≤ n * s ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    omega
  interval_cases s <;> interval_cases n <;>
    first
    | omega
    | exact hne ⟨rfl, rfl⟩
    | (revert hP; decide)

theorem u9_card_centerQuotient_orthDerived_ne {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {T : Type*} [Group T]
    (g : ↥(CFSG.RankThree.Classical2.orthDerived Q) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Q))
    (hperf : commutator ↥(CFSG.RankThree.Classical2.orthDerived Q) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) ≠ 5515776 := by
  intro hN
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT, Subgroup.card_bot, mul_one,
    hN] at hsplit
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hm : Module.finrank K V = 2 * (k - 1 + 1) := by omega
  have h1 := CFSG.HardMathSupport.Dickson.Bal207.OrthFix.factorization_two_card_orthDerived hQ hT
    hm hK
  rw [hsplit, CFSG.HardMathSupport.Dickson.Bal207.OrthFix.factorization_two_su38] at h1
  have he : Even (n * ((k - 1) * (k - 1 + 1))) := (Nat.even_mul_succ_self (k - 1)).mul_left n
  rw [← h1] at he
  exact (by decide : ¬ Even 9) he

end Orders

section UnitaryBlock

open Polynomial Module CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem u9_selfDual_three_of_card {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hℓ : ℓ = 2) {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    {a : primaryFactors (x : Module.End K (Fin n → K))} (ha : IsGoodBlock h x a)
    (hN : Nat.card (↥(KD264Lie.unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(KD264Lie.unitaryBlockComponent h (x := x) (a : K[X]))) = 5515776) :
    dualPoly h.bar (a : K[X]) = a ∧ f * (a : K[X]).natDegree = 3 ∧
      primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) = 3 := by
  classical
  subst hℓ
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  let SB := specialBlock (idForm h n) x (a : K[X])
  let Comp := KD264Lie.unitaryBlockComponent h (x := x) (a : K[X])
  let F := KD264Lie.unitaryPreimageBlock h (x := x) (a : K[X])
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (KD264Lie.unitaryNormOneScalars h n)) F
  have hπF : Function.Surjective πF :=
    (KD264Lie.subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a).1
  have hkerF : πF.ker ≤ Subgroup.center ↥F :=
    (KD264Lie.subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a).2
  let ε : ↥F ≃* ↥SB := KD264Lie.specialBlockEquiv (h := h) H a hq ha
  let πSB : ↥SB →* ↥Comp := πF.comp ε.symm.toMonoidHom
  have hπSB : Function.Surjective πSB := hπF.comp ε.symm.surjective
  have hkerSB : πSB.ker ≤ Subgroup.center ↥SB := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hkerF).trans (Subgroup.comap_center_le_center ε.symm.injective)
  have hQSB : CFSG.IsQuasisimple ↥SB := (specialBlockFacts_of_good H hq a ha).quasisimple ha.1
  haveI hperfSB : Group.IsPerfect ↥SB := hQSB.1
  have hj : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos h.one_le hj
  have hmodel : ∀ {M : Type} [Group M] (eM : ↥SB ≃* M),
      Function.Surjective (πSB.comp eM.symm.toMonoidHom) ∧
        (πSB.comp eM.symm.toMonoidHom).ker ≤ Subgroup.center M ∧ commutator M = ⊤ := by
    intro M _ eM
    refine ⟨hπSB.comp eM.symm.surjective, ?_, ?_⟩
    · rw [← MonoidHom.comap_ker]
      exact (Subgroup.comap_mono hkerSB).trans
        (Subgroup.comap_center_le_center eM.symm.injective)
    · haveI : Group.IsPerfect M :=
        Group.IsPerfect.ofSurjective (f := eM.toMonoidHom) eM.surjective
      exact Group.IsPerfect.commutator_eq_top
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, Φ, -, -⟩ :=
      KD264Lie.exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary (hK := h) H hself
        (selfDualPrimaryBlock H a hself)
    have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) := ha.1
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])) 3 with
      hm | hm
    ·
      exfalso
      have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite (AdjoinRoot (a : K[X])) := hE.finite
      haveI : Finite hE.fixedField := inferInstance
      have hcardF : Nat.card hE.fixedField = 2 ^ (f * (a : K[X]).natDegree) :=
        hE.card_fixedField
      obtain ⟨hs, hk, hp⟩ := hmodel (Φ.trans e2)
      exact u9_card_centerQuotient_SL_gen le_rfl hfd hcardF _ hs hk hp hN
    ·
      obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (Φ.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hne : (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]),
          2 ^ (f * (a : K[X]).natDegree)) ≠ (3, 2) := by
        intro hc
        exact ha.2 hself (by rw [hc]; simp)
      haveI : Finite (AdjoinRoot (a : K[X])) := hE.finite
      have hcardE : Nat.card (AdjoinRoot (a : K[X])) = (2 ^ (f * (a : K[X]).natDegree)) ^ 2 :=
        hE.card_eq_sq
      obtain ⟨hs, hk, hp⟩ := hmodel e4
      obtain ⟨hm3, hk3⟩ := u9_eq_of_card_centerQuotient_statedSU hm hfd hcardE hne _ hs hk hp hN
      exact ⟨hself, hk3, hm3⟩
  ·
    exfalso
    have hne : (a : K[X]) ≠ dualPoly h.bar (a : K[X]) := Ne.symm hself
    obtain ⟨eM⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a hne)
    haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    haveI : Finite K := h.finite
    haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
    have hEcard : Nat.card (AdjoinRoot (a : K[X])) = 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot h
    obtain ⟨hs, hk, hp⟩ := hmodel eM
    exact u9_card_centerQuotient_SL_gen ha.1 (by omega) hEcard _ hs hk hp hN

end UnitaryBlock

section UnitaryMain

open Polynomial Module CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms

theorem u9_fixSubgroup_congr {S P : Type} [Group S] [Group P] (e : S ≃* P) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* P) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ fixSubgroup β
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hy ⊢
    have h1 := congrArg e.symm hy
    simpa [MulAut.congr_apply] using h1
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ fixSubgroup β := hs
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hs' ⊢
    simp [MulAut.congr_apply, hs']

theorem u9_card_centerQuotient_map {S P : Type} [Group S] [Group P] (e : S ≃* P)
    (T : Subgroup S) :
    Nat.card (↥(T.map (e : S →* P)) ⧸ Subgroup.center ↥(T.map (e : S →* P))) =
      Nat.card (↥T ⧸ Subgroup.center ↥T) := by
  let ε : ↥T ≃* ↥(T.map (e : S →* P)) := T.equivMapOfInjective (e : S →* P) e.injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).toEquiv).symm

theorem u9_fixSubgroup_conj {G : Type} [Group G] (a : G) :
    fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set G) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem u9_dim_eq_nine {n : ℕ} {K : Type} [Field K] [Finite K] {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) {a : K[X]}
    (ha : a ∈ primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    (hdeg : a.natDegree = 3)
    (hmult : primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) a = 3) :
    n = 9 := by
  classical
  set x : Module.End K (Fin n → K) := ((Matrix.GeneralLinearGroup.toLin A :
    LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hxdef
  have hx3 : aeval x (X ^ 3 - C (c : K)) = 0 := by
    have h1 : x = Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) := rfl
    rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
      hA]
    ext v i
    by_cases hi : i = v <;> simp [hi]
  have hmin : minpoly K x ∣ X ^ 3 - C (c : K) := minpoly.dvd K x hx3
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.1 ha
  have hmonic3 : (X ^ 3 - C (c : K)).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hdeg3 : (X ^ 3 - C (c : K)).natDegree = 3 := natDegree_X_pow_sub_C
  have ha_eq' : X ^ 3 - C (c : K) = a :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hmonic3 (hdvd.trans hmin) (by rw [hdeg3, hdeg])
  have ha_eq : a = X ^ 3 - C (c : K) := ha_eq'.symm
  have hminm : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hmin_eq : minpoly K x = a := by
    have h1 : minpoly K x ∣ a := ha_eq ▸ hmin
    exact eq_of_monic_of_associated hminm hmon (associated_of_dvd_dvd h1 hdvd)
  have htop : primaryComponent x a = ⊤ := by
    rw [primaryComponent, ← hmin_eq, minpoly.aeval]
    exact LinearMap.ker_zero
  haveI : Fact (Irreducible a) := ⟨hirr⟩
  have h1 : Module.finrank K (primaryComponent x a) = n := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have h2 := finrank_primaryComponent (x := x) (a := a)
  rw [h1, hdeg] at h2
  have h3 : Module.finrank (AdjoinRoot a) (primaryComponent x a) = 3 := hmult
  omega

theorem noU38Comp_unit : NoU38Comp u9UnitIdx := by
  intro d hP hchar h8 S _ _ hSiso _ labL β _ hβmem hβ3 _ T hT hN
  obtain ⟨eS⟩ := hSiso
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | twistedA r0 q0 =>
    obtain ⟨r, q, K, _, h, hr2, hd, hne, ⟨eP⟩⟩ :=
      KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := ⟨.twistedA r0 q0, hv⟩) trivial
    have hd' : r0 = r ∧ q0 = q := TauCeti.LieTypeIndex.twistedA.inj hd
    obtain ⟨rfl, rfl⟩ := hd'
    have hp2 : q0.p = 2 := by simpa using hchar
    have h8' : q0.card ≠ 8 := h8
    have hP' : ¬ (r0 = 8 ∧ q0.card = 2) := hP
    let e : S ≃* primeFormP h (idGram K (r0 + 1)) := eS.trans eP.symm
    have hβ'mem : MulAut.congr e β ∈ innAutDerived (primeFormP h (idGram K (r0 + 1))) :=
      (mem_innAutDerived_congr e).2 hβmem
    have hβ'3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hT' : CFSG.Open.IsComponentOf (T.map (e : S →* primeFormP h (idGram K (r0 + 1))))
        (fixSubgroup (MulAut.congr e β)) := by
      rw [u9_fixSubgroup_congr]
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hT
    have hN' : Nat.card (↥(T.map (e : S →* primeFormP h (idGram K (r0 + 1)))) ⧸
        Subgroup.center ↥(T.map (e : S →* primeFormP h (idGram K (r0 + 1))))) = 5515776 := by
      rw [u9_card_centerQuotient_map, hN]
    have hn3 : 3 ≤ r0 + 1 := by omega
    have hqne : ¬(r0 + 1 = 3 ∧ q0.p ^ q0.exponent = 2) := by
      rintro ⟨h1, h2⟩
      exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
    obtain ⟨A, c, -, hA3, hβeq⟩ :=
      exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived (h := h)
        (C := (1 : GL (Fin (r0 + 1)) K)) isPrimeFormGram_idGram hn3 hqne hβ'mem hβ'3
    rw [hβeq] at hT'
    have H : UnitaryPrimaryData h.bar (idForm h (r0 + 1))
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin (r0 + 1)) K)) :=
      primaryData_toLin' h A.2 Nat.prime_three (by rw [hp2]; norm_num) hA3
    have hq2 : 2 ≤ q0.p ^ q0.exponent := by
      rw [hp2]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q0.exponent := Nat.pow_le_pow_right (by norm_num) q0.exponent_pos
    obtain ⟨a, haT⟩ := exists_good_primaryFactor_of_component hq2 A rfl H _ hT'
    have hN'' := hN'
    rw [haT] at hN''
    obtain ⟨-, hfd, hmult⟩ := u9_selfDual_three_of_card h hp2 H a.2 hN''
    have hf3 : q0.exponent ∣ 3 := ⟨_, hfd.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hf3 with hf1 | hf3'
    · have hdeg : (a.1 : K[X]).natDegree = 3 := by
        obtain ⟨dg, hdg⟩ : ∃ dg, (a.1 : K[X]).natDegree = dg := ⟨_, rfl⟩
        rw [hdg] at hfd ⊢
        simp only [hf1, one_mul] at hfd
        exact hfd
      haveI : Finite K := h.finite
      have hn9 := u9_dim_eq_nine hA3 a.1.2 hdeg hmult
      exact hP' ⟨by omega, by rw [TauCeti.PrimePower.card_def, hp2, hf1]; norm_num⟩
    · exact h8' (by rw [TauCeti.PrimePower.card_def, hp2, hf3']; norm_num)
  | _ => exact hP.elim

end UnitaryMain

section NoCover

private def U9NoCover (X : Type) [Group X] : Prop :=
  ∀ (T : Type) [Group T] (g : X →* T), Function.Surjective g → g.ker ≤ Subgroup.center X →
    Nat.card (T ⧸ Subgroup.center T) ≠ 5515776

private theorem u9NoCover_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : U9NoCover Y) : U9NoCover X := by
  intro T _ g hg hker
  refine h T (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) ?_
  intro y hy
  have hy' : e.symm y ∈ Subgroup.center X := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy))
  rw [Subgroup.mem_center_iff] at hy' ⊢
  intro z
  have h1 := congrArg e (hy' (e.symm z))
  simpa [map_mul] using h1

private theorem u9NoCover_of_card_lt {X : Type} [Group X] [Finite X]
    (h : Nat.card X < 5515776) : U9NoCover X := by
  intro T _ g hg _ hN
  have : Finite T := Finite.of_surjective g hg
  have h1 : Nat.card T ≤ Nat.card X := Nat.card_le_card_of_surjective g hg
  have h2 : Nat.card (T ⧸ Subgroup.center T) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center T))
  omega

private theorem u9_commutator_eq_top_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hX : commutator X = ⊤) : commutator Y = ⊤ := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hX
  exact (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
private theorem u9NoCover_of_orthFactorOver {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≠ 1) (hn3 : n ≠ 3)
    {X : Type} [Group X] (h : OrthFactorOver 2 (2 ^ n) X) (hperf : commutator X = ⊤) :
    U9NoCover X := by
  rcases h with ⟨m, j, E, _, _, hm, hj, -, hcard, -, ⟨e⟩⟩
    | ⟨m, j, q', E, _, _, hm, hj, -, hq', hcard, hne, ⟨e⟩⟩
    | ⟨K', _, _, hK, hchar, s, hs, -, ⟨e⟩⟩
    | ⟨K', _, _, V, _, _, _, Q, hK, hchar, hQ, hd, hT, ⟨e⟩⟩
  · refine u9NoCover_of_mulEquiv e fun T _ g hg hker => ?_
    exact u9_card_centerQuotient_SL_gen hm (Nat.mul_pos hn0 hj)
      (by rw [Nat.card_eq_fintype_card, hcard, ← pow_mul]) g hg hker
      (u9_commutator_eq_top_of_mulEquiv e hperf)
  · have hq'2 : q' = 2 ^ (n * j) := by rw [hq', pow_mul]
    subst hq'2
    refine u9NoCover_of_mulEquiv e fun T _ g hg hker hN => ?_
    obtain ⟨-, h3⟩ := u9_eq_of_card_centerQuotient_statedSU hm (Nat.mul_pos hn0 hj)
      (by rw [Nat.card_eq_fintype_card, hcard]) hne g hg hker
      (u9_commutator_eq_top_of_mulEquiv e hperf) hN
    rcases (Nat.dvd_prime Nat.prime_three).1 ⟨j, h3.symm⟩ with h | h
    · exact hn1 h
    · exact hn3 h
  · haveI : CharP K' 2 := ringChar.of_eq hchar
    refine u9NoCover_of_mulEquiv e fun T _ g hg hker => ?_
    exact u9_card_centerQuotient_Sp_ne hs hK (fun h => hn1 h.2) g hg hker
      (u9_commutator_eq_top_of_mulEquiv e hperf)
  · haveI : CharP K' 2 := ringChar.of_eq hchar
    refine u9NoCover_of_mulEquiv e fun T _ g hg hker => ?_
    exact u9_card_centerQuotient_orthDerived_ne hQ hd hT hK g hg hker
      (u9_commutator_eq_top_of_mulEquiv e hperf)

end NoCover

section SympComp

open Polynomial Module CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

private theorem u9_good_sp {r f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) {A : Subgroup (StatedSp r K)} {s : ℕ} (hs : 1 ≤ s) (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : IsLieFactorOf (fun X _ => U9NoCover X) ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  by_cases hs1 : s = 1
  · subst hs1
    let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
      CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
    have h4 : 4 ≤ Fintype.card K := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
    have hX := slFactorFacts_holds K 2 le_rfl (fun _ => h4)
    exact ⟨Matrix.SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance,
      A.subtype.comp (φ.symm.toMonoidHom.comp e1.toMonoidHom),
      Subtype.val_injective.comp (φ.symm.injective.comp e1.injective),
      range_comp_eq_commutator φ _ (range_equiv_eq_commutator e1 hX.perfect),
      fun T _ g hg hker => u9_card_centerQuotient_SL_gen le_rfl hf1 hK g hg hker hX.perfect⟩
  · have hs2 : 2 ≤ s := by omega
    by_cases hspecial : s = 2 ∧ Fintype.card K = 2
    · obtain ⟨rfl, hc2⟩ := hspecial
      refine ⟨↥(commutator ↥(StatedSp 2 K)), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (commutator ↥(StatedSp 2 K)).subtype),
        Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective),
        range_comp_eq_commutator φ _ (Subgroup.range_subtype _), ?_⟩
      refine u9NoCover_of_card_lt ?_
      have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hc2]
      have h720 : Nat.card ↥(StatedSp 2 K) = 720 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hK2] <;> norm_num
      have := Subgroup.card_le_card_group (commutator ↥(StatedSp 2 K))
      omega
    · have hne : (s, Fintype.card K) ≠ (2, 2) := fun h =>
        hspecial ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      have hne' : ¬(s = 2 ∧ f = 1) := by
        rintro ⟨rfl, rfl⟩
        exact hspecial ⟨rfl, by rw [hcard]; norm_num⟩
      have hX := spFactorFacts_holds K s hs2 hne
      have hθ : (MonoidHom.id ↥(StatedSp s K)).range = commutator ↥(StatedSp s K) := by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
      exact ⟨↥(StatedSp s K), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)),
        Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id),
        range_comp_eq_commutator φ _ hθ,
        fun T _ g hg hker => u9_card_centerQuotient_Sp_ne hs2 hK hne' g hg hker hX.perfect⟩

private theorem u9_good_gl {r : ℕ} {K : Type} [Field K] {E : Type} [Field E] [Finite E] {e : ℕ}
    (hE : Nat.card E = 2 ^ e) (he : 1 ≤ e) (h4 : 4 ≤ Nat.card E) {m : ℕ}
    {A : Subgroup (StatedSp r K)} (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : IsLieFactorOf (fun X _ => U9NoCover X) ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite E
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := isSolvable_gl_of_le_one (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have h4' : 4 ≤ Fintype.card E := by rwa [Fintype.card_eq_nat_card]
  have hX := slFactorFacts_holds E m hm (fun _ => h4')
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine range_eq_commutator_of_perfect θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  exact ⟨Matrix.SpecialLinearGroup (Fin m) E, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective),
    range_comp_eq_commutator φ θ hθ,
    fun T _ g hg hker => u9_card_centerQuotient_SL_gen hm he hE g hg hker hX.perfect⟩

open CFSG.RankThree.CentralLift CFSG.ClassicalGroups.UnitaryFlag in
private theorem u9_good_gu {r : ℕ} {K : Type} [Field K] {g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 g E) (hg3 : g ≠ 3) {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {m : ℕ} (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* sesqUnitaryGroup Hf) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    IsLieFactorOf (fun X _ => U9NoCover X) ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ 2 ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ 2 ^ g))) := fun h => by
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl h
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  have hg1 : 1 ≤ g := hE.one_le
  have hEcard : Fintype.card E = (2 ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
      hHfl hfin
    haveI : Finite ↥hE.fixedField := inferInstance
    haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
    have hFcard : Nat.card ↥hE.fixedField = 2 ^ g := hE.card_fixedField
    have h4 : 4 ≤ Fintype.card ↥hE.fixedField := by
      rw [Fintype.card_eq_nat_card, hFcard]
      exact hq2 rfl
    have hX := slFactorFacts_holds ↥hE.fixedField 2 le_rfl (fun _ => h4)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e
    exact ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, inferInstance, ψ,
      hψi, hψ, fun T _ g' hg' hker =>
        u9_card_centerQuotient_SL_gen le_rfl hg1 hFcard g' hg' hker hX.perfect⟩
  · have hnq : (m, 2 ^ g) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := hq3 h1
      omega
    have hX := suFactorFacts_holds E m (2 ^ g) hEcard hm3 hnq
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (2 ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (2 ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e'
    refine ⟨↥(StatedSU m (2 ^ g) E), inferInstance, inferInstance, ψ, hψi, hψ, ?_⟩
    intro T _ g' hg' hker hN
    obtain ⟨-, hg3'⟩ := u9_eq_of_card_centerQuotient_statedSU hm3 hg1 hE.card_eq_sq hnq g' hg'
      hker hX.perfect hN
    exact hg3 hg3'

private theorem u9_natDegree_le_two {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {y : Module.End K V} (hy : y ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors y) (h1 : h ≠ X - 1) : h.natDegree ≤ 2 := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.1 hh
  have hmin : minpoly K y ∣ X ^ 3 - 1 := minpoly.dvd K y (by simp [hy])
  have hfac : (X ^ 3 - 1 : K[X]) = (X - C 1) * (X ^ 2 + X + 1) := by
    rw [C_1]
    ring
  rw [hfac] at hmin
  rcases hirr.prime.dvd_or_dvd (hdvd.trans hmin) with h2 | h2
  · exfalso
    apply h1
    have hdeg : (X - C 1 : K[X]).natDegree ≤ h.natDegree := by
      rw [natDegree_X_sub_C]
      exact Irreducible.natDegree_pos hirr
    have := eq_of_monic_of_dvd_of_natDegree_le hmon (monic_X_sub_C 1) h2 hdeg
    rw [C_1] at this
    exact this.symm
  · have hne : (X ^ 2 + X + 1 : K[X]) ≠ 0 := by
      intro h0
      have := congrArg (fun p => p.coeff 0) h0
      simp at this
    calc h.natDegree ≤ (X ^ 2 + X + 1 : K[X]).natDegree := natDegree_le_of_dvd h2 hne
      _ ≤ 2 := by compute_degree

private theorem u9_good_spOrbit {r f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) (hf3 : f ≠ 3) {x : StatedSp r K} (hx : x ^ 3 = 1)
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks 2 f 3 x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    IsLieFactorOf (fun X _ => U9NoCover X)
      ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
        spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  classical
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact u9_good_sp hK hf1 hs1 (φ.trans e) hQ
    · obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      have hle := u9_natDegree_le_two (spEnd_pow hx) h.2 h1
      have hpos : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hd1 : d = 1 := by omega
      subst hd1
      exact u9_good_gu hE (by rw [mul_one]; exact hf3) hHf hHfl e he φ hQ
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hEc : Nat.card (AdjoinRoot (h : K[X])) = 2 ^ (f * (h : K[X]).natDegree) := by
      rw [hP.card_field, pow_mul]
    have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
      have hN : 2 ^ f ≤ (2 ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      have hle := Nat.le_of_dvd (by omega) hP.dvd
      rw [hP.card_field]
      omega
    exact u9_good_gl hEc (Nat.mul_pos hf1 hdeg) h4 φ hQ

theorem u9_sp_comp_card_ne {r f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) (hf3 : f ≠ 3) (hr : 1 ≤ r) (x : StatedSp r K) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (L : Subgroup (StatedProj (StatedSp r K)))
    (hL : IsComponentOf L (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x)))) :
    Nat.card (↥L ⧸ Subgroup.center ↥L) ≠ 5515776 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) hcardK
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) 3 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _) (by norm_num)
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
    hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
      (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
      (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hK
    Nat.prime_three (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  obtain ⟨X, inst, -, hX, g, hg, hker⟩ :=
    components_of_orbit_family_lieFactor (P := fun X _ => U9NoCover X) x
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O =>
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
          (by norm_num) hq hsq blocks O)
      (fun O hQ => by
        obtain ⟨O, h, hh, rfl⟩ := O
        exact u9_good_spOrbit hK hf1 hf3 hx hsq blocks ⟨h, hh⟩ hQ) L hL
  exact hX _ g hg hker

end SympComp

section OrthComp

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.Classical2 (ProjOrthDerived)

theorem u9_orth_comp_card_ne {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] [Finite G] {m n : ℕ} (hG : StatedClassicalModel G t m 2 n) (hn3 : n ≠ 3)
    (a : G) (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (J : Subgroup G)
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 5515776 := by
  intro hN
  have hn0 : 1 ≤ n := by
    rcases ht with rfl | rfl
    · exact hG.1.2.1
    · exact hG.1.2.1
  by_cases hn1 : n = 1
  · subst hn1
    obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcard, hring, ⟨e⟩⟩ :=
      exists_projOrth_model_card (Or.inr ht) hG
    haveI : CharP K 2 := ringChar.of_eq hring
    have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
    haveI : Nontrivial V := by
      obtain ⟨U, hU3, -⟩ := hT
      exact Module.nontrivial_of_finrank_pos (R := K)
        (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e a)
    have hxa : CFSG.RankThree.PartOne.piOrth Q x = e a := hx
    have hx3 : orderOf x = 3 := by
      have h1 : orderOf (CFSG.RankThree.PartOne.piOrth Q x) = orderOf x :=
        orderOf_injective _ (CFSG.RankThree.PartOne.piOrth_injective hQ) x
      have h2 : orderOf (e a) = orderOf a := orderOf_injective e.toMonoidHom e.injective a
      rw [← h1, hxa, h2]
      exact orderOf_eq_prime ha ha1
    have hcongr : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have hJ' : IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
        (Subgroup.centralizer ({CFSG.RankThree.PartOne.piOrth Q x} : Set (ProjOrthDerived Q))) := by
      rw [hxa, ← u9_fixSubgroup_conj, ← hcongr, u9_fixSubgroup_congr]
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
    have hN' : Nat.card (↥(J.map (e : G →* ProjOrthDerived Q)) ⧸
        Subgroup.center ↥(J.map (e : G →* ProjOrthDerived Q))) = 5515776 := by
      rw [u9_card_centerQuotient_map, hN]
    have h8 := (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.eq_componentImage_of_card
      (Or.inl hK2) hQ x hx3 hJ' hN').1
    rw [hK2] at h8
    norm_num at h8
  · obtain ⟨X, _, _, hXLie, hfac, -, g, hg, hker⟩ :=
      exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
        omegaFactorField_holds Nat.prime_three (by decide) (Or.inr ht) hG (by decide) a ha J hJ
    exact u9NoCover_of_orthFactorOver hn0 hn1 hn3 hfac hXLie.perfect _ g hg hker hN

end OrthComp

end CFSG.LocalAnalysis.GLTheoremA.I141FU9UC

end
