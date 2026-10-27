module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLUMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamQS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsFieldExp
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped IsMulCommutative

section Small

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] {p : ℕ}

theorem dvd_sub_one_of_dvd_pow_sub_one (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m)
    (h : p ∣ m ^ p - 1) : p ∣ m - 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hm), Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h
  rwa [Nat.cast_sub hm, Nat.cast_one]

theorem dvd_card_sub_one_of_pow (hp : p.Prime) {c : Kˣ} (hc1 : c ≠ 1) (hcp : c ^ p = 1) :
    p ∣ Nat.card K - 1 := by
  haveI := Fact.mk hp
  rw [← orderOf_eq_prime hcp hc1, ← Nat.card_units]
  exact orderOf_dvd_natCard c

theorem dvd_card_GL_two_of_plane (hp : p.Prime) {σ : K →+* K}
    {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {M N : Submodule K (ι → K)}
    (hM : Module.finrank K M = 2) {x : GL ι K} (hx : x ∈ blkSub β M N) (hxp : x ^ p = 1)
    (hx1 : ∃ m ∈ M, glEquiv x m ≠ m) :
    p ∣ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  classical
  set g := resU β M N ⟨x, hx⟩ with hg
  have hgp : g ^ p = 1 := by
    have h1 : (⟨x, hx⟩ : blkSub β M N) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hg, ← map_pow, h1, map_one]
  have hg1 : g ≠ 1 := by
    obtain ⟨m, hm, hxm⟩ := hx1
    intro h
    apply hxm
    have h1 := congrArg (fun e : M ≃ₗ[K] M => ((e ⟨m, hm⟩ : M) : ι → K)) h
    simpa [hg, coe_resU_apply] using h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  haveI : Fintype K := Fintype.ofFinite K
  let b := Module.finBasisOfFinrankEq K M hM
  let c : (M ≃ₗ[K] M) ≃ ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    { toFun := fun e => (b.equivFun.symm.trans e).trans b.equivFun
      invFun := fun e => (b.equivFun.trans e).trans b.equivFun.symm
      left_inv := fun e => LinearEquiv.ext fun m => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      right_inv := fun e => LinearEquiv.ext fun v => by
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] }
  have hcard : Nat.card (M ≃ₗ[K] M) =
      (Nat.card K ^ 2 - Nat.card K ^ 0) * (Nat.card K ^ 2 - Nat.card K ^ 1) := by
    rw [Nat.card_congr c, ← Nat.card_congr
      (glEquiv : GL (Fin 2) K ≃* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K))).toEquiv,
      Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
    rfl
  have h := orderOf_dvd_natCard g
  rwa [hord, hcard, pow_zero, pow_one] at h

theorem not_dvd_card_GL_two (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {m : ℕ} (hm : 1 ≤ m)
    (hm3 : ((m : ℕ) : ZMod p) = 3) : ¬ p ∣ (m ^ 2 - 1) * (m ^ 2 - m) := by
  intro h
  have h2 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : 1 ≤ m ^ 2 := hm.trans h2
  have hdvd : p ∣ 2 ^ 4 * 3 := by
    have h' := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_mul, Nat.cast_sub h3, Nat.cast_sub h2, Nat.cast_pow, Nat.cast_one, hm3] at h'
    rw [← ZMod.natCast_eq_zero_iff,
      show ((2 ^ 4 * 3 : ℕ) : ZMod p) = (3 ^ 2 - 1) * (3 ^ 2 - 3) by push_cast; ring]
    exact h'
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

end Small

theorem center_pQuot_eq_bot_of_core {Ω : Type} [Group Ω] {p : ℕ} {S : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) :
    Subgroup.center (PQuot p S) = ⊥ := by
  set e : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot with he
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) g']
  rw [hZ, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot, ← e.map_eq_one_iff]
  exact hez

section Linear

variable {p q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concl_lin
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) [hSn : S.Normal] (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = q ^ f)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (e : PSimple p S ≃* StatedProj (StatedSL n K))
    {Q : TauCeti.PrimePower} (hQq : Q.p = q) (hQK : Q.card = Nat.card K)
    {hv : (TauCeti.LieTypeIndex.A (n - 1) Q).Valid}
    (eL : Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.A (n - 1) Q, hv⟩).Group))
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : CharP K q :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hq hf hK
  have hcharne : ∀ m : ℕ, m.Prime → m ≠ q → (m : K) ≠ 0 := by
    intro m hm hmq h
    exact hmq ((Nat.prime_dvd_prime_iff_eq hq hm).1 ((CharP.cast_eq_zero_iff K q m).1 h)).symm
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcharne 2 Nat.prime_two (Ne.symm hq2)
  have hpK : (p : K) ≠ 0 := hcharne p hp (Ne.symm hqp)
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    exact hq3.trans (Nat.le_self_pow (by omega) q)
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_lin hp hp2 hcore hZ hn hq hf hK (Ne.symm hqp) hdiag e hB
  obtain ⟨Dat, -⟩ : ∃ _ : ClsInner p S B (StatedSL n K)
      (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K), True := by
    rcases hsplit with h | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl h⟩, trivial⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩, trivial⟩
  have hblk : ∀ U W : Submodule K (Fin n → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) u w = 0 ∧
        (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) w u = 0) →
      ((0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) = 0 ∨ ∀ u ∈ U,
        (∀ u' ∈ U, (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ 4 ≤ Nat.card K)) →
      blkI (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W ≤ StatedSL n K ∧
      CFSG.Open.IsQuasisimple ↥(blkI (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W) ∧
      (∀ x ∈ blkSub (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W, orderOf x = p →
        p ∣ Nat.card ↥(blkI (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W)) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) →
        (∀ j ∈ blkI (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) U W,
            y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j) :=
    fun U W hUW _ _ hdim => ⟨blkI_le_statedSL _ U W, isQuasisimple_blkI_zero hUW hdim,
      fun x hx hxp => dvd_card_blkI_zero hUW hdim hp hx hxp,
      fun y hyU hy => exists_smul_of_commute_blkI_zero hUW hdim hyU hy,
      fun A σ hσ hU y hyU k hk0 hkp => not_forall_semiConj_pow_zero hUW hdim hσ hU hyU hk0 hkp⟩
  have hfix3 : ∀ σ : K ≃+* K, Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p →
      3 ≤ Nat.card (semilinearFixedSubfield σ) ∧
        (Nat.card (semilinearFixedSubfield σ) = 3 → ((Nat.card K : ℕ) : ZMod p) = 3) := by
    intro σ hσK
    have h1 : 1 < Nat.card (semilinearFixedSubfield σ) := Finite.one_lt_card
    refine ⟨?_, fun h3 => ?_⟩
    · by_contra hlt
      have h2 : Nat.card (semilinearFixedSubfield σ) = 2 := by omega
      rw [h2, hK] at hσK
      have : 2 ∣ q ^ f := hσK ▸ dvd_pow_self 2 hp.ne_zero
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1
        (Nat.prime_two.dvd_of_dvd_pow this)).symm
    · haveI := Fact.mk hp
      rw [hσK, h3, Nat.cast_pow, ZMod.pow_card]
      norm_num
  have hp3 : ∀ m : ℕ, m = 3 → q = 3 → p ≠ 3 := fun _ _ hq3' hp3' => hqp (hq3'.trans hp3'.symm)
  have hQscal : (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)) →
      4 ≤ Nat.card K ∧ (FieldElt p S B Dat.φ (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)
        Dat.θ Dat.b Dat.A Dat.σ → 4 ≤ Nat.card (semilinearFixedSubfield Dat.σ)) := by
    rintro ⟨c, hc1, hcp, -⟩
    have hd := dvd_card_sub_one_of_pow hp hc1 hcp
    have hp3' : 3 ≤ p := by have := hp.two_le; omega
    refine ⟨by have := Nat.le_of_dvd (by omega) hd; omega, fun hF => ?_⟩
    have hσK := hF.2.2.2.2.1.2.1
    have h1 : 1 ≤ Nat.card (semilinearFixedSubfield Dat.σ) := Nat.card_pos
    rw [hσK] at hd
    have hd' := dvd_sub_one_of_dvd_pow_sub_one hp h1 hd
    have h3 := (hfix3 Dat.σ hσK).1
    have := Nat.le_of_dvd (by omega) hd'
    omega
  have hQdim2 : ∀ (M N : Submodule K (Fin n → K)) (x : GL (Fin n) K), Module.finrank K M = 2 →
      ((0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) = 0 ∨ ∀ m ∈ M,
        (∀ m' ∈ M, (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) m m' = 0) → m = 0) →
      x ∈ blkSub (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) M N → x ^ p = 1 →
      (∃ m ∈ M, glEquiv x m ≠ m) →
      4 ≤ Nat.card K ∧ (FieldElt p S B Dat.φ (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)
        Dat.θ Dat.b Dat.A Dat.σ → 4 ≤ Nat.card (semilinearFixedSubfield Dat.σ)) := by
    intro M N x hM _ hx hxp hx1
    have hd := dvd_card_GL_two_of_plane hp hM hx hxp hx1
    refine ⟨?_, fun hF => ?_⟩
    · by_contra hlt
      have h3 : Nat.card K = 3 := by omega
      have hq3' : q = 3 := by
        rw [hK] at h3
        exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (h3 ▸ dvd_pow_self q (by omega))
      refine not_dvd_card_GL_two hp hp2 (hp3 3 rfl hq3') (by omega) (by rw [h3]; norm_num) hd
    · have hσK := hF.2.2.2.2.1.2.1
      obtain ⟨hge, h3imp⟩ := hfix3 Dat.σ hσK
      by_contra hlt
      have h3 : Nat.card (semilinearFixedSubfield Dat.σ) = 3 := by omega
      have hq3' : q = 3 := by
        have : 3 ∣ q ^ f := by rw [← hK, hσK, h3]; exact dvd_pow_self 3 hp.ne_zero
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1
          (Nat.prime_three.dvd_of_dvd_pow this)).symm
      exact not_dvd_card_GL_two hp hp2 (hp3 3 rfl hq3') (by omega) (h3imp h3) hd
  have hD1 : ∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) →
      IsMaxElem (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
        isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1 := by
    intro Aε _ hA _ hmax ⟨c, hc1, hcp, _⟩ H' hH'
    haveI : Fintype K := Fintype.ofFinite K
    have hd := dvd_card_sub_one_of_pow hp hc1 hcp
    rw [Nat.card_eq_fintype_card] at hd
    exact finrank_weightSpace_eq_one_lin (glRep Aε) hp hA hpK hmax hd H' hH'
  rcases concl_lu (ι := Fin n) hp hB hrank hBC hcore hZ h4 h2K hpK Dat
      ModelGen.statedSL_le_isomGL (Or.inl rfl)
      (fun g _ hg => CFSG.Open.StatedAPI.mem_statedSL_of_det hg)
      (fun g _ hgp => ModelGen.exists_scalar_mul_mem_statedSL hp hdiag hgp)
      (QbigF := fun σ => 4 ≤ Nat.card (semilinearFixedSubfield σ)) hblk
      (fun U W hUW _ _ A σ hσ _ hU hW x hx hxp hdim =>
        glaPLayer_inf_centGL_ne_bot_zero hUW hp hσ hU hW hdim hx hxp)
      (fun _ u v => by simp) hQscal hQdim2 hD1 with
    hA | ⟨hB4, hodd⟩ | ⟨hB4, hn4, hsc, hBdec, hBdisj⟩
  · exact Or.inl hA
  ·
    exfalso
    have hd : HqRank.HqSixIdx q (⟨.A (n - 1) Q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
      refine ⟨hQq, ?_⟩
      rcases hodd with h9 | ⟨h6, hF⟩
      · rw [Fintype.card_fin] at h9
        exact Or.inl (by omega)
      · rw [Fintype.card_fin] at h6
        refine Or.inr ⟨by omega, ?_⟩
        have hp3' : 3 ≤ p := by have := hp.two_le; omega
        exact hp3'.trans (Nat.le_of_dvd Q.exponent_pos (dvd_exponent_of_fieldElt hF hQK.symm))
    have hrk : CFSG.Open.pRank p B ≤ 5 :=
      CFSG.SectionRank.pRank_le hp.one_lt fun _ hEB _ =>
        (Subgroup.card_le_of_le hEB).trans
          (hB4.le.trans (Nat.pow_le_pow_right hp.pos (by norm_num)))
    exact HqRank.not_hq_of_pQuot hq2 hd eL hrk hHq
  ·
    right
    obtain ⟨c, hc1, hcp, -⟩ := hsc
    rw [Fintype.card_fin] at hn4
    have hn3 : n - 1 = 3 := by omega
    have hcat : pSimpleIsLie p S (.A 3 Q) := by
      obtain ⟨eL⟩ := eL
      revert hv eL
      rw [hn3]
      intro hv eL
      exact ⟨TauCeti.CFSGIndex.lie ⟨.A 3 Q, hv⟩, rfl, ⟨eL⟩⟩
    refine Or.inr (Or.inl ⟨hB4, hBdec, hBdisj, center_pQuot_eq_bot_of_core hcore hZ, Q, hQq,
      Or.inl ⟨hcat, ?_⟩⟩)
    rw [hQK]
    exact dvd_card_sub_one_of_pow hp hc1 hcp

end Linear

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
