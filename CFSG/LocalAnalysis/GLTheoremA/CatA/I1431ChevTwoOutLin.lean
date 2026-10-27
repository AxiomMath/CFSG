module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Diag
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOdd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator
  (l2Aut3Classification_holds l2FieldFixed_holds l2fld_isQuasisimple_psl2
    l2fld_isSolvable_psl2_of_card_le_three l514c_card_psl2)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns (fixSub)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (exists_noncomm_of_center_bot)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (commutator_fixed_mem_range)
open CFSG.HardMathSupport.Dickson.Sec6 (FamA1 FamA2 FamAHigh)
open scoped commutatorElement

section NoCertificate

theorem mem_innAutDerived_of_linearAut_pow_three {n : ℕ} {K : Type} [Field K] [Finite K]
    {ψ : MulAut (projectiveSL n K)} (hψ3 : ψ ^ 3 = 1) (hD : ψ ∈ linearAutGroup n K) :
    ψ ∈ innAutDerived (projectiveSL n K) := by
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hD
  refine mem_innAutDerived_of_inner_inv_of_odd (τ := dualAut n K) (p := 3) ⟨1, rfl⟩ hψ3 ?_
  rw [← hA]
  exact CFSG.HardMathSupport.Dickson.Sec6.I923.isInnerAut_dual_conj_mul A

theorem two_pow_mul_ne_25920 (g : ℕ) : 2 ^ g * (4 ^ g - 1) ≠ 25920 := by
  intro h
  have hg : g ≤ 6 := by
    by_contra hcon
    push Not at hcon
    have h1 : 2 ^ 7 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hcon
    have h2 : 4 ^ 7 ≤ 4 ^ g := Nat.pow_le_pow_right (by norm_num) hcon
    have h3 : 1 ≤ 4 ^ g - 1 := by omega
    have h4 : 128 * 16000 ≤ 2 ^ g * (4 ^ g - 1) := by
      calc 128 * 16000 ≤ 2 ^ 7 * (4 ^ 7 - 1) := by norm_num
        _ ≤ 2 ^ g * (4 ^ g - 1) := Nat.mul_le_mul h1 (by omega)
    omega
  interval_cases g <;> simp at h

theorem u42Out_A1 : U42OuterAt FamA1 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | A r q =>
    have hr : r = 1 := hF
    subst hr
    have hp2 : q.p = 2 := hc
    exfalso
    have hm : CFSG.Models.LieModel S .PSL 2 q.p q.exponent := CFSG.Models.lieModel_A 1 q hv e
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      hm.2.resolve_right (fun h => absurd h.1 (by norm_num))
    haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S eK.toEquiv
    have hβ3 : MulAut.congr eK α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβ1 : MulAut.congr eK α ≠ 1 := fun h =>
      hp.2.1 ((MulAut.congr eK).injective (h.trans (map_one _).symm))
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, hp2]
    have hlay : U42Layer (MulAut.congr eK α) False := by
      set β := MulAut.congr eK α with hβdef
      have hfx : Lemma510Ns.fixSub β = fixSubgroup β := Subgroup.ext fun _ => Iff.rfl
      rcases l2Aut3Classification_holds K β hβ3 with h1 | hsol | ⟨σ, φ, γ, hφ, hβ⟩
      · exact absurd h1 hβ1
      · exact u42Layer_of_solvable_fixed (by rwa [← hfx])
      · obtain ⟨F₀, _, _, hcard, ⟨ψ0⟩⟩ := l2FieldFixed_holds K β hβ3 hβ1 σ φ γ hφ hβ
        have ψ1 : ↥(fixSubgroup β) ≃* StatedProj (StatedSL 2 F₀) :=
          (MulEquiv.subgroupCongr hfx.symm).trans ψ0
        by_cases h4 : 4 ≤ Nat.card F₀
        · obtain ⟨hQ₀, hZ₀⟩ := l2fld_isQuasisimple_psl2 h4
          have hsimple : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) := by
            haveI := hQ₀.2
            exact ((QuotientGroup.quotientMulEquivOfEq hZ₀).trans
              QuotientGroup.quotientBot).symm.isSimpleGroup
          haveI := hsimple
          refine u42Layer_of_fixed_equiv β ψ1 hsimple
            (exists_noncomm_of_center_bot hZ₀) fun hT => ?_
          have h25920 := CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT
          obtain ⟨g, hg⟩ : ∃ g : ℕ, Nat.card F₀ = 2 ^ g := by
            have hdvd : Nat.card F₀ ∣ 2 ^ q.exponent := by
              rw [← hK2, hcard]
              exact dvd_pow_self _ (by norm_num)
            obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
            exact ⟨g, hg⟩
          have hg1 : 1 ≤ g := by
            rcases Nat.eq_zero_or_pos g with h0 | h0
            · rw [h0] at hg; omega
            · exact h0
          have hodd : Odd (2 ^ g - 1) := by
            obtain ⟨c, hc'⟩ := dvd_pow_self 2 (show g ≠ 0 by omega)
            have hpos : 0 < 2 ^ g := Nat.two_pow_pos g
            exact ⟨c - 1, by omega⟩
          have hgcd : Nat.gcd 2 (2 ^ g - 1) = 1 := Nat.coprime_two_left.2 hodd
          have hord := l514c_card_psl2 (F := F₀)
          rw [h25920, hg, hgcd, mul_one] at hord
          have hsq : (2 ^ g) ^ 2 = 4 ^ g := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [hsq] at hord
          exact two_pow_mul_ne_25920 g hord.symm
        · haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
            l2fld_isSolvable_psl2_of_card_le_three (F := F₀) (by omega)
          exact u42Layer_of_solvable_fixed
            (Group.isSolvable_of_isSolvable_injective (f := ψ1.toMonoidHom) ψ1.injective)
    exact hp.apply (u42Layer_congr eK hlay)
  | _ => exact hF.elim

end NoCertificate

section Field


theorem u42Layer_fieldAut_psl {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    U42Layer (fieldAut n K σ) False := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let S : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range
  let eS : ↥S ≃* projectiveSL n ↥k := (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      simpa using this)⟩
  have hSle : S ≤ fixSubgroup (fieldAut n K σ) := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y
  have hcomm : ⁅fixSubgroup (fieldAut n K σ), fixSubgroup (fieldAut n K σ)⁆ ≤ S :=
    Subgroup.commutator_le.2 fun a ha b hb => commutator_fixed_mem_range (by omega) ha hb
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  refine u42Layer_of_simple_normal_comm _ S hSle hcomm hs hnab fun hT => ?_
  have hadm : StatedLieAdmissible .PSL n 2 (f / 3) :=
    ⟨Nat.prime_two, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : Blueprint.LieModel ↥S .PSL n 2 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eS.trans (statedProjEquiv n ↥k).symm⟩⟩
  exact absurd (eq_of_catalogIs_u4two_lieModel hT hmodel).1 (by decide)

theorem u42Out_lin_model {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (hm : Blueprint.LieModel S .PSL n 2 f) (α : MulAut S) (hα : α ∉ innAutDerived S)
    (hp : U42Pumpup S α) : False := by
  have hC : StatedClassicalModel S .PSL n 2 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : S ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv S e.toEquiv
  have hψ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
  by_cases hdiag : MulAut.congr e α ∈ linearAutGroup n K
  · exact hα ((mem_innAutDerived_congr e).mp
      (mem_innAutDerived_of_linearAut_pow_three hψ3 hdiag))
  · obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn (MulAut.congr e α) hψ3 hdiag
    have h1 : U42Layer (MulAut.congr e α) False := by
      rw [hψH]
      exact u42Layer_conj _ (u42Layer_fieldAut_psl hn hσ hf hK)
    exact hp.apply (u42Layer_congr e h1)

theorem u42Out_A2 : U42OuterAt FamA2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | A r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr2 : r = 2 := hF
    subst hr2
    have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_A 2 q hv e
    rw [hq2] at hm
    exact u42Out_lin_model (by norm_num) q.exponent_pos hm α hα hp
  | _ => exact hF.elim

theorem u42Out_AHigh : U42OuterAt FamAHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | A r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr3 : 3 ≤ r := hF
    have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_A r q hv e
    rw [hq2] at hm
    exact u42Out_lin_model (by omega) q.exponent_pos hm α hα hp
  | _ => exact hF.elim

end Field

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
