module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApClass
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApFuse
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeS

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem ap_phi6_dvd {q : ℕ} (hq : q % 3 = 2) :
    ∃ k : ℤ, (q : ℤ) ^ 2 + (-1 : ℤ) * q + 1 = 3 * k := by
  obtain ⟨m, hm⟩ : ∃ m, q = 3 * m + 2 := ⟨q / 3, by omega⟩
  refine ⟨3 * (m : ℤ) ^ 2 + 3 * m + 1, ?_⟩
  rw [hm]
  push_cast
  ring

theorem ap_tuple_data {p f : ℕ} [Fact p.Prime] (hq : (p ^ f) % 3 = 2) {L : Type} [Field L]
    [IsAlgClosed L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (p ^ f)) {B : Lˣ} (hB3 : B ^ 3 = 1)
    (hB1 : B ≠ 1) :
    rootDiagUnit TwistTag.D4.tag (threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, B)) ∈
        threeSixTorus L Fr (-1) ∧
      (∃ i, survivingRoots (threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, B)) = trialitySigma i) := by
  set a : Fin TwistTag.D4.tag.rank → Lˣ := threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, B) with ha
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have ha0 : a 0 = 1 := rfl
  have ha1 : a 1 = B := rfl
  have hmem : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus L Fr (-1) := by
    rw [rootDiagUnit_mem_threeSixTorus_iff' Fr hFr hε]
    refine ⟨rfl, by rw [ha0, one_zpow], ?_⟩
    obtain ⟨k, hk⟩ := ap_phi6_dvd hq
    rw [ha1, hk, zpow_mul]
    have : B ^ (3 : ℤ) = 1 := by simpa using hB3
    rw [this, one_zpow]
  refine ⟨hmem, ?_⟩
  have hfix := (rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε a).1 hmem
  have hane : a ≠ 1 := fun h => hB1 (by
    have := congrFun h 1
    rwa [ha1] at this)
  refine survivingRoots_eq_sigma_of_nonempty hε hfix hane ⟨Pi.single 0 1,
    IsRoot.basis (τ := TwistTag.D4.tag) 0, ?_⟩
  rw [CTTorus.rootChar_single]
  exact ha0

theorem ap_exists_tuple {p f : ℕ} [Fact p.Prime] (hq : (p ^ f) % 3 = 2) {L : Type} [Field L]
    [IsAlgClosed L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (p ^ f)) {A : Lˣ} (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    ∃ (B : Lˣ) (W : WeylGroup TwistTag.D4.tag), B ^ 3 = 1 ∧ B ≠ 1 ∧
      weylTuple W (threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, B)) =
        (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) := by
  classical
  set a : Fin TwistTag.D4.tag.rank → Lˣ := threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, A) with ha
  obtain ⟨-, i, hi⟩ := ap_tuple_data hq hFr hA3 hA1
  obtain ⟨W, hW⟩ := exists_weylTuple_longA2 hi
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow]
    have : ((1 : Lˣ), A) ^ 3 = 1 := Prod.ext (one_pow 3) hA3
    rw [this, map_one]
  have hcube : ∀ j, weylTuple W a j ^ 3 = 1 := fun j => by
    change rootChar a (W⁻¹ • Pi.single j 1) ^ 3 = 1
    rw [← rootChar_pow, ha3]
    simp [rootChar]
  obtain ⟨A', hA'3, hA'1, hA'⟩ := d4_tuple_of_kernel_longA2 hcube hW
  rcases cube_root_cases hA3 hA1 hA'3 hA'1 with h | h
  · exact ⟨A, W, hA3, hA1, by rw [← ha, hA', h]⟩
  · refine ⟨A⁻¹, W, by rw [inv_pow, hA3, inv_one], inv_ne_one.2 hA1, ?_⟩
    have e : threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, A⁻¹) = a⁻¹ := by
      rw [ha, ← map_inv]
      simp
    have hinv : weylTuple W a⁻¹ = (weylTuple W a)⁻¹ := by
      funext j
      simp [weylTuple, rootChar_inv_apply]
    rw [e, hinv, hA', h]
    funext j
    fin_cases j
    · exact inv_inv A
    · exact inv_inv A
    · exact inv_one
    · exact inv_inv A

theorem ap_singular {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] {A : Lˣ} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hFg₀ : twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : triEmb K σ L x = g₀ * rootDiagUnit TwistTag.D4.tag
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) * g₀⁻¹) :
    SingularCentralizerData σ (p ^ f) x := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
    omega
  have hq2 : 2 < p ^ f := lt_of_lt_of_le (by omega) (le_trans hp5 (Nat.le_self_pow (by omega) p))
  have hdle : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * (p ^ f : ℕ) + 1 :=
    ⟨(p ^ f) ^ 2 - p ^ f + 1, by push_cast [Nat.cast_sub hdle]; ring⟩
  obtain ⟨-, ⟨g₁, hg₁G, hFg₁⟩, -⟩ := triality_three_six_tori_Sylow_and_root_kernels hp hf K hK σ
    hσ L Fr hFr (Or.inr rfl) hd
  obtain ⟨B, W, hB3, hB1, hW⟩ := ap_exists_tuple hq hFr hA3 hA1
  set a : Fin TwistTag.D4.tag.rank → Lˣ := threeSixTuple ((p ^ f : ℕ) : ℤ) (-1) (1, B) with ha
  obtain ⟨hmem, i, hi⟩ := ap_tuple_data hq hFr hB3 hB1
  have hane : a ≠ 1 := fun h => hB1 (by
    have := congrFun h 1
    exact this)
  have hdord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have : a ^ 3 = 1 := by
        rw [ha, ← map_pow]
        have : ((1 : Lˣ), B) ^ 3 = 1 := Prod.ext (one_pow 3) hB3
        rw [this, map_one]
      rw [rootDiagUnit_pow, this, rootDiagUnit_one]
    · intro h
      apply hane
      have := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (h.trans rootDiagUnit_one.symm)
      exact this
  obtain ⟨x', hx'⟩ := exists_threeSixEmb_eq_conj hp hf hK hσ hFr hg₁G hFg₁ hmem
  have hSCD : SingularCentralizerData σ (p ^ f) x' :=
    singularCentralizerData_threeSix_gen hp hf K hK σ hσ L Fr hFr (Or.inr rfl) hd hg₁G hFg₁
      Nat.prime_three (by norm_num) hp3 hq2 a hmem hdord ⟨i, hi⟩ x' hx'
  set nW := canonicalRep (coxeterSystem TwistTag.D4.tag) L W with hnW
  have hnWG : nW ∈ adjointGroup TwistTag.D4.tag L :=
    canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L W
  have hconj : nW * rootDiagUnit TwistTag.D4.tag a * nW⁻¹ =
      rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) := by
    rw [hnW, canonicalRep_conj_rootDiagUnit, hW]
  have hcG : g₁ * nW⁻¹ * g₀⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem hg₁G (inv_mem hnWG)) (inv_mem hg₀)
  have hc : (g₁ * nW⁻¹ * g₀⁻¹) * triEmb K σ L x * (g₁ * nW⁻¹ * g₀⁻¹)⁻¹ = triEmb K σ L x' := by
    have hx'' : triEmb K σ L x' = g₁ * rootDiagUnit TwistTag.D4.tag a * g₁⁻¹ := hx'
    rw [hx'', hx, ← hconj]
    group
  obtain ⟨y, hy⟩ := ap_fuse_Y hf hK hσ hA3 hA1 hg₀ hFg₀ hx hcG hc
  exact singularCentralizerData_of_conj y (by rw [hy]; exact hSCD)


end CFSG.GH74.GLS.Stage2.Bender.Thm1
