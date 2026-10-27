module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankCrit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionCorner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup Matrix
open scoped MatrixGroups

private theorem exists_not_comm_of_commutator_eq_top {G : Type} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator G = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro y
    exact hcon y x
  rw [hbot] at h
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hxb : x ∈ (⊥ : Subgroup G) := h.symm ▸ mem_top x
  exact hx (mem_bot.1 hxb)

private theorem lt_of_primitive {p ℓ m : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < m → ¬ ℓ ∣ p ^ k - 1) : m < ℓ := by
  by_contra hle
  push Not at hle
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have ha : (p : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h)
  apply hprim (ℓ - 1) (by have := hℓ.two_le; omega) (by have := hℓ.two_le; omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow,
    ZMod.pow_card_sub_one_eq_one ha, Nat.cast_one, sub_self]

private theorem ne_of_primitive {p ℓ m : ℕ} (hℓ : ℓ.Prime) (hm : 0 < m) (hd : ℓ ∣ p ^ m - 1) :
    ℓ ≠ p := by
  rintro rfl
  have h1 : ℓ ∣ ℓ ^ m := dvd_pow_self ℓ (by omega)
  have h2 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

section Field

variable {K : Type} [Field K] [Fintype K]

private theorem psl_lowBlock_injective {p : ℕ} [Fact p.Prime] [CharP K p] :
    Function.Injective ((QuotientGroup.mk' (center SL(4, K))).comp
      (CFSG.RankThree.PartTwo.Census.lowBlockSL 4 K p)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : CFSG.RankThree.PartTwo.Census.lowBlockSL 4 K p a ∈ center SL(4, K) :=
    (QuotientGroup.eq_one_iff _).1 ha
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (0 : Fin 4)
  have h0 : CFSG.RankThree.PartTwo.Census.lowBlockMap 4 K a.toAdd = 0 :=
    CFSG.RankThree.PartTwo.Census.eq_zero_of_one_add_eq_scalar
      (fun i => CFSG.RankThree.PartTwo.Census.lowBlockMap_diag _ i) (0 : Fin 4) hs.symm
  exact Multiplicative.toAdd.injective
    (CFSG.RankThree.PartTwo.Census.lowBlockMap_injective le_rfl (h0.trans (map_zero _).symm))

theorem four_mul_le_pRank_PSL4 {p f : ℕ} [Fact p.Prime] [CharP K p] (hK : Fintype.card K = p ^ f) :
    4 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup PSL(4, K)) := by
  have hp : p.Prime := Fact.out
  have hK' : Nat.card K = p ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have hW : ∀ w : Fin 2 × Fin 2 → K, p • w = 0 := fun w => by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p,
      zero_smul]
  refine CFSG.SectionRank.le_pRank hp.one_lt le_top
    (CFSG.RankThree.PartTwo.Census.isElemAbelian_range_of_nsmul hW
      ((QuotientGroup.mk' (center SL(4, K))).comp
        (CFSG.RankThree.PartTwo.Census.lowBlockSL 4 K p))) ?_
  rw [CFSG.RankThree.PartTwo.Census.card_range_of_injective psl_lowBlock_injective, Nat.card_fun,
    hK', Nat.card_prod, Nat.card_fin, ← pow_mul, mul_comm]

private theorem exists_zsigmondy_PSL_four {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Fintype.card K = p ^ f) (hf : 1 ≤ f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Nat.card PSL(4, K) ∧
      ∀ i : ℕ, 0 < i → i < 4 * f → ¬ ℓ ∣ p ^ i - 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (show 3 ≤ 4 * f by omega)
  have hℓp := ne_of_primitive hℓ (by omega) hℓd
  have hlt := lt_of_primitive hp hℓ hℓp hprim
  refine ⟨ℓ, hℓ, hℓp, ?_, hprim⟩
  have hGL : ℓ ∣ Nat.card (GL (Fin 4) K) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_four]
    have h0 : Fintype.card K ^ 4 - Fintype.card K ^ ((0 : Fin 4) : ℕ) = p ^ (4 * f) - 1 := by
      rw [hK, Fin.val_zero, pow_zero, ← pow_mul, mul_comm]
    rw [h0]
    exact ((hℓd.mul_right _).mul_right _).mul_right _
  have hSL : ℓ ∣ Nat.card SL(4, K) := by
    rw [← Matrix.card_SL_mul_card_units] at hGL
    rcases (Nat.Prime.dvd_mul hℓ).1 hGL with h | h
    · exact h
    · exfalso
      rw [Nat.card_units, Nat.card_eq_fintype_card, hK] at h
      exact hprim f (by omega) (by omega) h
  have hsplit : Nat.card SL(4, K) = Nat.card PSL(4, K) * Nat.card (center SL(4, K)) :=
    card_eq_card_quotient_mul_card_subgroup _
  have hZ : Nat.card (center SL(4, K)) ≤ 4 := by
    rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 4)).toEquiv]
    simpa using card_rootsOfUnity K (Fintype.card (Fin 4))
  rw [hsplit] at hSL
  rcases (Nat.Prime.dvd_mul hℓ).1 hSL with h | h
  · exact h
  · have := Nat.le_of_dvd Nat.card_pos h
    omega

theorem six_le_pRank_of_surj_PSL4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Fintype.card K = p ^ f) (hf : 3 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : X →* PSL(4, K)) (hφ : Function.Surjective φ) : 6 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow hK
  have hK5 : 5 ≤ Fintype.card K := by
    rw [hK]
    calc 5 ≤ 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 3
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 4)
    (by norm_num) (Or.inl (by norm_num))
  haveI := hsimple
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier (k := K) (n := 4) (by norm_num)
      hK5
  have hnc := exists_not_comm_of_commutator_eq_top hperf
  have hM : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier PSL(4, K)) := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    have h1 : p ∣ Fintype.card K - 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ Fintype.card K := by rw [hK]; exact dvd_pow_self p (by omega)
    have h4 := Nat.dvd_sub h3 h1
    rw [Nat.sub_sub_self Fintype.card_pos] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
  have hcen := pRank_cover_of_multiplier hnc hp hM
    ((show 6 ≤ 4 * f by omega).trans (four_mul_le_pRank_PSL4 hK))
  obtain ⟨ℓ, hℓ, hℓp, hℓF, hprim⟩ := exists_zsigmondy_PSL_four (K := K) hp hp2 hK (by omega)
  have hinv := not_dvd_card_GL_of_prime (F := PSL(4, K)) (k := 6 ^ 2 / 4) hp hℓ hℓp hℓF
    (fun i hi1 hi2 => hprim i (by omega) (by norm_num at hi2; omega))
  exact le_pRank_of_surj_crit hnc hp hp2 hcen hinv φ hφ

private theorem cornerMat_injective {k n : ℕ} (hk : k ≤ n) :
    Function.Injective (CFSG.SeitzReduction.LinearPilot.cornerMat (K := K) hk) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  rwa [CFSG.SeitzReduction.LinearPilot.cornerMat_apply,
    CFSG.SeitzReduction.LinearPilot.cornerMat_apply, dif_pos (show _ ∧ _ from ⟨i.2, j.2⟩),
    dif_pos (show _ ∧ _ from ⟨i.2, j.2⟩)] at this

private theorem proj_cornerSL_injective {k n : ℕ} (hk : k ≤ n) (hlt : k < n) :
    Function.Injective ((QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K))).comp
      (CFSG.SeitzReduction.LinearPilot.cornerSL (K := K) hk)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hc : CFSG.SeitzReduction.LinearPilot.cornerSL (K := K) hk A ∈
      center (SpecialLinearGroup (Fin n) K) := (QuotientGroup.eq_one_iff _).1 hA
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hc (⟨n - 1, by omega⟩ : Fin n)
  have hentry : CFSG.SeitzReduction.LinearPilot.cornerMat (K := K) hk (A : Matrix (Fin k) (Fin k) K)
      ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 1 := by
    rw [CFSG.SeitzReduction.LinearPilot.cornerMat_apply, dif_neg (by simp only; omega),
      one_apply_eq]
  rw [CFSG.SeitzReduction.LinearPilot.coe_cornerSL, hentry, map_one] at hs
  have hA1 : (A : Matrix (Fin k) (Fin k) K) = 1 :=
    cornerMat_injective hk (hs.symm.trans (CFSG.SeitzReduction.LinearPilot.cornerMat_one hk).symm)
  exact Subtype.ext hA1

theorem six_le_twoLocalRank_of_PSL_field {p f N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Fintype.card K = p ^ f) (hf : 3 ≤ f) (hN : 5 ≤ N) {X : Type} [Group X] [Finite X]
    (φ : X →* ProjectiveSpecialLinearGroup (Fin N) K) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank p X := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow hK
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.PartOne.Census3.two_ne_zero_of_charP hp2
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hk : 4 ≤ N := by omega
  set ψ := (QuotientGroup.mk' (center (SpecialLinearGroup (Fin N) K))).comp
    (CFSG.SeitzReduction.LinearPilot.cornerSL (K := K) hk) with hψ
  have hinj : Function.Injective ψ := proj_cornerSL_injective hk (by omega)
  obtain ⟨m1, hm1⟩ : ∃ m1 : SL(4, K), (m1 : Matrix (Fin 4) (Fin 4) K) = -1 :=
    ⟨⟨-1, by rw [det_neg, det_one, Fintype.card_fin]; norm_num⟩, rfl⟩
  have hm1sq : m1 * m1 = 1 := Subtype.ext
    (show (m1 : Matrix (Fin 4) (Fin 4) K) * m1 = 1 by rw [hm1, neg_mul_neg, one_mul])
  have hm1ne : m1 ≠ 1 := by
    intro h
    have h' := congrArg (fun A : SL(4, K) => (A : Matrix (Fin 4) (Fin 4) K) 0 0) h
    rw [hm1] at h'
    change (-1 : Matrix (Fin 4) (Fin 4) K) 0 0 = (1 : Matrix (Fin 4) (Fin 4) K) 0 0 at h'
    rw [neg_apply, one_apply_eq] at h'
    exact hne h'
  have hcomm : ∀ A : SL(4, K), m1 * A = A * m1 := fun A => Subtype.ext
    (show (m1 : Matrix (Fin 4) (Fin 4) K) * A = A * m1 by rw [hm1, neg_one_mul, mul_neg_one])
  set z := ψ m1 with hz
  have hz2 : z ^ 2 = 1 := by rw [pow_two, hz, ← map_mul, hm1sq, map_one]
  have hz1 : z ≠ 1 := fun h => hm1ne (hinj (h.trans (map_one ψ).symm))
  refine le_twoLocalRank_of_section hp (J := ψ.range) (U₀ := zpowers z) ?_
    (zpowers_ne_bot.2 hz1) ?_ ?_ φ hφ
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
  · refine le_trans ?_ (centralizer_le_normalizer _)
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    have hc : Commute z (ψ A) := by
      show z * ψ A = ψ A * z
      rw [hz, ← map_mul, ← map_mul, hcomm A]
    exact (hc.zpow_left k).eq
  · intro X' _ _ φ' hφ'
    let e := MonoidHom.ofInjective hinj
    exact six_le_pRank_of_surj_PSL4 hp hp2 hK hf
      ((QuotientGroup.mk' (center SL(4, K))).comp (e.symm.toMonoidHom.comp φ'))
      ((QuotientGroup.mk'_surjective _).comp (e.symm.surjective.comp hφ'))

end Field

theorem six_le_twoLocalRank_A_field {n : ℕ} (hn : 4 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (hq2 : Q.p ≠ 2) (hr : 3 ≤ Q.exponent)
    {X : Type} [Group X] [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.A n Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  letI : Fintype (GaloisField Q.p Q.exponent) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent := by
    rw [Fintype.card_eq_nat_card, GaloisField.card _ _ Q.exponent_pos.ne']
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n Q hv
  exact six_le_twoLocalRank_of_PSL_field Q.prime_p hq2 hK hr (by omega) (e.toMonoidHom.comp φ)
    (e.surjective.comp hφ)

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
