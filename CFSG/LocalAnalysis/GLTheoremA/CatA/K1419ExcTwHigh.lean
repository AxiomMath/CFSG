module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcTwBad
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Dickson.Sec6

section Arith

theorem l3u3_three_dvd_two_pow_mul_two_sub_one (e i : ℕ) : 3 ∣ (2 ^ e) ^ (2 * i) - 1 := by
  rw [pow_mul']
  refine l3u3_three_dvd_sq_sub_one fun h => l3u3_not_three_dvd_two_pow (e * i) ?_
  rwa [pow_mul]

theorem l3u3_nine_dvd_two_pow_six_sub_one (e : ℕ) : 9 ∣ (2 ^ e) ^ 6 - 1 := by
  have h : (2 ^ e) ^ 6 = 64 ^ e := by
    rw [← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul, mul_comm]
  rw [h]
  exact l3u3_nine_dvd_sixtyFour_pow_sub_one e

theorem l3u3_twentySeven_dvd_prod_two_pow {n : ℕ} (e : ℕ) (hn : 4 ≤ n) :
    27 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ e) ^ (2 * i) - 1) := by
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 (n - 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    show (27 : ℕ) = 3 * (3 * 3) by norm_num]
  exact mul_dvd_mul (l3u3_three_dvd_two_pow_mul_two_sub_one e 1)
    (mul_dvd_mul (l3u3_three_dvd_two_pow_mul_two_sub_one e 2)
      (l3u3_three_dvd_two_pow_mul_two_sub_one e 3))

theorem l3u3_twentySeven_dvd_ordTwistedD {n : ℕ} (e : ℕ) (hn : 4 ≤ n) :
    27 ∣ ordTwistedD n (2 ^ e) := by
  unfold ordTwistedD
  have h27 := l3u3_twentySeven_dvd_prod_two_pow e hn
  have hgN : Nat.gcd 4 ((2 ^ e) ^ n + 1) ∣ (2 ^ e) ^ (n * (n - 1)) * ((2 ^ e) ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ e) ^ (2 * i) - 1) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _) _
  have hcop : Nat.Coprime 27 (Nat.gcd 4 ((2 ^ e) ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 _) (by norm_num)
  have hN : 27 ∣ (2 ^ e) ^ (n * (n - 1)) * ((2 ^ e) ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ e) ^ (2 * i) - 1) := Dvd.dvd.mul_left h27 _
  obtain ⟨k, hk⟩ := hgN
  have hgpos : 0 < Nat.gcd 4 ((2 ^ e) ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [hk, Nat.mul_div_cancel_left _ hgpos]
  rw [hk] at hN
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hN

theorem l3u3_twentySeven_dvd_ordTwistedE6 (e : ℕ) : 27 ∣ ordTwistedE6 (2 ^ e) := by
  unfold ordTwistedE6
  have hA : 3 ∣ (2 ^ e) ^ 12 - 1 := by simpa using l3u3_three_dvd_two_pow_mul_two_sub_one e 6
  have hC : 3 ∣ (2 ^ e) ^ 8 - 1 := by simpa using l3u3_three_dvd_two_pow_mul_two_sub_one e 4
  have hF : 3 ∣ (2 ^ e) ^ 2 - 1 := by simpa using l3u3_three_dvd_two_pow_mul_two_sub_one e 1
  have hD := l3u3_nine_dvd_two_pow_six_sub_one e
  have h243 : 243 ∣ (2 ^ e) ^ 36 * ((2 ^ e) ^ 12 - 1) * ((2 ^ e) ^ 9 + 1) * ((2 ^ e) ^ 8 - 1) *
      ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 5 + 1) * ((2 ^ e) ^ 2 - 1) := by
    have h := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
      (mul_dvd_mul (one_dvd ((2 ^ e) ^ 36)) hA) (one_dvd ((2 ^ e) ^ 9 + 1))) hC) hD)
      (one_dvd ((2 ^ e) ^ 5 + 1))) hF
    simpa using h
  rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 ((2 ^ e) + 1)) with hg | hg
  · rw [hg, Nat.div_one]
    exact dvd_trans (by norm_num) h243
  · rw [hg]
    obtain ⟨k, hk⟩ := h243
    rw [hk, show 243 * k = 3 * (81 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.dvd.mul_right (by norm_num) k

end Arith

section Models

theorem not_l3u3Order_of_lieModel_pOmegaMinus {G : Type} [Group G] {n e : ℕ}
    (h : LieModel G .POmegaMinus n 2 e) (hO : L3U3Order (Nat.card G)) : False := by
  have hn4 : 4 ≤ n := h.admissible.2.2
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
    (h.statedClassicalModel (by decide))] at hO
  exact hO.not_27_dvd (l3u3_twentySeven_dvd_ordTwistedD e hn4)

end Models

section ModelsE6


theorem not_l3u3Order_of_lieModel_twistedE6 {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .twistedE6 0 2 f) (hO : L3U3Order (Nat.card G)) : False := by
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
    (h.chevalleyExceptionalModel (by decide))] at hO
  exact hO.not_27_dvd (l3u3_twentySeven_dvd_ordTwistedE6 f)

end ModelsE6

section Classes


theorem not_l3u3_twoD_high (hF : L3U3Facts) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ¬ L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  intro hL
  haveI := ssTw_finite_rationalComponent S i
  obtain ⟨m, e, -, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap h1 i h5 hn hout
      (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  rw [ringChar.eq L 2] at hlie
  exact not_l3u3Order_of_lieModel_pOmegaMinus hlie (hF.order _ hL)

theorem not_l3u3_exc_e6class (hF : L3U3Facts) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (h72 : (componentRoots (rootCharHom a) i).ncard = 72)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ¬ L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  intro hL
  haveI := ssTw_finite_rationalComponent S i
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have : (3 : ℕ) = 2 + 1 := rfl
      rw [this, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)) := by
    rw [h6, h72]
    rfl
  rcases hτ with rfl | rfl | rfl
  · exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [h72]; rfl))
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S Nat.prime_three h3L hT hTp i (by omega) hn hout
    rw [ringChar.eq L 2] at hlie
    exact not_l3u3Order_of_lieModel_twistedE6 hlie (hF.order _ hL)
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S Nat.prime_three h3L hT hTp i (by omega) hn hout
    rw [ringChar.eq L 2] at hlie
    exact not_l3u3Order_of_lieModel_twistedE6 hlie (hF.order _ hL)

end Classes

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
