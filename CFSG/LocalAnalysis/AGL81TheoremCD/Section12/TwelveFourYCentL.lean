module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactParabolicWCent
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ParabolicGroupForm
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxOrbit
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.AutThreeGroupSmall
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankAlt
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
import CFSG.Quasithin.H13.NQCatT513A7
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L : Subgroup G}

omit [Finite G] in
private theorem commutator_mem_of_mem_closure {S : Set G} (hSM : S ⊆ M)
    (hS : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    ∀ y ∈ Subgroup.closure S, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  have hN : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  intro y hy
  refine (Subgroup.closure_induction
    (p := fun y _ => y ∈ M ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M)
    (fun s hs => ⟨hSM hs, hS s hs⟩) ⟨M.one_mem, fun l _ => by simp⟩ ?_ ?_ hy).2
  · rintro g h - - ⟨hgM, hg⟩ ⟨hhM, hh⟩
    refine ⟨M.mul_mem hgM hhM, fun l hl => ?_⟩
    have e : g * h * l * (g * h)⁻¹ * l⁻¹ =
        g * (h * l * h⁻¹ * l⁻¹) * g⁻¹ * (g * l * g⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp (hN hgM) _).mp (hh l hl)) (hg l hl)
  · rintro g - ⟨hgM, hg⟩
    refine ⟨M.inv_mem hgM, fun l hl => ?_⟩
    have e : g⁻¹ * l * g⁻¹⁻¹ * l⁻¹ = g⁻¹ * (g * l * g⁻¹ * l⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hN (M.inv_mem hgM)) _).mp (inv_mem (hg l hl))

private theorem eq_one_of_alternating_seven {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (e : X ≃* alternatingGroup (Fin 7)) {d k : ℕ}
    (hd : d.Prime) (hd5 : 5 ≤ d) {α : MulAut X} (hα : α ^ (d ^ k) = 1) {t : X}
    (ht : orderOf t = 3) (hαt : α t = t) : α = 1 := by
  have hZ := (quot_center_alternating_of_mulEquiv hq e).2.1
  obtain ⟨l₀, rfl⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.F10.exists_conj_of_odd_orderOf_alt
    (by norm_num) e _ ((hd.odd_of_ne_two (by omega)).pow.of_dvd_nat
      (orderOf_dvd_of_pow_eq_one hα))
  have hl₀ : l₀ ^ (d ^ k) = 1 := by
    have hc : l₀ ^ (d ^ k) ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun φ : MulAut X => φ g)
        (show MulAut.conj (l₀ ^ (d ^ k)) = 1 by rw [map_pow, hα])
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * l₀ ^ d ^ k = (l₀ ^ d ^ k * g * (l₀ ^ d ^ k)⁻¹) * l₀ ^ d ^ k := by rw [h1]
        _ = l₀ ^ d ^ k * g := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.mp hc
  have hc : Commute l₀ t := by
    simp only [MulAut.conj_apply] at hαt
    exact mul_inv_eq_iff_eq_mul.mp hαt
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hd).mp (orderOf_dvd_of_pow_eq_one hl₀)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    rw [hj, map_one]
  exfalso
  have hord : orderOf (l₀ * t) = d ^ j * 3 := by
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [hj, ht]
      exact Nat.Coprime.pow_left j ((Nat.coprime_primes hd Nat.prime_three).mpr (by omega))),
      hj, ht]
  let σ : Equiv.Perm (Fin 7) := (e (l₀ * t) : alternatingGroup (Fin 7))
  have hσ : orderOf σ = d ^ j * 3 := by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  have hdvd : d ∣ 2 ^ 4 * 3 ^ 2 * 5 * 7 := by
    have h1 : orderOf σ ∣ Nat.card (Equiv.Perm (Fin 7)) := orderOf_dvd_natCard σ
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, hσ] at h1
    exact (dvd_pow_self d hj0.ne').trans ((Dvd.intro 3 rfl).trans (h1.trans (by decide)))
  obtain ⟨h15, h21⟩ := CFSG.Quasithin.H13.NQCat.T513P.perm7_not_dvd σ
  rw [hσ] at h15 h21
  rcases (Nat.Prime.dvd_mul hd).mp hdvd with h | h7
  · rcases (Nat.Prime.dvd_mul hd).mp h with h | h5
    · rcases (Nat.Prime.dvd_mul hd).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h)
        omega
    · rw [(Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h5] at h15
      exact h15 (mul_dvd_mul_right (dvd_pow_self 5 hj0.ne') 3)
  · rw [(Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h7] at h21
    exact h21 (mul_dvd_mul_right (dvd_pow_self 7 hj0.ne') 3)

private theorem exists_orderOf_three_fixed {X : Type} [Group X] [Finite X] {K A : Subgroup X}
    (hKA : K ≤ A) (e : ↥A ≃* alternatingGroup (Fin 7)) (hK3 : 3 ∣ Nat.card K) {d k : ℕ}
    (hd : d.Prime) (hd5 : 5 ≤ d) (hKd : ¬ d ∣ Nat.card K) {b : X}
    (hbK : b ∈ normalizer (K : Set X)) (hb : b ^ (d ^ k) = 1) :
    ∃ t ∈ K, orderOf t = 3 ∧ b * t * b⁻¹ = t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT, hbT⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime hd
    Nat.prime_three (isPGroup_zpowers_of_pow_eq_one hb) (Subgroup.zpowers_le.mpr hbK) hKd
  have hT3 : 3 ∣ Nat.card T := by
    rw [hT.card_eq]
    exact dvd_pow_self 3
      (Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' hK3).ne'
  have hT9 : Nat.card T ≤ 9 := by
    obtain ⟨m, hm⟩ := hT.isPGroup.exists_card_eq
    have hdvd : 3 ^ m ∣ 2520 := by
      have h1 := Subgroup.card_dvd_of_le (hT.le.trans hKA)
      rwa [hm, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h1
    have hm2 : m ≤ 2 := by
      by_contra hm2
      exact absurd ((pow_dvd_pow 3 (by omega : 3 ≤ m)).trans hdvd) (by decide)
    rw [hm]
    exact (Nat.pow_le_pow_right (by norm_num) hm2).trans (by norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 hT3
  have hβ : T.normalizerMonoidHom ⟨b, hbT (Subgroup.mem_zpowers b)⟩ = 1 := by
    have hcop : Nat.Coprime (d ^ k) (Nat.card (MulAut ↥T)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hd).mpr
        (not_dvd_card_mulAut_of_five_le hT.isPGroup
          ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans hT9) hd hd5))
    refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_natCard _))
    rw [← map_pow, show (⟨b, hbT (Subgroup.mem_zpowers b)⟩ : ↥(normalizer (T : Set X))) ^ (d ^ k)
      = 1 from Subtype.ext (by simpa using hb), map_one]
  refine ⟨t, hT.le t.2, by rw [Subgroup.orderOf_coe, ht], ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥T => ((φ t : ↥T) : X)) hβ
  simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] using h1

private theorem commutator_mem_of_nineThreeFive (hL : IsTwoPrimeComponent M L)
    (h7 : NineThreeFive M L) (h3 : 3 ∣ Nat.card (L ⊓ H : Subgroup G))
    (h23 : ∀ r : ℕ, r.Prime → r ∣ Nat.card (H ⊓ L : Subgroup G) → r = 2 ∨ r = 3)
    (hd : d.Prime) (hd5 : 5 ≤ d) {b : G} (hbH : b ∈ H) (hbM : b ∈ M)
    (hbL : b ∈ normalizer (L : Set G)) {k : ℕ} (hk : orderOf b = d ^ k) :
    ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨-, ⟨e⟩, -⟩ := h7
  have hHLM : H ⊓ L ≤ M := inf_le_right.trans hL.le
  have hbN := CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.mem_normalizer_barM hbM hbL
  have hbK := CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.mem_normalizer_barM hbM
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hbH, hbL⟩ :
      b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G))
  have hbk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ ^ (d ^ k) = 1 := by
    rw [← map_pow, show (⟨b, hbM⟩ : ↥M) ^ (d ^ k) = 1 from
      Subtype.ext (by simp [← hk]), map_one]
  have hK3 : 3 ∣ Nat.card (barM M (H ⊓ L)) := by
    by_contra hn
    have hc := coprime_three_card_of_barM hHLM
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
    rw [inf_comm] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc h3
  have hKd : ¬ d ∣ Nat.card (barM M (H ⊓ L)) := fun h => by
    rcases h23 d hd (h.trans (card_barM_dvd hHLM)) with h | h <;> omega
  obtain ⟨t, htK, ht3, hbt⟩ :=
    exists_orderOf_three_fixed (barM_mono inf_le_right) e hK3 hd hd5 hKd hbK hbk
  have htL : t ∈ barM M L := barM_mono inf_le_right htK
  have hpow : (⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩, hbN⟩ :
      ↥(normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) ^ (d ^ k) = 1 :=
    Subtype.ext (by simpa using hbk)
  have hα := eq_one_of_alternating_seven hL.component.2.2 e hd hd5
    (α := (barM M L).normalizerMonoidHom ⟨_, hbN⟩) (k := k)
    (by rw [← map_pow, hpow, map_one])
    (t := ⟨t, htL⟩) ((Subgroup.orderOf_coe (⟨t, htL⟩ : ↥(barM M L))).symm.trans ht3)
    (Subtype.ext ((Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _).trans hbt))
  intro l hl
  have hlM : l ∈ M := hL.le hl
  have h2 := congrArg (fun φ : MulAut ↥(barM M L) =>
    ((φ ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)⟩ : ↥(barM M L)) :
        ↥M ⧸ CFSG.pCore 2 ↥M)) hα
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
  apply coe_mem_pCoreOf_two_of_mk_eq_one (⟨b, hbM⟩ * ⟨l, hlM⟩ * ⟨b, hbM⟩⁻¹ * ⟨l, hlM⟩⁻¹)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2, mul_inv_cancel]

omit [Finite G] in
private theorem commutator_mem_pCoreOf_oPPrimeHull (hLM : L ≤ M)
    (h1 : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M)
    {W : Subgroup G} (hW : W ≤ H ⊓ M) (hWL : W ≤ L ⊔ pCoreOf 2 M) {y w : G}
    (hy : y ∈ oPPrimeHull d (H ⊓ M)) (hw : w ∈ W) :
    y * w * y⁻¹ * w⁻¹ ∈ pCoreOf 2 (oPPrimeHull d (H ⊓ M)) := by
  have hN : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hyM : y ∈ M := (oPPrimeHull_le d _ hy).2
  have hYn : H ⊓ M ≤ normalizer (oPPrimeHull d (H ⊓ M) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oPPrimeHull_le d (H ⊓ M))).mp
      (oPPrimeHull_subgroupOf_normal d le_rfl (by simp [Subgroup.subgroupOf_self]))
  have hwmem : w ∈ ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hWL hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hLM.trans hN)] at hwmem
  obtain ⟨l, hl, o, ho, hlo⟩ := Set.mem_mul.mp hwmem
  have hO : y * w * y⁻¹ * w⁻¹ ∈ pCoreOf 2 M := by
    have e : y * w * y⁻¹ * w⁻¹ = (y * l * y⁻¹ * l⁻¹) * (l * (y * o * y⁻¹ * o⁻¹) * l⁻¹) := by
      rw [← hlo]
      group
    rw [e]
    exact mul_mem (h1 y hy l hl) ((mem_normalizer_iff.mp (hN (hLM hl)) _).mp
      (mul_mem ((mem_normalizer_iff.mp (hN hyM) o).mp ho) (inv_mem ho)))
  have hY : y * w * y⁻¹ * w⁻¹ ∈ oPPrimeHull d (H ⊓ M) := by
    have e : y * w * y⁻¹ * w⁻¹ = y * (w * y⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem hy ((mem_normalizer_iff.mp (hYn (hW hw)) _).mp (inv_mem hy))
  exact AscEightSix.inf_twoCore_le_twoCore ((oPPrimeHull_le d _).trans inf_le_right) ⟨hY, hO⟩

theorem twelveFourYCentL_of_twelveCtx (hWc : KFactParabolicWCentSolvable)
    (_h : TwelveCtx G M p Q H) (hd : d ∈ sigmaSet G M) (hD : TwelveThreeData M p H d)
    (hA : TwelveFourStepA M d) (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L)
    (h33 : TwelveFourTenThreeThree M H L) (hYJ : TwelveFourYCentJ M H L d) :
    TwelveFourYCentL M H L d := by
  have hdp : d.Prime := sigmaA_prime d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  have hdo : Odd d := hdp.odd_of_ne_two (by have := hA.2.2; omega)
  have hL' : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hYL : oPPrimeHull d (H ⊓ M) ≤ normalizer (L : Set G) :=
    oPPrimeHull_le_normalizer_of_isTwoPrimeComponent hL' hA.2.1 hB.order_three hdp hA.2.2
      inf_le_right
  have h1 : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
    by_cases hpar : IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (H ⊓ L))
    · have := hD.common.y_simple
      exact commutator_mem_pCoreOf_M_of_isParabolicTwo hWc hdo hL' (oPPrimeHull_le d _)
        (S631.oPPrimeHull_oPPrimeHull d _).symm
        (commutator_eq_self_of_simple_modPrimeComplement_of_not_solvable hdp
          (S631.oPPrimeHull_oPPrimeHull d _) hD.common.y_nonsolvable)
        hYL hYJ hpar.1 hpar.2
    · refine commutator_mem_of_mem_closure (S := {x | x ∈ H ⊓ M ∧ ∃ k : ℕ, orderOf x = d ^ k})
        (fun x hx => hx.1.2) ?_
      rintro b ⟨hbHM, k, hk⟩ l hl
      have hbY : b ∈ oPPrimeHull d (H ⊓ M) := Subgroup.subset_closure ⟨hbHM, k, hk⟩
      rcases h33 b hbHM (hYL hbY) (by rw [hk]; exact hdo.pow) (hYJ b hbY) with hb | hb | h7
      · exact (hL'.inf_twoCore.ge (hb l hl)).2
      · exact absurd ⟨hb.1, hb.2.1⟩ hpar
      · exact commutator_mem_of_nineThreeFive hL' h7 hB.three_dvd (hB.aSeven_primes h7) hdp
          hA.2.2 hbHM.1 hbHM.2 (hYL hbY) hk l hl
  exact ⟨h1, fun W hW hWL y hy w hw =>
    commutator_mem_pCoreOf_oPPrimeHull hL'.le h1 hW hWL hy hw⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
