module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUPSL
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04LU

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (isCyclic_unitaryD_quotient exists_ne_one_inf_of_cyclic)
open CFSG.LocalAnalysis.GLTheoremA.YS04LUPSU
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem psu_core {ℓ f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hn3 : n ≠ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hpq : p ∣ ℓ ^ f + 1) :
    LUCore p (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)
      (primeSubfieldPSU h hp hp2 hσ n).range := by
  classical
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hn1 : 1 ≤ n := by omega
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := fun h' => hn3 h'.1
  have hpowq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hpq₀ : p ∣ ℓ ^ (f / p) + 1 := dvd_add_one_of_pow_eq hp hpowq hpq
  have hinj := subfieldPSU_injective h (fixSubfield_unitaryFieldData h hp hp2 hσ)
    (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n hn1
  have hS := isSimpleGroup_primeFormP_one (fixSubfield_unitaryFieldData h hp hp2 hσ) hn hq₀
  have hnc := not_commute_primeFormP_one (fixSubfield_unitaryFieldData h hp hp2 hσ) hn hq₀
  obtain ⟨x₀, hx₀⟩ :=
    exists_orderOf_prime_primeFormP (fixSubfield_unitaryFieldData h hp hp2 hσ) hn hp hpq₀
  haveI := hS
  refine ⟨range_subfieldPSU_le h n (fixSubfield_unitaryFieldData h hp hp2 hσ)
    (fixSubfield_unitaryFieldData_bar h hp hp2 hσ),
    isSimpleGroup_of_mulEquiv (MonoidHom.ofInjective hinj), ?_, ?_,
    fun g hg z hz => psu_normalizes h hn hp hp2 hσ g ((mem_fixSub_iff _ _).1 hg) z hz⟩
  · push Not at hnc
    exact nonabelian_of_mulEquiv (MonoidHom.ofInjective hinj) hnc
  · have hx : orderOf (⟨primeSubfieldPSU h hp hp2 hσ n x₀, MonoidHom.mem_range.2 ⟨x₀, rfl⟩⟩ :
        (primeSubfieldPSU h hp hp2 hσ n).range) = p := by
      rw [Subgroup.orderOf_mk, orderOf_injective _ hinj x₀, hx₀]
    have hdvd := orderOf_dvd_natCard
      (⟨primeSubfieldPSU h hp hp2 hσ n x₀, MonoidHom.mem_range.2 ⟨x₀, rfl⟩⟩ :
        (primeSubfieldPSU h hp hp2 hσ n).range)
    rw [hx] at hdvd
    exact hdvd

theorem psu_LUGood {ℓ f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hn3 : n ≠ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian p D) (hc : Nat.card D = p ^ 2)
    (hinn : D ⊓ (MulAut.conj : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
      MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).range = ⊥) :
    LUGood p D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => hn3 h'.1
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hnot : ¬ D ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro hle
    haveI := isCyclic_unitaryD_quotient h hn hq
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_inf_of_cyclic
      (primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hp D hle hD hc
    have hx' : x ∈ D ⊓ (MulAut.conj : primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) →* MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))).range := hx
    rw [hinn, Subgroup.mem_bot] at hx'
    exact hx1 hx'
  obtain ⟨x, hxD, hxL⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨-, -, -, -, -, -, -, hFker, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  have hx1 : x ≠ 1 := fun h1 => hxL (by rw [h1]; exact one_mem _)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hΦx : primeFormFieldFactor h hC hn hq x ≠ 1 := by
    intro h1
    apply hxL
    rw [← hFker]
    exact (MonoidHom.mem_ker).2 h1
  have hσ : orderOf (primeFormFieldFactor h hC hn hq x) = p := by
    apply orderOf_eq_prime _ hΦx
    rw [← map_pow, hxp, map_one]
  obtain ⟨-, -, -, -, -, M⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq hp hp2 x
      hord _ rfl hσ
  obtain ⟨M, hM⟩ := M
  have hxeq : x = primeFormConjHom h _ M * primeFormFieldHom h hC
      (primeFormFieldFactor h hC hn hq x) * (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM]
    group
  exact LUGood_of_conj (psu_core h hn hn3 hp hp2 hσ hpq) hxD hx1 hxeq

theorem kd26bcLinUni_holds : CFSG.LocalAnalysis.GLTheoremA.KD26bcLinUni := by
  intro S _ _ hs hna n q lin hS p hp hp2 hdiv hsq D hD hc hinn
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  cases lin
  ·
    obtain ⟨m, ℓ, f, F, _, hU, hmn, hℓq, h3, ⟨e0⟩⟩ := exists_psu_of_isLnEps hS
    subst hmn
    subst hℓq
    have hpq : p ∣ ℓ ^ f + 1 := by
      have := hdiv.trans (Nat.gcd_dvd_right _ _)
      simpa [qEps] using this
    have hn3 : 3 ≤ m + 1 := by
      have := Nat.le_of_dvd (Nat.succ_pos m) (hdiv.trans (Nat.gcd_dvd_left _ _))
      omega
    have hn9 : m + 1 ≠ 3 := by
      intro h3'
      have h9 : 9 ≤ p ^ 2 := by nlinarith
      have := Nat.le_of_dvd (by omega) (hsq.trans (Nat.gcd_dvd_left _ _))
      omega
    have hadm : StatedLieAdmissible .PSU (m + 1) ℓ f := by
      refine ⟨hU.prime, hU.one_le, hn3, ?_⟩
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := h3 (by omega)
      omega
    have hm : StatedClassicalModel S .PSU (m + 1) ℓ f :=
      ⟨hadm, F, inferInstance, hU.finite, by rw [hU.card, ← pow_mul, mul_comm], ⟨e0⟩⟩
    obtain ⟨K, _, h, -, hn3', ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.exists_mulEquiv_primeFormP hm
    haveI : Finite K := h.finite
    have hD' : IsElemAbelian p (D.map (MulAut.congr e).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hD _
    have hc' : Nat.card (D.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
    exact LUGood_of_mulEquiv e (psu_LUGood h hn3' hn9 hp hp2 hpq _ hD' hc'
      (map_congr_inf_inner e D hinn))
  ·
    obtain ⟨m, F, _, _, hmn, hFq, ⟨e0⟩⟩ := exists_psl_of_isLnEps hS
    subst hmn
    have hpK : p ∣ Nat.card F - 1 := by
      have := hdiv.trans (Nat.gcd_dvd_right _ _)
      rw [hFq]
      simpa [qEps] using this
    have hn3 : 3 ≤ m + 1 := by
      have := Nat.le_of_dvd (Nat.succ_pos m) (hdiv.trans (Nat.gcd_dvd_left _ _))
      omega
    let e : S ≃* projectiveSL (m + 1) F :=
      e0.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) F)
    have hD' : IsElemAbelian p (D.map (MulAut.congr e).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hD _
    have hc' : Nat.card (D.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
    exact LUGood_of_mulEquiv e (CFSG.LocalAnalysis.GLTheoremA.YS04LUPSL.psl_LUGood hn3 hp hp2 hpK _
      hD' hc' (map_congr_inf_inner e D hinn))

end CFSG.LocalAnalysis.GLTheoremA.YS04LU
