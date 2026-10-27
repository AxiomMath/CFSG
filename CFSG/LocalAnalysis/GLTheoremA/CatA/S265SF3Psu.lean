module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.LocalAnalysis.GLTheoremA.YS04LUPSU
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem psu_core_of_ne {ℓ f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hpq : p ∣ ℓ ^ f + 1) (hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2)) :
    LUCore p (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)
      (primeSubfieldPSU h hp hp2 hσ n).range := by
  classical
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hn1 : 1 ≤ n := by omega
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

end CFSG.LocalAnalysis.GLTheoremA.S265.SF

end
