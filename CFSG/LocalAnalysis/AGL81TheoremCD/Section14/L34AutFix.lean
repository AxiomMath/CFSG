module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.PartTwo.KFacts.K72Omega
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

private theorem coprime_seventy_two_of_prime_ge_five {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    Nat.Coprime q 72 := by
  rw [hq.coprime_iff_not_dvd]
  intro h
  have hfactor : 72 = 2 ^ 3 * 3 ^ 2 := by norm_num
  rw [hfactor] at h
  rcases hq.dvd_mul.mp h with h2 | h3
  · have hq2 : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h2
    omega
  · have hq3 : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h3
    omega

theorem eq_one_of_map_eq_of_pow_prime_projectiveSL {k : Type*} [Field k]
    (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {α : MulAut (projectiveSL 3 k)} (hαE : E.map α.toMonoidHom = E) (hαq : α ^ q = 1) :
    α = 1 := by
  set I : Subgroup (MulAut (projectiveSL 3 k)) :=
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range with hI
  have hInnCard : Nat.card I = 20160 := by
    rw [hI, ← Nat.card_congr (MonoidHom.ofInjective (conj_injective hk)).toEquiv,
      card_projectiveSL hk]
  have hInnIndex : I.index = 12 := by
    have h := Subgroup.card_mul_index I
    rw [hInnCard, card_mulAut hk] at h
    omega
  haveI : I.Normal := by
    rw [hI]
    exact CFSG.RankThree.PartTwo.KFacts.range_conj_normal
  have hpow12 : α ^ 12 ∈ I := by
    have h := Subgroup.pow_index_mem I α
    rwa [hInnIndex] at h
  have hpowq : α ^ q ∈ I := by
    rw [hαq]
    exact I.one_mem
  have hcop72 := coprime_seventy_two_of_prime_ge_five hq hq5
  have hcop12 : Nat.Coprime 12 q :=
    (hcop72.coprime_dvd_right (by norm_num : 12 ∣ 72)).symm
  have hαInn : α ∈ I :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem hcop12 hpow12 hpowq
  rw [hI] at hαInn
  obtain ⟨y, rfl⟩ := hαInn
  have hyq : y ^ q = 1 := by
    apply conj_injective hk
    rw [map_pow, map_one]
    exact hαq
  have hyN : y ∈ Subgroup.normalizer (E : Set (projectiveSL 3 k)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hαE
  have hNcard : Nat.card (Subgroup.normalizer (E : Set (projectiveSL 3 k))) = 72 := by
    obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hE
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (eZero k) (MulAut.conj g)]
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_normalizer_eZero hk]
  have hordq : orderOf y ∣ q := orderOf_dvd_of_pow_eq_one hyq
  have hord72 : orderOf y ∣ 72 := by
    have h :=
      Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (E : Set (projectiveSL 3 k))) hyN
    rwa [hNcard] at h
  have hord1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop72 hordq hord72
  have hy1 : y = 1 := orderOf_eq_one_iff.mp hord1
  rw [hy1, map_one]

theorem eq_one_of_map_eq_of_pow_prime {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E : Subgroup X}
    (hE : Nat.card E = 9) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {α : MulAut X}
    (hαE : E.map α.toMonoidHom = E) (hαq : α ^ q = 1) : α = 1 := by
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let ψ : X ≃* projectiveSL 3 (GaloisField 2 2) :=
    e.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  let E' : Subgroup (projectiveSL 3 (GaloisField 2 2)) := E.map ψ.toMonoidHom
  let α' : MulAut (projectiveSL 3 (GaloisField 2 2)) := MulAut.congr ψ α
  have hE' : Nat.card E' = 9 := by
    dsimp [E']
    rw [Subgroup.card_map_of_injective ψ.injective, hE]
  have hα'E' : E'.map α'.toMonoidHom = E' := by
    have h := CFSG.map_mulAut_congr ψ α E
    rw [hαE] at h
    simpa [E', α'] using h
  have hα'q : α' ^ q = 1 := by
    dsimp [α']
    rw [← map_pow, hαq]
    exact map_one (MulAut.congr ψ)
  have hα'1 : α' = 1 :=
    eq_one_of_map_eq_of_pow_prime_projectiveSL hk hE' hq hq5 hα'E' hα'q
  have h : MulAut.congr ψ α = 1 := hα'1
  exact (MulAut.congr ψ).injective (by rw [h, map_one])

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
