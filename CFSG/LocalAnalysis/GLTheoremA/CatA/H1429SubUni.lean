module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Unitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieAdmissible StatedProj StatedSU)

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_fixModel_primeFormP (h : UnitaryFieldData p f K) (hp3 : p = 3) {n : ℕ} (hn : 3 ≤ n)
    {β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
      MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).range)
    {I : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .PSU n 3 a := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI := h.finite
  haveI := h.charP
  have hf1 := h.one_le
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv _ (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h n).toEquiv
  obtain ⟨σ, g, hσ, hβeq⟩ := exists_conj_primeFormFieldHom_of_outer h hn hp2 hβ hout
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ 3 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 3 ∣ 2 := h2 ▸ dvd_pow_self 3 (by omega)
    omega
  have hZ : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    intro hd
    have h2 : 3 ∣ 3 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))
  obtain ⟨hpf, hcardK0, hbar, hker, hcomap, hinj, hrange, hZ1, hZ0, hsimple, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hq hZ
  have hf' : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hq₀ : ¬(n = 3 ∧ 3 ^ (f / 3) = 2) := by
    rintro ⟨-, h2⟩
    have : 3 ∣ 2 := h2 ▸ dvd_pow_self 3 (by omega)
    omega
  obtain ⟨hsC, hnC, -, -, -⟩ := hsimple hq₀
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set β₀ := primeFormFieldHom h hC σ with hβ₀
  have hCeq : fixSubgroup β₀ = fieldFixedPSU h n σ := Subgroup.ext fun x => Iff.rfl
  have hs : IsSimpleGroup ↥(fixSubgroup β₀) := by
    rw [hCeq]
    exact hsC
  have hnc : ∃ a b : ↥(fixSubgroup β₀), a * b ≠ b * a := by
    rw [hCeq]
    push Not at hnC
    exact hnC
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hdvd : 3 ∣ Nat.card ↥(fixSubgroup β₀) := by
    rw [hCeq, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact dvd_card_primeFormP_one h₀ hn hq₀
  let eC : ↥(fixSubgroup β₀) ≃*
      StatedProj (StatedSU n (3 ^ (f / 3)) (CFSG.LieType.Chevalley.fixSubfield σ)) :=
    ((MulEquiv.subgroupCongr (hCeq.trans hrange.symm)).trans (MonoidHom.ofInjective hinj).symm).trans
      ((CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans (unitaryPSUEquiv h₀ (by omega)))
  have hmodel : StatedClassicalModel ↥(fixSubgroup β₀) .PSU n 3 (f / 3) :=
    ⟨⟨hp, hf', hn, fun heq => hq₀ ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩⟩,
      CFSG.LieType.Chevalley.fixSubfield σ, inferInstance, inferInstance, hcardK0, ⟨eC⟩⟩
  let ψ : T ≃* T := (g⁻¹ : MulAut T)
  have hψ : MulAut.congr ψ β = β₀ := by
    have h1 : MulAut.congr ψ β = g⁻¹ * β * g := by
      ext x
      rfl
    rw [h1, hβeq]
    group
  haveI hnormC := normal_subgroupOf_self (fixSubgroup β₀)
  obtain ⟨e⟩ := exists_equiv_of_conj ψ hψ (J := fixSubgroup β₀) le_rfl (isSolvable_quotient_self _)
    hs hnc hdvd hI
  obtain ⟨hmod, K', fK, finK, hK', ⟨eK'⟩⟩ := hmodel
  exact ⟨f / 3, hf', by omega, hmod, K', fK, finK, hK', ⟨e.trans eK'⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem i1429SubUni_holds : I1429SubLieAt SubIsUni := by
  intro S _ _ hS hnc d hchar ⟨n, q, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  have hq3 : q.p = 3 := by simpa using hchar
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h
    (isPrimeFormGram_one (n := n + 1) (K := K))
  let e' : S ≃* primeFormP h ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hβ' : orderOf (MulAut.congr e' β) = 3 := by rw [MulEquiv.orderOf_eq]; exact hord
  have hout' : MulAut.congr e' β ∉ (MulAut.conj : primeFormP h
      ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) →* _).range := fun hin =>
    hout ((congr_mem_range_conj_iff e' β).1 hin)
  haveI : Finite (primeFormP h ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :=
    Finite.of_equiv S e'.toEquiv
  obtain ⟨hI', ⟨eI⟩⟩ := component_transport e' rfl hI
  obtain ⟨a, ha, hf', hmI⟩ := exists_fixModel_primeFormP h hq3 hn3 hβ' hout' hI'
  have hmI' : StatedClassicalModel (PSimple 3 I) .PSU (n + 1) 3 a :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eI.symm hmI
  obtain ⟨ht, -, -⟩ := finish_classical hmI' hU
  exact absurd ht (by decide)

end CFSG.LocalAnalysis.GLTheoremA

end
