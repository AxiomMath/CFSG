module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.GLTheoremA.S3.KD76cHolds
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Pump
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieAdmissible StatedProj StatedSU)
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv)

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem dvd_card_primeFormP_one (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    p ∣ Nat.card (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  have hp := h.prime
  rw [← Nat.card_congr (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h n).toEquiv]
  have hmodel : StatedClassicalModel (unitaryPSU h n) CFSG.Assembly.LowTwoRank.StatedLieTag.PSU n
      p f := by
    refine ⟨⟨hp, h.one_le, hn, fun heq => hq ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩⟩, K,
      inferInstance, inferInstance, ?_, ⟨unitaryPSUEquiv h (by omega)⟩⟩
    rw [h.card, ← pow_mul, mul_comm]
  have hform := (unitary_model_outer_two_part_bound _ n p f hmodel).1
  have hfpos : f ≠ 0 := by have := h.one_le; omega
  have hexp : n * (n - 1) / 2 ≠ 0 := by
    have : 6 ≤ n * (n - 1) := le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul hn (by omega))
    omega
  have hpd : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ j - (-1) ^ j) :=
    Dvd.dvd.mul_right (dvd_pow (Int.natCast_dvd_natCast.mpr (dvd_pow_self p hfpos)) hexp) _
  rw [← hform] at hpd
  have hpd' : p ∣ Nat.card (unitaryPSU h n) * Nat.gcd n (p ^ f + 1) := by exact_mod_cast hpd
  rcases hp.dvd_mul.mp hpd' with h1 | h1
  · exact h1
  · exfalso
    have h2 : p ∣ p ^ f + 1 := h1.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ p ^ f := dvd_pow_self p hfpos
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))

theorem isChevSimple_of_statedPSU {G : Type} [Group G] {n : ℕ} (hadm : StatedLieAdmissible
    CFSG.Assembly.LowTwoRank.StatedLieTag.PSU n p f) {K' : Type} [Field K'] [Finite K']
    (hK : Nat.card K' = (p ^ f) ^ 2) (e : G ≃* StatedProj (StatedSU n (p ^ f) K')) :
    IsChevSimple p G := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid n p f hadm
  haveI : Fact p.Prime := ⟨hp⟩
  let q : TauCeti.PrimePower := ⟨p, f, hp, by omega⟩
  let L := GaloisField p (2 * f)
  let _ : Fintype K' := Fintype.ofFinite K'
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K' = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K' ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ n (p ^ f))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv' : (TauCeti.LieTypeIndex.twistedA m q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv'
  exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨_, hv'⟩, TauCeti.LieTypeIndex.characteristic_twistedA m q,
    ⟨(e.trans e1).trans eT.symm⟩⟩

theorem outerCentData_primeFormFieldHom {n : ℕ} (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hout : primeFormFieldHom h
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ ∉
      innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    OuterCentData p (primeFormFieldHom h
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.finite
  haveI := h.charP
  have hp := h.prime
  have hf1 := h.one_le
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    intro hd
    have h2 : p ∣ p ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))
  obtain ⟨hpf, hcardK0, hbar, hker, hcomap, hinj, hrange, hZ1, hZ0, hsimple, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hq hZ
  have hf' : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hq₀ : ¬(n = 3 ∧ p ^ (f / p) = 2) := by
    rintro ⟨-, h2⟩
    have : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  obtain ⟨hsC, hnC, hfix, hzp, hcard⟩ := hsimple hq₀
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set β := primeFormFieldHom h hC σ with hβ
  have hCeq : fixSubgroup β = fieldFixedPSU h n σ := Subgroup.ext fun x => Iff.rfl
  have hord : orderOf β = p := by
    rw [← Nat.card_zpowers]
    exact hcard
  have hs : IsSimpleGroup ↥(fixSubgroup β) := by
    rw [hCeq]
    exact hsC
  have hnc : ∃ a b : ↥(fixSubgroup β), a * b ≠ b * a := by
    rw [hCeq]
    push Not at hnC
    exact hnC
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hdvd : p ∣ Nat.card ↥(fixSubgroup β) := by
    rw [hCeq, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact dvd_card_primeFormP_one h₀ hn hq₀
  have hchev : IsChevSimple p ↥(fixSubgroup β) := by
    rw [hCeq, ← hrange]
    have hadm : StatedLieAdmissible CFSG.Assembly.LowTwoRank.StatedLieTag.PSU n p (f / p) :=
      ⟨hp, hf', hn, fun heq => hq₀ ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩⟩
    refine isChevSimple_of_mulEquiv (MonoidHom.ofInjective hinj)
      (isChevSimple_of_statedPSU hadm (K' := CFSG.LieType.Chevalley.fixSubfield σ) hcardK0 ?_)
    exact (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans
      (unitaryPSUEquiv h₀ (by omega))
  have hZc : Subgroup.center T = ⊥ := by
    haveI := isSimpleGroup_primeFormP_one h hn hq
    exact b3Lie_center_eq_bot (by
      by_contra hcon
      push Not at hcon
      exact not_commute_primeFormP_one h hn hq hcon)
  refine OuterCentData.ofSimpleNormal hp (SimpleNormalData.ofSimple hs hnc hchev hdvd) ?_ ?_
  · intro _ w hw _ hfixw
    have hmem : w ∈ fixingSubgroup (MulAut T) (fieldFixedPSU h n σ : Set T) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact hfixw y (by rw [hCeq]; exact hy)
    rw [hfix, hzp] at hmem
    have h1 : orderOf w ∣ orderOf β := orderOf_dvd_of_mem_zpowers hmem
    rw [hord] at h1
    have h2 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hw.symm h1
    rw [orderOf_eq_one_iff.1 h2]
    exact (innerAut T).one_mem
  · intro hp3 _ β' hβ' hcomm _
    subst hp3
    exact exists_inner_on_fixSubgroup_of_pump hp hZc hord hout
      (fun D hexp hc => CFSG.LocalAnalysis.GLTheoremA.kd76c_exists_inner_primeFormP hp h hn hq D
        hexp hc) hβ' hcomm

end Unitary

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
