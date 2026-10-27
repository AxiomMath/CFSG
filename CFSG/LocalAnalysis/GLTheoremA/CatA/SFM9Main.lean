module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM9Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Orbit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
open CFSG.LocalAnalysis.GLTheoremA.SFM9Split CFSG.Yardstones.Md0ec50421ce4

theorem sfm9_iso_statedProj {S : Type} [Group S] (hcat : catalogIs S S9.isL3char2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), CharP F 2 ∧ Nat.card F % 3 = 1 ∧
      Nonempty (S ≃* StatedProj (StatedSL 3 F)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨q, rfl, hq2, hq3⟩ := index_A2_of_isL3char2 d hv hi
    have hm := CFSG.Models.lieModel_A 2 q hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ := hcl
    have hFq : Nat.card F = q.card := by rw [hFcard, ← TauCeti.PrimePower.card_def]
    refine ⟨F, hFf, hFfin, ?_, by rw [hFq]; exact hq3, ⟨eF⟩⟩
    exact CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (by rw [hFcard, hq2])

theorem sfm9_cube_root (F : Type) [Field F] [Finite F] (h : Nat.card F % 3 = 1) :
    ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [hcard]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · intro h1
    rw [h1, orderOf_one] at hω
    norm_num at hω

theorem sfm9_O3_eq_bot {K : Type} [Group K] [Finite K] (hZ : Nat.card (Subgroup.center K) = 3)
    (hQ : CFSG.Open.IsQuasisimple K) : GLAPPrimeCore 3 K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3K : 3 ∣ Nat.card K := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.center K)
    rw [hZ] at h
    exact h
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 K)) := CFSG.pPrimeCore_coprime_card
  have hO1 : GLAPPrimeCore 3 K ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3K) (by norm_num)
  have hO2 : GLAPPrimeCore 3 K ≤ Subgroup.center K :=
    le_center_of_normal_of_isQuasisimple hQ (GLAPPrimeCore.normal 3 K) hO1
  have hdvd : Nat.card (GLAPPrimeCore 3 K) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hO2
    rw [hZ] at h
    exact h
  have h1 : Nat.card (GLAPPrimeCore 3 K) = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
  exact Subgroup.eq_bot_of_card_eq _ h1

noncomputable def sfm9_psimple_top_equiv {K : Type} [Group K]
    (hcore : GLAPPrimeCore 3 ↥(⊤ : Subgroup K) = ⊥) :
    PSimple 3 (⊤ : Subgroup K) ≃* (K ⧸ Subgroup.center K) :=
  (pSimpleEquiv hcore).trans
    (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup K)) (Subgroup.center K)
      Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv))

section Final


theorem sfm9_perfect_case {K : Type} [Group K] [Finite K] (hZ : Nat.card (Subgroup.center K) = 3)
    (hcat : catalogIs (K ⧸ Subgroup.center K) S9.isL3char2) (hQ : CFSG.Open.IsQuasisimple K) :
    ∃ y : K, (∃ z : K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧ y ∈ Subgroup.normalizer (U : Set K) := by
  have hO := sfm9_O3_eq_bot hZ hQ
  have hcoreTop : GLAPPrimeCore 3 ↥(⊤ : Subgroup K) = ⊥ :=
    glaPPrimeCore_eq_bot_of_subnormal Nat.prime_three hO (CFSG.Open.IsSubnormal.refl ⊤)
  have hqTop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
  have hcomp : GLAPComponent 3 (⊤ : Subgroup K) ⊤ := glaPComponent_self_p hqTop hcoreTop
  have hcatTop : catalogIs (PSimple 3 (⊤ : Subgroup K)) S9.isL3char2 := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    exact ⟨i, hi, ⟨(sfm9_psimple_top_equiv hcoreTop).trans f⟩⟩
  have hcenTop : Nat.card (Subgroup.center (PQuot 3 (⊤ : Subgroup K))) = 3 := by
    have e1 : PQuot 3 (⊤ : Subgroup K) ≃* ↥(⊤ : Subgroup K) :=
      (QuotientGroup.quotientMulEquivOfEq hcoreTop).trans QuotientGroup.quotientBot
    rw [card_center_congr e1, card_center_congr Subgroup.topEquiv, hZ]
  obtain ⟨E, T, -, hEab, hEcard, -, hTp, hEn, hTn⟩ :=
    sl3TorusAt_holds K ⊤ ⊤ hcomp hcatTop hcenTop
  have hEnot : ¬ E ≤ Subgroup.center K := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [hEcard, hZ] at hc
    norm_num at hc
  obtain ⟨y, hyE, hyZ⟩ : ∃ y ∈ E, y ∉ Subgroup.center K := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hEnot (fun x hx => hcon x hx)
  have hy3 : y ^ 3 = 1 := hEab.2 y hyE
  have hy1 : y ≠ 1 := by
    intro h
    apply hyZ
    rw [h]
    exact Subgroup.one_mem _
  refine ⟨y, ?_, orderOf_eq_prime hy3 hy1, T, ?_, hTp, hEn hyE⟩
  · by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hyZ (Subgroup.mem_center_iff.2 fun g => hcon g)
  · intro hT
    apply hTn
    rw [hT]
    exact bot_le

theorem I114FactA_holds : I114FactA := by
  intro K _ _ hZ hcat
  obtain ⟨F, hFf, hFfin, hCh, hmod, ⟨eF⟩⟩ := sfm9_iso_statedProj hcat
  obtain ⟨ω, hω3, hω1⟩ := sfm9_cube_root F hmod
  by_cases hZK : Subgroup.center K ≤ commutator K
  · have hperf : Group.IsPerfect (K ⧸ Subgroup.center K) := isPerfect_quot_of_iso eF
    have hcomm : commutator K = ⊤ := commutator_eq_top_of_center_le hperf hZK
    haveI hsimpP : IsSimpleGroup (StatedProj (StatedSL 3 F)) :=
      isSimpleGroup_statedProj_statedSL F (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    haveI hsimpK : IsSimpleGroup (K ⧸ Subgroup.center K) := eF.isSimpleGroup
    have hQ : CFSG.Open.IsQuasisimple K := by
      unfold CFSG.Open.IsQuasisimple
      exact ⟨hcomm, hsimpK⟩
    exact sfm9_perfect_case hZ hcat hQ
  · exact split_torus hω3 hω1 eF hZ hZK

end Final

end CFSG.LocalAnalysis.GLTheoremA.I114
