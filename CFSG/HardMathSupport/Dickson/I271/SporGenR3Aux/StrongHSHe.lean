module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoSigStrong
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HSFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeSeven

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Yardstones.Md0ec50421ce4
open Subgroup CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.Sec4 CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem strongHSHe_coprime_five {n : ℕ} (h : n ≤ 2) (hpos : 0 < n) : Nat.Coprime 5 n := by
  interval_cases n <;> norm_num

theorem strongHSHe_coprime_seven {n : ℕ} (h : n ≤ 2) (hpos : 0 < n) : Nat.Coprime 7 n := by
  interval_cases n <;> norm_num

section HS


theorem sporStrong_HS_five (hOut : SporadicOuterLeTwo) : SporStrong .HS 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have eH : NativeSporadic.Carrier .HS ≃* hs100P := hs100Equiv
  exact sporStrong_of_noSig_model hOut Nat.prime_five (by norm_num) (by decide)
    (eH.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => hsFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) b₀ offPair_HS

end HS

section HSRk


theorem hs100P_elemAbelian_twentyfive :
    ∃ E₀ : Subgroup ↥hs100P, IsElemAbelian 5 E₀ ∧ Nat.card E₀ = 5 ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, hAP, hAc, hAe, -, -⟩, -, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  have hcard : Nat.card ↥(hs100FiveA0.subgroupOf hs100P) = 5 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAc]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ⟨hs100FiveA0.subgroupOf hs100P, ⟨?_, fun x hx => ?_⟩, hcard⟩
  · haveI : IsMulCommutative ↥(hs100FiveA0.subgroupOf hs100P) :=
      ⟨⟨(IsPGroup.commGroupOfCardEqPrimeSq hcard).mul_comm⟩⟩
    infer_instance
  · have h1 := Monoid.pow_exponent_eq_one (⟨(x : Equiv.Perm (Fin 100)),
      Subgroup.mem_subgroupOf.1 hx⟩ : ↥hs100FiveA0)
    rw [hAe] at h1
    have h2 : ((x : Equiv.Perm (Fin 100))) ^ 5 = 1 := congrArg Subtype.val h1
    exact Subtype.ext (by simpa using h2)

theorem rkAut_hs100P_five (hOut : SporadicOuterLeTwo) : RkAut 5 ↥hs100P := by
  have hsimple : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have g : ↥hs100P ≃* NativeSporadic.HS := hs100Equiv.symm
  have hfin : Finite NativeSporadic.HS :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  haveI : Finite ↥hs100P := Finite.of_equiv _ g.symm.toEquiv
  have hsimpleP : IsSimpleGroup ↥hs100P :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hsimple g
  have hnabP : ∃ a c : ↥hs100P, a * c ≠ c * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥hs100P := { (inferInstance : Group ↥hs100P) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥hs100P)
    rw [Nat.card_congr g.toEquiv, CFSG.Sporadic.HS.card_HS] at hp
    norm_num at hp
  have hZP : Subgroup.center ↥hs100P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥hs100P) with h | h
    · exact h
    · exfalso
      obtain ⟨a, c, hac⟩ := hnabP
      exact hac (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c) a)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.HS ≃* Spor .HS := b
  have hoP : Nat.card (Outer ↥hs100P) ≤ 2 := hOut _ hsimpleP hnabP .HS ⟨g.trans b₀⟩
  exact rkAut_of_simple Nat.prime_five hZP (strongHSHe_coprime_five hoP Nat.card_pos)
    hs100P_elemAbelian_twentyfive

theorem rkAut_HS_five (hOut : SporadicOuterLeTwo) {T : Type} [Group T]
    (e : T ≃* NativeSporadic.Carrier .HS) : RkAut 5 T :=
  rkAut_of_equiv (hs100Equiv.symm.trans e.symm) (rkAut_hs100P_five hOut)

theorem rkSpor_HS_five (hOut : SporadicOuterLeTwo) {T : Type} [Group T]
    (hZ : Subgroup.center T = ⊥) : RkSpor 5 [.HS] T := by
  rintro (⟨h3, -⟩ | ⟨S, hS, ⟨f⟩⟩)
  · norm_num at h3
  · simp only [List.mem_singleton] at hS
    subst hS
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
    have b₀ : NativeSporadic.Carrier .HS ≃* Spor .HS := b
    let e₁ : T ≃* T ⧸ Subgroup.center T :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact rkAut_HS_five hOut ((e₁.trans f).trans b₀.symm)

end HSRk

section He


theorem sporStrong_He_seven (hOut : SporadicOuterLeTwo) : SporStrong .He 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
  have eH : NativeSporadic.Carrier .He ≃* heP := heEquivP
  exact sporStrong_of_noSig_model hOut (by norm_num) (by norm_num) (by decide)
    (eH.symm.trans b₀)
    (fun R Y hR hR9 hY3 hRY => heSeven_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY) b₀ offPair_He

end He

section HeRk


theorem heP_elemAbelian_fortynine :
    ∃ E₀ : Subgroup ↥heP, IsElemAbelian 7 E₀ ∧ Nat.card E₀ = 7 ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, -, hAP, hAc, hAe, -⟩⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hcard : Nat.card ↥(heSevenA2.subgroupOf heP) = 7 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAc]
    norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨heSevenA2.subgroupOf heP, ⟨?_, fun x hx => ?_⟩, hcard⟩
  · haveI : IsMulCommutative ↥(heSevenA2.subgroupOf heP) :=
      ⟨⟨(IsPGroup.commGroupOfCardEqPrimeSq hcard).mul_comm⟩⟩
    infer_instance
  · have h1 := Monoid.pow_exponent_eq_one (⟨(x : Equiv.Perm (Fin 8330)),
      Subgroup.mem_subgroupOf.1 hx⟩ : ↥heSevenA2)
    rw [hAe] at h1
    have h2 : ((x : Equiv.Perm (Fin 8330))) ^ 7 = 1 := congrArg Subtype.val h1
    exact Subtype.ext (by simpa using h2)

theorem rkAut_heP_seven (hOut : SporadicOuterLeTwo) : RkAut 7 ↥heP := by
  have hsimple : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  have g : ↥heP ≃* NativeSporadic.He := heEquivP.symm
  have hfin : Finite NativeSporadic.He :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.He.card_He]; norm_num)
  haveI : Finite ↥heP := Finite.of_equiv _ g.symm.toEquiv
  have hsimpleP : IsSimpleGroup ↥heP :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.He _ hsimple g
  have hnabP : ∃ a c : ↥heP, a * c ≠ c * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥heP := { (inferInstance : Group ↥heP) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥heP)
    rw [Nat.card_congr g.toEquiv, CFSG.Sporadic.He.card_He] at hp
    norm_num at hp
  have hZP : Subgroup.center ↥heP = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥heP) with h | h
    · exact h
    · exfalso
      obtain ⟨a, c, hac⟩ := hnabP
      exact hac (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c) a)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.He ≃* Spor .He := b
  have hoP : Nat.card (Outer ↥heP) ≤ 2 := hOut _ hsimpleP hnabP .He ⟨g.trans b₀⟩
  exact rkAut_of_simple (by norm_num) hZP (strongHSHe_coprime_seven hoP Nat.card_pos)
    heP_elemAbelian_fortynine

theorem rkAut_He_seven (hOut : SporadicOuterLeTwo) {T : Type} [Group T]
    (e : T ≃* NativeSporadic.Carrier .He) : RkAut 7 T :=
  rkAut_of_equiv (heEquivP.symm.trans e.symm) (rkAut_heP_seven hOut)

theorem rkSpor_He_seven (hOut : SporadicOuterLeTwo) {T : Type} [Group T]
    (hZ : Subgroup.center T = ⊥) : RkSpor 7 [.He] T := by
  rintro (⟨h3, -⟩ | ⟨S, hS, ⟨f⟩⟩)
  · norm_num at h3
  · simp only [List.mem_singleton] at hS
    subst hS
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
    let e₁ : T ≃* T ⧸ Subgroup.center T :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact rkAut_He_seven hOut ((e₁.trans f).trans b₀.symm)

end HeRk

end CFSG.HardMathSupport.Dickson.I271
