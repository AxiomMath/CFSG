module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowDataB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal
public import CFSG.Sporadic.NativeFinite

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem three_le_pRank_of_szEight {X K : Type} [Group X] [Group K] [Finite X] [Finite K]
    (e : X ≃* K)
    (hE : ∃ E : Subgroup K, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      Nat.card E = 8) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨E, hsq, hc, hcard⟩ := hE
  refine three_le_pRank_of_elemAbelian (E.map e.symm.toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    show e.symm y * e.symm y = 1
    rw [← map_mul, hsq y hy, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    show e.symm y * e.symm z = e.symm z * e.symm y
    rw [← map_mul, ← map_mul, hc y hy z hz]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcard.ge

theorem eq_one_of_odd_of_dvd_ru {c : ℕ} (hodd : Odd c) (h : 29120 * c ∣ 116480) : c = 1 := by
  have h' : 29120 * c ∣ 29120 * 4 := by
    have : (29120 : ℕ) * 4 = 116480 := by norm_num
    rw [this]
    exact h
  have h4 : c ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  have hle : c ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  obtain ⟨k, hk⟩ := hodd
  interval_cases c <;> omega

theorem center_eq_bot_of_simple_nonabelian {X : Type} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ center X := h ▸ mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem ru_finite : Finite (Carrier .Ru) :=
  CFSG.Sporadic.finite_carrier_of_ne_M .Ru (by decide)

theorem ru_top_sporadic : IsSporadic ↥(⊤ : Subgroup (Carrier .Ru)) .Ru := ⟨Subgroup.topEquiv⟩

theorem ruPinned_of_isK {X : Type} [Group X] (h : IsKPinned .Ru (fun n => n = 29120) X) :
    ∃ (u : Carrier .Ru) (K : Subgroup (Carrier .Ru)),
      RuPair (Carrier .Ru) ⊤ K u ∧ Nonempty (X ≃* ↥K) := h

theorem ruPinned_simple (hf : RuLocalFacts) {u : Carrier .Ru} {K : Subgroup (Carrier .Ru)}
    (hQ : RuPair (Carrier .Ru) ⊤ K u) : IsSimpleGroup ↥K :=
  hf.simple (Carrier .Ru) ⊤ K u ru_top_sporadic hQ

section Pinned

theorem ru_isSimpleGroup : IsSimpleGroup (Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru

theorem card_carrier_ru : Nat.card (Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru

end Pinned

section Row

theorem ruPinned_quasisimple (hf : RuLocalFacts) {u : Carrier .Ru} {K : Subgroup (Carrier .Ru)}
    (hQ : RuPair (Carrier .Ru) ⊤ K u) : CFSG.IsQuasisimple ↥K := by
  have := ru_finite
  exact ruPair_isQuasisimple hf ru_top_sporadic hQ

section Opaque

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem ruK_not_exc (hf : RuLocalFacts) {X : Type} [Group X]
    (h : IsKPinned .Ru (fun n => n = 29120) X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f := by
  obtain ⟨u, K, hQ, ⟨e⟩⟩ := ruPinned_of_isK h
  have := ru_finite
  have hs := ruPinned_simple hf hQ
  have hna : ∃ a b : ↥K, a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hQ.2.2.2.2]; norm_num)
  have hZ : center ↥K = ⊥ := center_eq_bot_of_simple_nonabelian hna
  have hc1 : Nat.card ↥(center ↥K) = 1 := by
    rw [hZ]
    exact Subgroup.card_bot
  have hKq : Nat.card (↥K ⧸ center ↥K) = 29120 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K)
    rw [hc1, hQ.2.2.2.2] at h1
    omega
  refine kNotExc_of_card (N := 29120) (c := 38) ?_ (by norm_num) (by norm_num) (by norm_num)
  rw [Nat.card_congr (quotientCenterEquiv' e).toEquiv]
  exact hKq

theorem ruK_ne_L {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Ru] X)
    (hY : IsKPinned .Ru (fun n => n = 29120) (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  obtain ⟨s', hs', hq, hodd, hsp⟩ := hX
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨f⟩ := hsp
  obtain ⟨u, K, hQ, ⟨g⟩⟩ := ruPinned_of_isK hY
  have := ru_finite
  have : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have : Finite (Y ⧸ CFSG.oddCore Y) := Finite.of_equiv _ g.symm.toEquiv
  refine kNeL_of_card (cardS := 145926144000) (cardK := 29120) ?_ (by decide) ?_ (by norm_num)
  · rw [Nat.card_congr f.toEquiv]
    exact card_carrier_ru
  · rw [Nat.card_congr g.toEquiv]
    exact hQ.2.2.2.2

theorem ru_fit (hmult : OddMultTrivial .Ru) {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hcov : OddCover .Ru L) (hKL : K ≤ L)
    (hK : IsKPinned .Ru (fun n => n = 29120) (↥K ⧸ CFSG.oddCore ↥K))
    (hstd : SolStd (K.subgroupOf L)) : ∃ u : H, RuPair H L K u := by
  have hL : IsSporadic ↥L .Ru := hcov.isSporadic_of_mult hmult
  obtain ⟨t, ht2, hcomp⟩ := hstd.exists_involution
  have hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k := fun k hk => by
    have h1 : (⟨k, hKL hk⟩ : ↥L) ∈ centralizer ({t} : Set ↥L) := hcomp.1 (mem_subgroupOf.2 hk)
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1)
  have hKle : K ≤ L ⊓ centralizer ({(t : H)} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKt k hk)⟩
  have hdvd : Nat.card K ∣ Nat.card ↥(L ⊓ centralizer ({(t : H)} : Set H)) :=
    Subgroup.card_dvd_of_le hKle
  have hcc := (ruFacts_of_isSporadic hL).card_centralizer t ht2
  rw [card_centralizer_subtype L t] at hcc
  obtain ⟨u', K', hQ', ⟨f⟩⟩ := ruPinned_of_isK hK
  have hq : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 29120 := by
    rw [Nat.card_congr f.toEquiv]
    exact hQ'.2.2.2.2
  have hKcard : Nat.card ↥K = 29120 * Nat.card ↥(CFSG.oddCore ↥K) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K)
    rw [hq] at h
    exact h
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥K)) := odd_card_oddCore
  have hc1 : Nat.card ↥(CFSG.oddCore ↥K) = 1 := by
    rcases hcc with h | h
    · exfalso
      rw [h, hKcard] at hdvd
      have h29 : 29120 ∣ 245760 := (dvd_mul_right 29120 _).trans hdvd
      omega
    · rw [h, hKcard] at hdvd
      exact eq_one_of_odd_of_dvd_ru hodd hdvd
  refine ⟨(t : H), t.2, ?_, hKL, hKt, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact ht2
  · show Nat.card ↥K = 29120
    omega

theorem outTwoCovers_ru (hmult : OddMultTrivial .Ru) : OutTwoCovers [.Ru] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  exact fun α _ => Or.inl (CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic
    (oddCover_isSporadic ru_finite hmult hM) α)

end Opaque

end Row

section Cover

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

end Cover

end CFSG.EvenSporadicStandard.Induction
