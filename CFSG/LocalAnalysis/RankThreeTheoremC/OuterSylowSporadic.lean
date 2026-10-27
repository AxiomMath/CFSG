module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3K1Spor
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsSmall
import CFSG.Quasithin.Background.A318POutHe
import CFSG.Quasithin.Background.A318POutMore
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.Sporadic.Bridge.Fi24Surj
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.HeSurj
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Bridge.RuSurj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem sylow_normal_of_not_dvd_card {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ∣ Nat.card X) : ∀ S : Sylow p X, (S : Subgroup X).Normal := by
  haveI : Finite X := Nat.finite_of_card_ne_zero fun h0 => h (by rw [h0]; exact dvd_zero p)
  exact sylow_normal_of_not_dvd h

private theorem not_dvd_card_outer_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {p : ℕ} (h : ¬ p ∣ Nat.card (Outer G)) : ¬ p ∣ Nat.card (Outer H) := by
  rwa [← Nat.card_congr (equivalence e).toEquiv]

theorem not_dvd_card_outer_sporadic_M11
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .M11).Group) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.not_dvd_card_outer_M11 (MulEquiv.refl _) hp hp2

theorem not_dvd_card_outer_sporadic_M12
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .M12).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact CFSG.LocalAnalysis.RankThreeTheoremC.not_dvd_card_outer_of_card_dvd_two b
    (by rw [CFSG.ComponentClassification.M12Cover.card_outer]) hp hp2

theorem not_dvd_card_outer_sporadic_J3
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .J3).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux.not_dvd_card_outer_J3
    (b.symm : _ ≃* NativeSporadic.Carrier .J3) hp hp2

theorem not_dvd_card_outer_sporadic_McL
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .McL).Group) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.not_dvd_card_outer_McL (MulEquiv.refl _) hp hp2

theorem not_dvd_card_outer_sporadic_HS
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .HS).Group) := by
  have : Finite (NativeSporadic.Carrier .HS) := inferInstanceAs (Finite NativeSporadic.HS)
  have h : ¬ p ∣ Nat.card (Outer (NativeSporadic.Carrier .HS)) :=
    CFSG.Quasithin.A318P.not_dvd_outer_HS (MulEquiv.refl _) hp hp2
  have hb : Nonempty (NativeSporadic.Carrier .HS ≃* TauCeti.SporadicName.HS.Group) :=
    CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  obtain ⟨b⟩ := hb
  exact not_dvd_card_outer_of_mulEquiv' b h

theorem not_dvd_card_outer_sporadic_Ru
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .Ru).Group) := by
  have : Finite (NativeSporadic.Carrier .Ru) := inferInstanceAs (Finite NativeSporadic.Ru)
  have h : ¬ p ∣ Nat.card (Outer (NativeSporadic.Carrier .Ru)) :=
    CFSG.Quasithin.A318P.not_dvd_outer_Ru (MulEquiv.refl _) hp hp2
  have hb : Nonempty (NativeSporadic.Carrier .Ru ≃* TauCeti.SporadicName.Ru.Group) :=
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  obtain ⟨b⟩ := hb
  exact not_dvd_card_outer_of_mulEquiv' b h

theorem not_dvd_card_outer_sporadic_ONan
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .ONan).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  intro hdvd
  have e : Outer (TauCeti.CFSGIndex.sporadic .ONan).Group ≃* Outer NativeSporadic.ON :=
    equivalence b.symm
  rw [Nat.card_congr e.toEquiv] at hdvd
  rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent p hp hdvd
    with rfl | rfl <;> omega

theorem not_dvd_card_outer_sporadic_Fi24Prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux.not_dvd_card_outer_Fi24
      (b.symm : _ ≃* NativeSporadic.Carrier .Fi24Prime) hp hp2

theorem not_dvd_card_outer_sporadic_He
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .He).Group) := by
  have : Finite (NativeSporadic.Carrier .He) := inferInstanceAs (Finite NativeSporadic.He)
  have h : ¬ p ∣ Nat.card (Outer (NativeSporadic.Carrier .He)) :=
    CFSG.Quasithin.A318P.not_dvd_outer_He (MulEquiv.refl _) hp hp2
  have hb : Nonempty (NativeSporadic.Carrier .He ≃* TauCeti.SporadicName.He.Group) :=
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  obtain ⟨b⟩ := hb
  exact not_dvd_card_outer_of_mulEquiv' b h

theorem not_dvd_card_outer_sporadic_J4
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic .J4).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  intro hdvd
  rcases (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
    (T := (TauCeti.CFSGIndex.sporadic .J4).Group) ⟨b.symm⟩).1 p hp hdvd with rfl | rfl <;> omega

theorem sylow_normal_outer_sporadic_nineThree
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (s : TauCeti.SporadicName)
    (hs : IsNineThreeIndex p (.sporadic s)) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.sporadic s).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.sporadic s).Group)).Normal := by
  have hp : p.Prime := Fact.out
  refine sylow_normal_of_not_dvd_card ?_
  rcases hs with ⟨-, rfl | rfl | rfl⟩ | ⟨-, rfl | rfl | rfl⟩ | ⟨hp7, rfl | rfl | rfl⟩ | ⟨hp11, rfl⟩
  · exact not_dvd_card_outer_sporadic_M11 hp hp2
  · exact not_dvd_card_outer_sporadic_M12 hp hp2
  · exact not_dvd_card_outer_sporadic_J3 hp hp2
  · exact not_dvd_card_outer_sporadic_McL hp hp2
  · exact not_dvd_card_outer_sporadic_HS hp hp2
  · exact not_dvd_card_outer_sporadic_Ru hp hp2
  · exact not_dvd_card_outer_sporadic_ONan hp (by omega)
  · exact not_dvd_card_outer_sporadic_Fi24Prime hp hp2
  · exact not_dvd_card_outer_sporadic_He hp hp2
  · exact not_dvd_card_outer_sporadic_J4 hp (by omega)

theorem sylow_normal_outer_alternating_nineThree {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ)
    (hn : 5 ≤ n) (_h : IsNineThreeIndex p (.alternating n hn)) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.alternating n hn).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.alternating n hn).Group)).Normal :=
  sylow_normal_of_not_dvd_card
    (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p Fact.out hp2)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
