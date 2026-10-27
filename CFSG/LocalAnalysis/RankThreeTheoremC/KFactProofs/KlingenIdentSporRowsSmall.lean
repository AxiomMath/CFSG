module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverWeakGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import Certificates.Certificate9508

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.AGLEmbedding.SporCubic

section J3


theorem false_of_J3 {Y : Type} [Group Y] [Finite Y] [Fact (Nat.Prime 3)] {Rb : Sylow 3 Y}
    {Y₀ : Subgroup Y} (hred : ReducedNongeneration 3 Y Rb Y₀) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    (hkl : HasKlingenData 3 Rb Y₀) [Finite (Outer K)] (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hZ : Subgroup.center K = ⊥) (eK : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) : False := by
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hC := KlingenIdentLieAux.centralizer_eq_bot hred hKn hcent hZ
  have hRK : (Rb : Subgroup Y) ≤ K := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Rb.isPGroup') ⟨x, hx⟩
    have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : (Rb : Subgroup Y))
    rw [hn] at h1
    have := mem_sup_centralizer_of_pow Nat.prime_three hOut (n := n) (congrArg Subtype.val h1)
    rwa [hC, sup_bot_eq] at this
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hTR : (T₀ : Subgroup K).map K.subtype = (Rb : Subgroup Y) := by
    rw [hT₀]
    exact inf_eq_left.mpr hRK
  obtain ⟨hZel, hZcard⟩ := (kFactJ3Sylow K ⟨eK⟩ T₀).center_elem
  have hcard := card_le_of_klingen hred hkl
    (W := (CFSG.Quasithin.centerOf (T₀ : Subgroup K)).map K.subtype) ?_ ?_ ?_
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hZcard] at hcard
    omega
  · rintro _ ⟨k, hk, rfl⟩
    exact hTR ▸ Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_inf.mp hk).1
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ (T₀ : Subgroup K).map K.subtype := by
      rw [hTR]
      exact hr
    obtain ⟨t, ht, rfl⟩ := hr'
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 t ht)
  · rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (hZel.2 k hk)

end J3

section J3Cover


theorem weakCore_eq_top_J3_cover {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .J3) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (T : Sylow 3 K) : GLBWeakCore 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  have : Finite (NativeSporadic.Carrier .J3) := Finite.of_equiv _ e.toEquiv
  exact j3CoverWeakGenThree K π hπ hker ⟨hK.1⟩ hZ hZp hZc T

end J3Cover

section M22


theorem rankData_M22_three [Finite (NativeSporadic.Carrier .M22)] [Fact (Nat.Prime 3)] :
    RankData (NativeSporadic.Carrier .M22) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  exact Or.inl (by rw [hc]; norm_num)

end M22

section Fi24


theorem rankData_Fi24_seven [Finite (NativeSporadic.Carrier .Fi24Prime)] [Fact (Nat.Prime 7)] :
    RankData (NativeSporadic.Carrier .Fi24Prime) 7 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 781).cubic_of_check fi24Sylow7HData Certificates.certificate9508
  have h4 : ¬ 7 ^ 4 ∣ Nat.card NativeSporadic.Fi24prime := by
    rw [CFSG.Sporadic.Fi24.card_Fi24prime]
    norm_num
  exact Or.inr ⟨h4, CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Fact.out hx hy hz hQ,
    kernelTrivialAt_of_cubic hx hy hz hzx hzy hQ h4 hhx hhy hhz (by decide +revert)⟩

end Fi24

section OuterJ3


theorem not_dvd_card_outer_J3
    {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .J3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_card_outer_of_mulEquiv e.symm
    (card_outer_dvd_two_of_le_two (G := NativeSporadic.J3)
      (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
        CFSG.Sporadic.Schreier.j3PermEquiv)) hp hp2

end OuterJ3

section OuterM22


theorem not_dvd_card_outer_M22
    {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .M22) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_card_outer_of_mulEquiv e.symm
    (card_outer_dvd_two_of_eq (G := NativeSporadic.M22)
      (.inr CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1)) hp hp2

end OuterM22

section OuterFi24


theorem not_dvd_card_outer_Fi24
    {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .Fi24Prime) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (Outer X) :=
  not_dvd_card_outer_of_mulEquiv e.symm
    (card_outer_dvd_two_of_eq (G := NativeSporadic.Fi24prime)
      (.inr CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime)) hp hp2

end OuterFi24

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
