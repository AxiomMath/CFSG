module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf28O2Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf21Vertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Generic

theorem oddCoreIn_le_oddCoreIn_of_le {G : Type} [Group G] [Finite G] {z u : G}
    (hz2 : IsPGroup 2 (Subgroup.zpowers z)) (hzu : z * u = u * z)
    (hNH : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.centralizer ({u} : Set G))
    (hB : InO2C z u) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  set N : Subgroup G := oddCoreIn (Subgroup.centralizer ({z} : Set G)) with hN
  have hNH : N ≤ H := hNH
  have hzH : z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hzu
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  obtain ⟨P, hPH, hPn, hP2, hzP⟩ := hB
  set O : Subgroup ↥H := classicalInvolutionOddCore ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hOnd : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hOq : classicalInvolutionOddCore (↥H ⧸ O) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  set Pb : Subgroup (↥H ⧸ O) := (P.subgroupOf H).map π with hPb
  have hPbn : Pb.Normal := hPn.map π (QuotientGroup.mk'_surjective O)
  have hPb2 : IsPGroup 2 Pb :=
    (hP2.comap_subtype).of_surjective (π.subgroupMap (P.subgroupOf H)) (π.subgroupMap_surjective _)
  have hzPb : π zH ∈ Pb := ⟨zH, Subgroup.mem_subgroupOf.mpr hzP, rfl⟩
  have h35 := oddCoreIn_centralizer_eq_bot_of_mem_normal hOq hPbn hPb2 hzPb
  have hQ : IsPGroup 2 (Subgroup.zpowers zH) := by
    refine hz2.of_injective
      ((H.subtype.comp (Subgroup.zpowers zH).subtype).codRestrict (Subgroup.zpowers z) ?_) ?_
    · rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hcent := GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 2) (N := O) hOnd hQ
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hcent
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  set Nb : Subgroup (↥H ⧸ O) := N'.map π with hNb
  have hNbC : Nb ≤ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) := by
    rintro _ ⟨n', hn', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hc : (n' : G) * z = z * n' := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hn)
    have : n' * zH = zH * n' := Subtype.ext hc
    rw [← map_mul, ← map_mul, this]
  have hfwd : ∀ g ∈ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)), ∀ x ∈ Nb, g * x * g⁻¹ ∈ Nb := by
    intro g hg x hx
    rw [hcent] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨n', hn', rfl⟩ := hx
    have hhC : (h : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have h1 : (h : G) * n' * (h : G)⁻¹ ∈ N := conj_mem_oddCoreIn hhC hn
    refine ⟨h * n' * h⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hNbN : Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) ≤ Subgroup.normalizer (Nb : Set (↥H ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd g hg x hx, fun hx => ?_⟩
    have := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this
  have hN'odd : Odd (Nat.card N') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact odd_card_oddCoreIn _
  have hNbodd : Odd (Nat.card Nb) :=
    Odd.of_dvd_nat hN'odd (CFSG.card_dvd_of_surjective (π.subgroupMap N') (π.subgroupMap_surjective _))
  have hNbO := le_oddCoreIn_of_normalizes hNbC hNbN hNbodd
  rw [h35, le_bot_iff] at hNbO
  intro n hn
  have hn' : (⟨n, hNH hn⟩ : ↥H) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
  have h1 : π ⟨n, hNH hn⟩ ∈ Nb := ⟨_, hn', rfl⟩
  rw [hNbO, Subgroup.mem_bot] at h1
  exact ⟨⟨n, hNH hn⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

end Generic

section Odd

variable {n : ℕ}

section PartA

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

set_option maxHeartbeats 1600000 in
theorem movedOddFree_u_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (hP : PerpHypS n Y R S t)
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (h43 : K₄ ≠ K₃) (htc : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)) :
    MovedOddFreeAt (u₁ * u₂) t htc := by
  have hC := CoreData.of_S hP.core
  have hBelow : CIT3Below (Nat.card Y) := hC.card ▸ hC.below
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  have hΩ := d.hyp
  have hcc : (u₁ * u₂) * (u₁ * u₂) = 1 := d.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet d.hz hK₄
  have hmem := tq_of_hyp22G d
  have hmem4 : K₄ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    refine ⟨hK₄.1, ?_⟩
    have t14 : u₁ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.mem hK₄.1 h41.symm d.hz hz4 d.hu₁.1
    have t24 : u₂ ∈ trivialOnQuot K₄ :=
      A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
    exact (trivialOnQuot K₄).mul_mem t14 t24
  have hu₂c : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * u₂ = (u₂ * u₁) * u₂ := by rw [d.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hcm : ∀ {J : Subgroup Y}, u₂ ∈ trivialOnQuot J → u₂ ∈ centralizerModOdd ⊤ J := fun h =>
    ⟨Subgroup.mem_top _, h.1, Asc77.mem_normalizer_oddCore_of_mem_normalizer h.1,
      fun l hl => h.2 l hl⟩
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' d.hzK₃ d.hu₂.1
  have t24 : u₂ ∈ trivialOnQuot K₄ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 hK₄.1 h42.symm d.hzK' hz4 d.hu₂.1
  have out1 := v3_out_gen hSp hD4 h4 hP hcc d.mul_ne_one d.hK₃.1 hK₄.1 d.hzK₃ hz4 h43 hmem.2 hmem4.2 htc
  have out2 := v3_out_gen hSp hD4 h4 hP hcc d.mul_ne_one hK₄.1 d.hK₃.1 hz4 d.hzK₃ (Ne.symm h43)
    hmem4.2 hmem.2 htc
  have hcq : TL4.ClassicalOrQuiet (u₁ * u₂) t htc → MovedOddFreeAt (u₁ * u₂) t htc := fun h =>
    movedOddFreeAt_of_classicalOrQuiet hBelow hZ d.mul_ne_one h
  rcases out1 with q | l3 | ⟨e3, m3⟩
  · exact hcq (Or.inr q)
  · rcases out2 with q | l4 | ⟨e4, m4⟩
    · exact hcq (Or.inr q)
    · obtain ⟨M, M', hM, hM', hne, hcomm, hcM, hcM', hmM, -⟩ :=
        liftPair_of_twinsY hP hΩ hc2 hcc d.mul_ne_one hmem hmem4 h43 d.hzK₃ hz4 htc l3 l4 hu₂c
          (hcm t23) (hcm t24)
      exact hcq (Or.inl ⟨M, hM⟩)
    · exact m4
  · exact m3

end PartA

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
