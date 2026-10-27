module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmE

section OddStand

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem exists_lift_twin (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : K ∈ Ω) {Lb : Subgroup (G ⧸ N)}
    (hLb : Lb ∈ twinSet (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ L ∈ twinSet Ω K, L.map (QuotientGroup.mk' N) = Lb := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hLbΩ, zb, hzbK, hzbL⟩ := hLb
  obtain ⟨L₀, hL₀, rfl⟩ := hLbΩ
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  obtain ⟨z₀, hz₀⟩ := hΩ.exists_uniqueInvolution hL₀
  have e1 : mk z = zb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz).eq hzbK
  have e2 : mk z₀ = zb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L₀) hz₀).eq hzbL
  obtain ⟨n, hn, hnz⟩ := exists_conj_eq_of_map_eq hN hz.sq hz₀.sq (e1.trans e2.symm)
  refine ⟨conjSub n L₀, ⟨hΩ.conjInvariant n L₀ hL₀, z, hz, ?_⟩, ?_⟩
  · have := hz₀.conj n
    rwa [hnz] at this
  · rw [AscQuot.map_conjSub, show mk n = 1 from (QuotientGroup.eq_one_iff _).mpr hn,
      conjSub_one]

theorem map_ne_of_twin (hΩ : HypOmegaGen Ω)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := by
  intro heq
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
  obtain ⟨V, hV, hVsyl, -⟩ :=
    exists_mem_RSet_ge hK (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hV8 := hΩ.eight_le_of_mem_RSet hV
  have hVN : V ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hVsyl.2.1 hVsyl.1 (odd_natCard_inf hN K)
  have hsub : ∀ y ∈ V.map mk, y = 1 ∨ y = mk z := by
    rintro _ ⟨x, hxV, rfl⟩
    have hxbar : mk x ∈ K'.map mk := by
      rw [heq]
      exact Subgroup.mem_map_of_mem _ (hVsyl.1 hxV)
    obtain ⟨y, hy, hyx⟩ := hxbar
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      hVsyl.2.1.to_le (Subgroup.zpowers_le.mpr hxV)
    rcases Q3T6.eq_one_or_eq_of_map_eq_of_twin_gen hΩ hN hK hK'Ω (Ne.symm hne) hz hz' hy
      (hVsyl.1 hxV) hx2 hyx with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1]
  have hcard2 : Nat.card ↥(V.map mk) ≤ 2 := natCard_subgroup_le_two_of_subset hsub
  have hcardV : Nat.card ↥(V.map mk) = Nat.card V :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
  omega

theorem exists_W_of_hypOmega {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) :
    ∃ W ∈ WSet Ω, W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W := by
  obtain ⟨η, hη, hinv⟩ := (Q3T8.Asc77.l6_9_proved G Ω hΩ S).1
  have hS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU => (hη.1 hU).2
  have hle : ∀ t ∈ (S : Subgroup G), conjSub t (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
    intro t ht
    rw [conjSub_iSup]
    refine iSup_le fun U => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSub t U) (hinv t ht U hU) le_rfl
  refine ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le hS, fun s hs => ?_⟩
  apply le_antisymm (hle s hs)
  have := conjSub_mono (n := s) (hle s⁻¹ ((S : Subgroup G).inv_mem hs))
  rwa [conjSub_conjSub_inv] at this

end OddStand

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
