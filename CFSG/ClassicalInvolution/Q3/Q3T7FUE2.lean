module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE1
public import CFSG.ClassicalInvolution.Asc77.AscE187EndA

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]
section MinCexConj
variable {Ω : Set (Subgroup G)} [Finite G]

theorem EStand.conj {K R W : Subgroup G} {S : Sylow 2 G} (h : EStand MT Ω K S R W) (g : G) :
    EStand MT Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) where
  hyp := h.hyp
  mem := h.hyp.conjInvariant g K h.mem
  aEmpty := aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  twin := E187C.twin_conj h.hyp.conjInvariant h.twin g
  hR := E187C.hR_conj h.hyp.conjInvariant h.hR g
  hW := E187C.hW_conj h.hyp.conjInvariant h.hW g

theorem MinCex.conj {K R W H : Subgroup G} {S : Sylow 2 G} (c : MinCex MT Ω K S R W H)
    (g : G) : MinCex MT Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W)
      (conjSub g H) where
  stand := c.stand.conj g
  hyp := c.hyp.conj c.stand.hyp.conjInvariant g
  proper := E187C.conjSub_ne_top c.proper g

end MinCexConj
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Finite
variable [Finite G] {N : Subgroup G} [N.Normal]

theorem eq_one_or_eq_of_map_eq_of_twin (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {x k : G} (hx : x ∈ J)
    (hk : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hxk : QuotientGroup.mk' N x = QuotientGroup.mk' N k) : k = 1 ∨ k = z :=
  E187C.eq_one_or_eq_of_map_eq_of_twin_of
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hK hz)
    hN hK hJ hKJ hzK hzJ hx hk hk2 hxk

theorem exists_conj_of_map_eq (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K :=
  E187C.exists_conj_of_map_eq_of (fun hK => hΩ.exists_uniqueInvolution hK) hΩ.conjInvariant
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hK hz)
    hN hK hL h

theorem exists_conj_normalizer (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  exact E187C.exists_conj_normalizer_of hΩ.conjInvariant (fun hK hL h => exists_conj_of_map_eq hΩ hN hK hL h) hN hK hU2 hUN

theorem exists_lift_USet (hΩ' : HM MT (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω)
    {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  exact E187C.exists_lift_USet_of (fun hU => hΩ'.exists_data_of_mem_USet hU)
    (fun hK hJ hA h4 hAK hAJ => hΩ'.eq_of_le_of_le hK hJ hA h4 hAK hAJ) hN hJ hUb hUbJ

theorem exists_conj_omegaStarNbr (hΩ : HM MT Ω)
    (hΩ' : HM MT (quotFamily Ω N)) (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) := by
  exact E187C.exists_conj_omegaStarNbr_of (fun hJ hUb hUbJ => exists_lift_USet hΩ' hN hJ hUb hUbJ)
    (fun hU => hΩ.isPGroup_of_mem_USet hU) (fun hK hU2 hUN => exists_conj_normalizer hΩ hN hK hU2 hUN) hK hJ h

theorem aEmpty_quotFamily (hΩ : HM MT Ω)
    (hΩ' : HM MT (quotFamily Ω N)) (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  exact E187C.aEmpty_quotFamily_of hΩ.conjInvariant
    (fun hK hJ h => exists_conj_omegaStarNbr hΩ hΩ' hN hK hJ h)
    (fun hK hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hK hT hTJ)
    (fun hK => hΩ.exists_uniqueInvolution hK) hN hA

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

structure E187Hyps : Prop where
  l67 : L6_7
  l69 : L6_9
  l611 : L6_11

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_dstarComp_of_twin (hΩ : HM MT Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) : K' ∈ dstarComp Ω K := by
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  by_cases hKK' : K' = K
  · rw [hKK']
    exact Relation.ReflTransGen.refl
  have hperp : K' ∈ KPerp Ω K := CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΩ hK'Ω hK
      hzK' hzK
  rcases hperp with h | ⟨-, -, R, hR, hRK', hRN⟩
  · exact absurd h hKK'
  obtain ⟨U, hUR, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_cyclic_index_two
  have hRsyl : IsSylow2In R K' := hΩ.isSylow2In_of_mem_RSet_of_le hK'Ω hR hRK'
  have hU : U ∈ USet Ω := mem_USet_of_natCard hK'Ω hRsyl hUR hcyc hcard
  exact Relation.ReflTransGen.single
    ⟨hK'Ω, Or.inl ⟨hK'Ω, hKK', U, hU, hUR.trans hRK', hUR.trans hRN⟩⟩

namespace E187Hyps
open CFSG.ClassicalInvolution.Asc77.E187Hyps

theorem etaAbelian (h : E187Hyps) (hΩ : HM MT Ω) :
    EtaAbelian Ω :=
  EtaAbelian.of_l6_9 h.l69 hΩ

theorem etaMeet (h : E187Hyps) (hΩ : HM MT Ω) :
    EtaMeet Ω :=
  EtaMeet.of_l6_11 h.l611 hΩ

end E187Hyps
section MinCex
variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.mem_of_conj_mem_dstar (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {M : Subgroup G} (hMS : M ∈ dstarComp Ω K) {u : G} (hu : u ∈ M)
    (hu4 : orderOf u = 4) {x : G} (hx : x * u * x⁻¹ ∈ H) : x ∈ H := by
  exact E187C.mem_of_conj_mem_dstar_of c.hyp.trans
    (fun hu hu4 hx => c.mem_of_conj_mem hA hM hu hu4 hx) hMS hu hu4 hx

end MinCex
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_mem_USet_le [Finite G] (hΩ : HM MT Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) : ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem dstarAdj_of_commutes [Finite G] (hΩ : HM MT Ω) {K J : Subgroup G}
    (hJ : J ∈ Ω) (hne : J ≠ K) (hc : Commutes J K) : dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := exists_mem_USet_le hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes (hUJ hu) hc)⟩⟩

theorem dstarAdj_of_le_normalizer [Finite G] (hΩ : HM MT Ω)
    {K J : Subgroup G} (hJ : J ∈ Ω) (hne : J ≠ K) (hN : J ≤ Subgroup.normalizer (K : Set G)) :
    dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := exists_mem_USet_le hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu => hN (hUJ hu)⟩⟩

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G] {N : Subgroup G} [N.Normal]

theorem omega4_quot_odd (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
        J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) :=
  E187C.omega4_quot_odd_of (fun hK => hΩ.exists_uniqueInvolution hK) hΩ.conjInvariant
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hK hz)
    hN hK hJ hne

theorem omega5_quot_odd (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' → ∀ z : G ⧸ N, IsUniqueInvolution L z →
      ∀ v ∈ L', (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) :=
  E187C.omega5_quot_odd_of (fun hK => hΩ.exists_uniqueInvolution hK) hΩ.conjInvariant hΩ.omega5 hN

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

section Finite
variable [Finite G] {Ω : Set (Subgroup G)}

theorem WSet.exists_normalized_sylow (hΩ : HM MT Ω)
    (S' : Sylow 2 G) :
    ∃ W' ∈ WSet Ω, W' ≤ (S' : Subgroup G) ∧ ∀ s ∈ (S' : Subgroup G), conjSub s W' = W' := by
  obtain ⟨η, hη, hinv⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ.toGen
      S'
  refine ⟨⨆ U ∈ η, U, ⟨η, ⟨S', hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2, ?_⟩
  intro s hs
  rw [conjSub_iSup₂]
  apply le_antisymm
  · exact iSup₂_le fun U hU => le_iSup₂_of_le _ (hinv s hs U hU) le_rfl
  · refine iSup₂_le fun U hU => ?_
    have hU' : conjSub s⁻¹ U ∈ η := hinv s⁻¹ ((S' : Subgroup G).inv_mem hs) U hU
    have : U = conjSub s (conjSub s⁻¹ U) := (conjSub_conjSub_inv s U).symm
    rw [this]
    exact le_iSup₂_of_le (conjSub s⁻¹ U) hU' le_rfl

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.conj_of_mem (c : MinCex MT Ω K S R W H) {x : G} (hx : x ∈ H) :
    MinCex MT Ω (conjSub x K) (conjSylow x S) (conjSub x R) (conjSub x W) H := by
  have := c.conj x
  rwa [conjSub_eq_self_of_mem hx] at this

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.le_H_of_mem_dstarComp (c : MinCex MT Ω K S R W H) {J : Subgroup G}
    (hJ : J ∈ dstarComp Ω K) : J ≤ H :=
  E187C.le_H_of_mem_dstarComp_of c.hyp.trans c.le_H hJ

end Asc77
end
section
namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Finite
variable [Finite G]

theorem exists_commuting_sylow_pair (hΩ : HM MT Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ R T : Subgroup G, IsSylow2In R K ∧ IsSylow2In T J ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Commutes R T :=
  E187C.exists_commuting_sylow_pair_of (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hJ hT hTJ)
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hK hJ hA h4 hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (l6_7_proved G Ω hΩ)
    hK hJ

theorem mem_omegaNbr_of_le_centralizer (hΩ : HM MT Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hJc : J ≤ Subgroup.centralizer ({z} : Set G)) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  have h8 := hΩ.eight_le_of_mem_RSet hR
  exact ⟨hJ, hne, R, hR, hRJ.1, hΩ.le_normalizer_of_le_centralizer hK hJ hne.symm hz hRJ.1
    hRJ.2.1 (by omega) (hRJ.1.trans hJc)⟩

theorem mem_dstarComp_of_twin (hΩ : HM MT Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K := by
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Relation.ReflTransGen.single
    (dstarAdj_of_le_normalizer hΩ hLΩ hLK (hΩ.le_normalizer_of_twin hLΩ hK hLK hzL hzK))

end Finite
end Asc77.AscE186
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]

theorem exists_lift_RSet (hΩ' : HM MT (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω)
    {Rb : Subgroup (G ⧸ N)} (hRb : Rb ∈ RSet (quotFamily Ω N))
    (hRbJ : Rb ≤ J.map (QuotientGroup.mk' N)) :
    ∃ R ∈ RSet Ω, R ≤ J ∧ R.map (QuotientGroup.mk' N) = Rb := by
  have hRbsyl : IsSylow2In Rb (J.map (QuotientGroup.mk' N)) :=
    hΩ'.isSylow2In_of_mem_RSet_of_le (map_mem_quotFamily hJ) hRb hRbJ
  obtain ⟨R, hR, hmap⟩ := exists_lift_sylow hN hRbsyl
  exact ⟨R, mem_RSet_of_isSylow2In hJ hR, hR.1, hmap⟩

theorem exists_lift_twin (hΩ : HM MT Ω)
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

theorem map_ne_of_twin (hΩ : HM MT Ω)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  E187C.map_ne_of_twin_of (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hK hz)
    hN hK hK' hne

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G]

theorem endgame_all [Finite G] {Ω : Set (Subgroup G)} (hΩ : HM MT Ω) {H : Subgroup G} {t : G}
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (ht : IsUniqueInvolution K₁ t) (hbad : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (n₁ : conjSub d₁ K₁ = K₁) (n₂ : conjSub d₂ K₁ = K₁) : False :=
  E187C.endgame_all_of (fun hQ => hΩ.eight_le_of_mem_RSet hQ) hK₁ ht hbad g₁ g₂ g₃ hc n₁ n₂

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem MinCex.center_eq_bot (h6 : E18_6At MT G) (c : MinCex MT Ω K S R W H) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, F, -, -, -, hF⟩ := h6 Ω K S R W H c
  exact E187C.center_eq_bot_of_centralizer_eq_bot hF

theorem MinCex.centralizer_ne_top (h6 : E18_6At MT G) (c : MinCex MT Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
  E187C.centralizer_singleton_ne_top (c.center_eq_bot h6) hx

theorem MinCex.of_sylow (c : MinCex MT Ω K S R W H) {S' : Sylow 2 G} {W' : Subgroup G}
    (hRS' : R ≤ (S' : Subgroup G)) {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S' : R' ≤ (S' : Subgroup G))
    (hW' : W' ∈ WSet Ω) (hW'S' : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') : MinCex MT Ω K S' R W' H where
  stand :=
    { hyp := c.stand.hyp
      mem := c.stand.mem
      aEmpty := c.stand.aEmpty
      twin := ⟨K', hK', hne, R', hR', hR'K', hR'S'⟩
      hR := ⟨c.stand.hR.1, c.stand.hR.2.1, hRS'⟩
      hW := ⟨hW', hW'S', hW'n⟩ }
  hyp := ⟨c.hyp.trans, c.hyp.cent⟩
  proper := c.proper

theorem MinCex.centralizer_le_H (h4 : E187E4CAt MT G) (c : MinCex MT Ω K S R W H)
    {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {A : Subgroup G}
    (hA : IsPGroup 2 A) (hAcyc : (∃ w : G, w ≠ 1 ∧ w * w = 1 ∧ A = Subgroup.zpowers w)) (hRA : R ⊔
        R' ≤ Subgroup.centralizer (A : Set G))
    (hX : Subgroup.centralizer (A : Set G) ≠ ⊤) : Subgroup.centralizer (A : Set G) ≤ H := by
  have hΩ : HM MT Ω := c.stand.hyp
  obtain ⟨S', hRS', hR'S', hSyl⟩ :=
    E187C.exists_sylow_inf_centralizer c.stand.hR.2.2 hR'S hRA
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hΩ S'
  have c' := c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n
  exact h4 Ω K S' R W' H c' K' hK' hne R' hR' hR'K' hR'S' A hA hAcyc hRA hX hSyl

end Asc77
end

end CFSG.ClassicalInvolution.T7FU
