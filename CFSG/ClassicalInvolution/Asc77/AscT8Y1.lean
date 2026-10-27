module

import CFSG.ClassicalInvolution.Asc77.AscT8Y1Eng
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd
public import CFSG.ClassicalInvolution.Asc77.AscT8LayerCl

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8

section Good

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem layerJoin_conjSub_eq (hΩ : HypOmegaMod p f Ω) {x n : G} (hn : n ∈ cenZ x) :
    conjSub n (layerJoin Ω x) = layerJoin Ω x := by
  exact layerJoin_conjSub_eqE (fun hL hm => layerSet_conj hΩ hL hm) hn

theorem mem_normalizer_oddCoreOf_layerJoin (hΩ : HypOmegaMod p f Ω) {x n : G} (hn : n ∈ cenZ x) :
    n ∈ Subgroup.normalizer (oddCoreOf (layerJoin Ω x) : Set G) :=
  mem_normalizer_oddCore_of_mem_normalizer
    (mem_normalizer_iff_conjSub_eq.mpr (layerJoin_conjSub_eq hΩ hn))

theorem oddCoreOf_layerJoin_le_of_good (hΩ : HypOmegaMod p f Ω) {x : G} {E J : Subgroup G}
    (hEcomm : IsMulCommutative E) (hEexp : ∀ w ∈ E, w ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hEx : E ≤ cenZ x)
    (hgood : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ J) :
    oddCoreOf (layerJoin Ω x) ≤ J :=
  CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le hEcomm hEexp hE4
    (fun _ hw => mem_normalizer_oddCoreOf_layerJoin hΩ (hEx hw)) (odd_natCard_oddCoreOf _)
    (fun e he he1 => inf_le_right.trans (hgood e he he1))

theorem oddCoreOf_layerJoin_le_of_good_pair (hΩ : HypOmegaMod p f Ω) {x u v : G} {J : Subgroup G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hne : u ≠ v) (hux : u ∈ cenZ x) (hvx : v ∈ cenZ x)
    (hgu : Subgroup.centralizer ({u} : Set G) ≤ J) (hgv : Subgroup.centralizer ({v} : Set G) ≤ J)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ J) :
    oddCoreOf (layerJoin Ω x) ≤ J := by
  exact oddCoreOf_layerJoin_le_of_good_pairE (oddCoreOf_layerJoin_le_of_good hΩ) hu hv huv hu1 hv1
    hne hux hvx hgu hgv hguv

end Good

section Star

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem layer_omegaStarNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (m : ↥(layerJoin Ω x))
    (h : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      omegaStarNbr (restrictFamily (layerSet Ω x) (layerJoin Ω x))
        (conjSub m ((layerRes x K).subgroupOf (layerJoin Ω x)))) :
    J ∈ omegaStarNbr Ω (conjSub (m : G) K) := by
  obtain ⟨-, hne, U', hU'S, hU'J, hU'N⟩ := h
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  obtain ⟨R', hR'S, -, -, -, hU'R', hcyc, hcard, h4⟩ := hΛ.exists_data_of_mem_USet hp hU'S
  have hmc : (m : G) ∈ cenZ x := layerJoin_le_cenZ x m.2
  have hKm : XMem Ω x (conjSub (m : G) K) := hK.conj hΩ hmc
  have hLm : layerRes x (conjSub (m : G) K) = conjSub (m : G) (layerRes x K) :=
    (layerRes_conj K hmc).symm
  have hYJ : layerRes x J ≤ layerJoin Ω x := le_layerJoin ⟨J, hJ, rfl⟩
  have hYKm : layerRes x (conjSub (m : G) K) ≤ layerJoin Ω x := le_layerJoin ⟨_, hKm, rfl⟩
  have hUJ : U'.map (layerJoin Ω x).subtype ≤ layerRes x J := by
    have := Subgroup.map_mono (f := (layerJoin Ω x).subtype) hU'J
    rwa [Subgroup.map_subgroupOf_eq_of_le hYJ] at this
  obtain ⟨J₀, ⟨J₀', hJ₀', rfl⟩, hJ₀Y, hRJ₀⟩ := exists_isSylow2In_of_mem_RSet_restrict hR'S
  have hRK₀ : IsSylow2In (R'.map (layerJoin Ω x).subtype) J₀' :=
    hJ₀'.isSylow2In_of_layerRes hp hq hΩ hx hRJ₀
  have hUR : U'.map (layerJoin Ω x).subtype ≤ R'.map (layerJoin Ω x).subtype :=
    Subgroup.map_mono hU'R'
  have hUcyc : IsCyclic ↥(U'.map (layerJoin Ω x).subtype) := by
    have := hcyc
    exact isCyclic_of_surjective
      (U'.equivMapOfInjective (layerJoin Ω x).subtype (layerJoin Ω x).subtype_injective).toMonoidHom
      (U'.equivMapOfInjective (layerJoin Ω x).subtype (layerJoin Ω x).subtype_injective).surjective
  have hUcard : Nat.card (R'.map (layerJoin Ω x).subtype) =
      2 * Nat.card (U'.map (layerJoin Ω x).subtype) := by
    rw [Subgroup.card_map_of_injective (layerJoin Ω x).subtype_injective,
      Subgroup.card_map_of_injective (layerJoin Ω x).subtype_injective]
    exact hcard
  have hU4 : 4 ≤ Nat.card (U'.map (layerJoin Ω x).subtype) := by
    rw [Subgroup.card_map_of_injective (layerJoin Ω x).subtype_injective]
    exact h4
  have hUS : U'.map (layerJoin Ω x).subtype ∈ USet Ω :=
    mem_USet_of_natCard hJ₀'.1 hRK₀ hUR hUcyc hUcard
  have hU2 : IsPGroup 2 (U'.map (layerJoin Ω x).subtype) := hRK₀.2.1.to_le hUR
  have hJJ : J₀' = J := hΩ.eq_of_le_of_le hJ₀'.1 hJ.1 hU2 hU4 (hUR.trans hRK₀.1)
    (hUJ.trans (layerRes_le x J))
  subst hJJ
  have hKJ : conjSub (m : G) K ≠ J₀' := by
    intro hKJ
    apply hne
    rw [← hKJ, hLm, conjSub_subgroupOf]
  obtain ⟨z', hz'⟩ := hΩ.exists_uniqueInvolution hp hq hKm.1
  have hz'L := hKm.isUniqueInvolution_layerRes hp hq hΩ hx hz'
  have hYm : conjSub (m : G) (layerRes x K) ≤ layerJoin Ω x := by
    rw [← hLm]
    exact hYKm
  have hUN : U'.map (layerJoin Ω x).subtype ≤
      Subgroup.normalizer (layerRes x (conjSub (m : G) K) : Set G) := by
    rintro _ ⟨u', hu', rfl⟩
    have h1 := hU'N hu'
    rw [conjSub_subgroupOf] at h1
    show (u' : G) ∈ _
    rw [hLm]
    exact (mem_normalizer_subgroupOf_iff hYm).mpr h1
  have hAc : U'.map (layerJoin Ω x).subtype ≤ Subgroup.centralizer ({z'} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_conjSub_eq hz' (layerRes_le x (conjSub (m : G) K)) hz'L.mem
      (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z' = (u * z' * u⁻¹) * u := by group
      _ = z' * u := by rw [this]
  have hUNK : U'.map (layerJoin Ω x).subtype ≤ Subgroup.normalizer (conjSub (m : G) K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hKm.1 hJ₀'.1 hKJ hz' (hUR.trans hRK₀.1) hU2
      (by omega) hAc
  exact ⟨hJ₀'.1, fun h => hKJ h.symm, _, hUS, hUR.trans hRK₀.1, hUNK⟩

theorem exists_oddCore_conj_omegaStarNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (h : layerImg Ω x J ∈ omegaStarNbr (layerFamQ Ω x) (layerImg Ω x K)) :
    ∃ n ∈ oddCoreOf (layerJoin Ω x), J ∈ omegaStarNbr Ω (conjSub n K) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  have hΨ := hypOmegaMod_layerQuot hp hq hΩ hx
  have hKL : layerRes x K ∈ layerSet Ω x := ⟨K, hK, rfl⟩
  have hJL : layerRes x J ∈ layerSet Ω x := ⟨J, hJ, rfl⟩
  have hK'Λ : (layerRes x K).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hKL, le_layerJoin hKL, rfl⟩
  have hJ'Λ : (layerRes x J).subgroupOf (layerJoin Ω x) ∈
      restrictFamily (layerSet Ω x) (layerJoin Ω x) := ⟨_, hJL, le_layerJoin hJL, rfl⟩
  obtain ⟨m, hmN, hm⟩ := exists_conj_omegaStarNbr hp hq hΛ hΨ hodd hK'Λ hJ'Λ h
  exact ⟨(m : G), ⟨m, hmN, rfl⟩, layer_omegaStarNbr hp hq hΩ hx hK hJ m hm⟩

theorem exists_oddCore_conj_mem_dstarComp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (hK : XMem Ω x K)
    (hconn : T3.DStarConnected (layerFamQ Ω x)) {M : Subgroup G} (hM : XMem Ω x M) :
    ∃ ν ∈ oddCoreOf (layerJoin Ω x), conjSub ν M ∈ dstarComp Ω K := by
  have key : ∀ U : Subgroup (LayerQuot Ω x),
      Relation.ReflTransGen (dstarAdj (layerFamQ Ω x)) (layerImg Ω x K) U →
      U ∈ layerFamQ Ω x ∧ ∀ M' : Subgroup G, XMem Ω x M' → layerImg Ω x M' = U →
        ∃ ν ∈ oddCoreOf (layerJoin Ω x), conjSub ν M' ∈ dstarComp Ω K := by
    intro U hU
    induction hU with
    | refl =>
      refine ⟨layerImg_mem hK, fun M' hM' h => ?_⟩
      obtain ⟨n, hn, hnM⟩ := exists_oddCore_conj_of_layerImg_eq hp hq hΩ hx hK hM' h.symm
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      rw [← hnM, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M' hM' hMc => ?_⟩
      obtain ⟨_, ⟨L, ⟨M₁, hM₁, rfl⟩, hLY, rfl⟩, hb⟩ := hbΦ
      have hb' : layerImg Ω x M₁ = b := hb
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ hb'
      have hν₁c : ν₁ ∈ cenZ x := layerJoin_le_cenZ x (oddCoreOf_le_self _ hν₁)
      have hM₂X : XMem Ω x (conjSub ν₁ M₁) := hM₁.conj hΩ hν₁c
      have hM₂b : layerImg Ω x (conjSub ν₁ M₁) = b :=
        (layerImg_conj_of_mem_oddCore hν₁).trans hb'
      have hdc : dstarComp Ω (conjSub ν₁ M₁) = dstarComp Ω K := T7A.dstarComp_eq_of_mem hK.1 hM₂
      rcases hadj with hc1 | hc2
      · rw [← hM₂b, ← hMc] at hc1
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaStarNbr hp hq hΩ hx hM₂X hM' hc1
        refine ⟨m⁻¹, (oddCoreOf _).inv_mem hm, ?_⟩
        have h1 := omegaStarNbr_conj hΩ.conjInvariant hmn m⁻¹
        rw [conjSub_inv_conjSub] at h1
        have h2 : conjSub m⁻¹ M' ∈ dstarComp Ω (conjSub ν₁ M₁) :=
          Relation.ReflTransGen.single ⟨hΩ.conjInvariant m⁻¹ M' hM'.1, Or.inl h1⟩
        rwa [hdc] at h2
      · rw [← hM₂b, ← hMc] at hc2
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaStarNbr hp hq hΩ hx hM' hM₂X hc2
        refine ⟨m, hm, ?_⟩
        exact Relation.ReflTransGen.tail hM₂
          ⟨hΩ.conjInvariant m M' hM'.1, Or.inr hmn⟩
  exact (key _ (hconn _ (layerImg_mem hK) _ (layerImg_mem hM))).2 M hM rfl

end Star

end T8

end CFSG.ClassicalInvolution.Asc77
