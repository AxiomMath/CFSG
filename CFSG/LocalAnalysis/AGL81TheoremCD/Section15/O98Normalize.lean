module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O97Defs

import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98ThreeEleven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Shape
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import TauCeti.Algebra.Group.Coprime
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open

theorem O97Red.le_normalizer_E {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (h : O97Red X E Y S) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    E ≤ Subgroup.normalizer (L : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card (p := 3) Nat.prime_three h.core hL
  have hrank : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl h.elem_E
      (by rw [h.card_E]; norm_num)
  rcases le_gamma_or_le_normalizer (p := 3) Nat.prime_three hL h3 h.elem_E hrank with hΓ | hN
  · exact absurd (hΓ.trans h.gamma_le) hLY
  · exact hN

theorem O97Red.exists_inner {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (hK35 : KFactThreeFiveInner) (h : O97Red X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ k ∈ L, ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X' : Subgroup X := Subgroup.normalizer (L : Set X)
  have hLX' : L ≤ X' := Subgroup.le_normalizer
  have hEX' : E ≤ X' := O97Red.le_normalizer_E h hL hLY
  let K : Subgroup X' := L.subgroupOf X'
  let E' : Subgroup X' := E.subgroupOf X'
  have hKnormal : K.Normal := Subgroup.normal_in_normalizer (H := L)
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.LocalCores.component_overgroup hL hLX').1
  have hKcore : CFSG.pPrimeCore 3 ↥K = ⊥ :=
    h.pPrimeCore_subgroupOf_normalizer_eq_bot hL
  have hEelem : CFSG.Open.IsElemAbelian 3 E' :=
    CFSG.Open.IsElemAbelian.subgroupOf h.elem_E X'
  have hEcard : Nat.card E' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX').toEquiv, h.card_E]
  have hnotΓ : ¬ K ≤ CFSG.Open.rankThreeGamma 1 3 E' := by
    intro hKΓ
    have hKY : K ≤ Y.subgroupOf X' := hKΓ.trans (h.rankThreeGamma_subgroupOf_le X')
    apply hLY
    intro y hy
    exact hKY (show (⟨y, hLX' hy⟩ : X') ∈ K from hy)
  obtain ⟨e, heE', he1, k, hkK, hrel⟩ :=
    hK35 X' (h.catalog.subgroup X') K E' hKnormal hKq hKcore hEelem hEcard
      (h.rank23_subgroup X') (h.pRank_rankThreeGamma_subgroupOf_le X') hnotΓ
  have heE : (e : X) ∈ E := Subgroup.mem_subgroupOf.mp heE'
  have hkL : (k : X) ∈ L := Subgroup.mem_subgroupOf.mp hkK
  have he1' : (e : X) ≠ 1 := fun h => he1 (Subtype.ext h)
  refine ⟨(e : X), heE, he1', (k : X), hkL, ?_⟩
  intro y hy
  let y' : X' := ⟨y, hLX' hy⟩
  have hy' : y' ∈ K := Subgroup.mem_subgroupOf.mpr hy
  have h := hrel y' hy'
  simpa using congrArg Subtype.val h

private theorem pow_three_mem_center_of_inner {X : Type} [Group X] {L : Subgroup X}
    {e k : X} (hkL : k ∈ L) (he3 : e ^ 3 = 1)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) :
    (⟨k, hkL⟩ : L) ^ 3 ∈ Subgroup.center ↥L := by
  let c : X := k⁻¹ * e
  have hc_cent : c ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcy : c * y = y * c := by
      calc c * y = k⁻¹ * (e * y) := by simp only [c]; group
        _ = k⁻¹ * ((e * y * e⁻¹) * e) := by group
        _ = k⁻¹ * ((k * y * k⁻¹) * e) := by rw [hrel y hy]
        _ = y * c := by simp only [c]; group
    exact hcy.symm
  have hkce : k * c = e := by simp only [c]; group
  have hck : Commute k c := Subgroup.mem_centralizer_iff.mp hc_cent k hkL
  have he3' : (k * c) ^ 3 = 1 := by rw [hkce]; exact he3
  have hcube : k ^ 3 * c ^ 3 = 1 := (hck.mul_pow 3).symm.trans he3'
  have hk3 : k ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hcube
  have hc3_cent : c ^ 3 ∈ Subgroup.centralizer (L : Set X) :=
    Subgroup.pow_mem _ hc_cent 3
  have hk3_cent : k ^ 3 ∈ Subgroup.centralizer (L : Set X) := by
    rw [hk3]
    exact Subgroup.inv_mem _ hc3_cent
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hk3_cent (g : X) g.2

private theorem mem_Y_of_inner {X : Type} [Group X] [Finite X] {E Y : Subgroup X}
    {L : Subgroup X} {e k : X} (hE : CFSG.Open.IsElemAbelian 3 E) (heE : e ∈ E)
    (he1 : e ≠ 1) (hγ : CFSG.Open.rankThreeGamma 1 3 E ≤ Y) (hkL : k ∈ L)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) :
    k ∈ Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkC : k ∈ Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : e * k * e⁻¹ = k := by simpa using hrel k hkL
    calc e * k = (e * k * e⁻¹) * e := by group
      _ = k * e := by rw [h1]
  exact hγ (CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := 3)
    (A := E) (M := CFSG.Open.rankThreeGamma 1 3 E) le_rfl heE
    (orderOf_eq_prime (hE.2 e heE) he1) hkC)

private theorem not_mem_center_of_inner {X : Type} [Group X] [Finite X]
    {E Y : Subgroup X} {L : Subgroup X} {e k : X} (hE : CFSG.Open.IsElemAbelian 3 E)
    (heE : e ∈ E) (he1 : e ≠ 1) (hγ : CFSG.Open.rankThreeGamma 1 3 E ≤ Y) (hkL : k ∈ L)
    (hrel : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) (hLY : ¬ L ≤ Y) :
    (⟨k, hkL⟩ : L) ∉ Subgroup.center ↥L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hkZ
  have hEL : L ≤ Subgroup.centralizer ({e} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hky : k * y * k⁻¹ = y := by
      have h := Subgroup.mem_center_iff.mp hkZ (⟨y, hy⟩ : L)
      have h' : k * y = y * k := (congrArg Subtype.val h).symm
      rw [h']
      group
    have h := hrel y hy
    rw [hky] at h
    calc e * y = (e * y * e⁻¹) * e := by group
      _ = y * e := by rw [h]
  have hC : Subgroup.centralizer ({e} : Set X) ≤ CFSG.Open.rankThreeGamma 1 3 E :=
    CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := 3) (A := E)
      (M := CFSG.Open.rankThreeGamma 1 3 E) le_rfl heE
      (orderOf_eq_prime (hE.2 e heE) he1)
  exact hLY (hEL.trans (hC.trans hγ))

private theorem le_normalizer_of_moved_component {X : Type} [Group X] [Finite X]
    {L S : Subgroup X} (hL : CFSG.IsComponent L) (hS2 : IsPGroup 2 S) {k : X}
    (hkL : k ∈ L) (hk3 : (⟨k, hkL⟩ : L) ^ 3 ∈ Subgroup.center ↥L)
    (hkZ : (⟨k, hkL⟩ : L) ∉ Subgroup.center ↥L)
    (hconj : ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ S) :
    S ≤ Subgroup.normalizer (L : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  by_contra hsN
  let Ls : Subgroup X := L.map (MulAut.conj s).toMonoidHom
  have hLs : CFSG.IsComponent Ls :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hL
  have hne : Ls ≠ L := by
    intro h
    exact hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hne' : L ≠ Ls := fun h => hne h.symm
  have hcomm : L ≤ Subgroup.centralizer (Ls : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hL hLs).resolve_left hne')
  let k' : X := s * k⁻¹ * s⁻¹
  have hk' : k' ∈ Ls := by
    refine Subgroup.mem_map.mpr ⟨k⁻¹, L.inv_mem hkL, ?_⟩
    simp [k', MulAut.conj_apply]
  have hck : Commute k k' :=
    (Subgroup.mem_centralizer_iff.mp (hcomm hkL) k' hk').symm
  let c : X := k * s * k⁻¹ * s⁻¹
  have hcS : c ∈ S := hconj s hs
  have hc_eq : c = k * k' := by simp only [c, k']; group
  obtain ⟨m, hm⟩ := hS2.exists_card_eq
  have hc_pow : c ^ (2 ^ m) = 1 := by
    have h := pow_card_eq_one' (G := ↥S) (x := ⟨c, hcS⟩)
    rw [hm] at h
    simpa using congrArg Subtype.val h
  have hmul : k ^ (2 ^ m) * k' ^ (2 ^ m) = 1 := by
    rw [← hck.mul_pow (2 ^ m), ← hc_eq]
    exact hc_pow
  have hkpowLs : k ^ (2 ^ m) ∈ Ls := by
    rw [eq_inv_of_mul_eq_one_left hmul]
    exact Ls.inv_mem (Ls.pow_mem hk' _)
  have hkpow_center : (⟨k, hkL⟩ : L) ^ (2 ^ m) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : X) * k ^ (2 ^ m) = k ^ (2 ^ m) * (g : X)
    exact (Subgroup.mem_centralizer_iff.mp (hcomm g.2) (k ^ (2 ^ m)) hkpowLs).symm
  have hcop : Nat.Coprime 3 (2 ^ m) :=
    Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)
  obtain ⟨i, j, hij⟩ :=
    TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := ↥L) hcop
  have hmem : ((⟨k, hkL⟩ : L) ^ 3) ^ i * ((⟨k, hkL⟩ : L) ^ (2 ^ m)) ^ j ∈
      Subgroup.center ↥L :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hk3 i) (Subgroup.zpow_mem _ hkpow_center j)
  rw [hij (⟨k, hkL⟩ : L)] at hmem
  exact hkZ hmem

theorem O97Red.le_normalizer_S {X : Type} [Group X] [Finite X] {E Y S : Subgroup X}
    (hK35 : KFactThreeFiveInner) (h : O97Red X E Y S) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    S ≤ Subgroup.normalizer (L : Set X) := by
  obtain ⟨e, heE, he1, k, hkL, hrel⟩ := O97Red.exists_inner hK35 h hL hLY
  have hkY : k ∈ Y := mem_Y_of_inner h.elem_E heE he1 h.gamma_le hkL hrel
  have hk3 : (⟨k, hkL⟩ : L) ^ 3 ∈ Subgroup.center ↥L :=
    pow_three_mem_center_of_inner hkL (h.elem_E.2 e heE) hrel
  have hkZ : (⟨k, hkL⟩ : L) ∉ Subgroup.center ↥L :=
    not_mem_center_of_inner h.elem_E heE he1 h.gamma_le hkL hrel hLY
  have hconj : ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ S := by
    intro s hs
    exact S.mul_mem (h.normal_S k hkY s hs) (S.inv_mem hs)
  exact le_normalizer_of_moved_component hL h.two_S hkL hk3 hkZ hconj

theorem O98Red.le_normalizer_E {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (h : O98Red X E Y S z) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    E ≤ Subgroup.normalizer (L : Set X) :=
  h.toO97Red.le_normalizer_E hL hLY

theorem O98Red.le_normalizer_S {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (hK35 : KFactThreeFiveInner) (h : O98Red X E Y S z) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    S ≤ Subgroup.normalizer (L : Set X) :=
  h.toO97Red.le_normalizer_S hK35 hL hLY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
