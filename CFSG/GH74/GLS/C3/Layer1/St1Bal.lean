module

public import CFSG.GH74.GLS.C3.Layer1.St1Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section Balance

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pPrimeCoreOf_of_normal_odd {Z W : Subgroup G} (hWZ : W ≤ Z)
    (hN : (W.subgroupOf Z).Normal) (hcop : Nat.Coprime 2 (Nat.card W)) :
    W ≤ pPrimeCoreOf 2 Z := by
  have hcard : Nat.card (W.subgroupOf Z) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWZ).toEquiv
  have h1 : W.subgroupOf Z ≤ pPrimeCore 2 ↥Z := le_sSup ⟨hN, by rw [hcard]; exact hcop⟩
  have h2 : (W.subgroupOf Z).map Z.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWZ
  rw [← h2]
  exact Subgroup.map_mono h1

omit [Finite G] in
theorem pPrimeCoreOf_le_self (C : Subgroup G) : pPrimeCoreOf 2 C ≤ C := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem coprime_card_pPrimeCoreOf (C : Subgroup G) : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 C)) := by
  unfold pPrimeCoreOf
  rw [Subgroup.card_map_of_injective C.subtype_injective]
  exact pPrimeCore_coprime_card

theorem isUnbalancingTriple_of_gsUnbalancingTriple {a x : G} {J : Subgroup G}
    (h : GSUnbalancingTriple a x J) : IsUnbalancingTriple a x J := by
  obtain ⟨ha, hx, hax, hJa, hJpc, hJx, hJD⟩ := gsUnbalancingTriple_iff.mp h
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hxN : x ∈ normalizer (J : Set G) := by
    have hfwd : ∀ n ∈ J, x * n * x⁻¹ ∈ J := by
      intro n hn
      have h1 : ⁅n⁻¹, x⁆ ∈ ⁅J, zpowers x⁆ :=
        commutator_mem_commutator (inv_mem hn) (mem_zpowers x)
      rw [hJx, commutatorElement_def, inv_inv] at h1
      have h2 := mul_mem hn h1
      rwa [show n * (n⁻¹ * x * n * x⁻¹) = x * n * x⁻¹ by group] at h2
    rw [mem_normalizer_iff]
    intro n
    refine ⟨hfwd n, fun hn => ?_⟩
    have h1 := hfwd _ hn
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    rwa [hxinv, show x * (x * n * x) * x = (x * x) * n * (x * x) by group, hxx, one_mul,
      mul_one] at h1
  refine ⟨⟨ha, hJa, hJpc⟩, hx, mem_centralizer_singleton_iff.mpr hax.symm, hxN, ?_⟩
  intro hcent
  have hJle : J ≤ pPrimeCoreOf 2 J := by
    refine le_of_eq_of_le hJD.symm ?_
    refine Subgroup.commutator_le.mpr fun j hj d hd => ?_
    exact (hcent hd).2.2 j hj
  have hJtop : pPrimeCore 2 ↥J = ⊤ := by
    rw [eq_top_iff]
    intro j _
    obtain ⟨j₀, hj₀, hj₀j⟩ := hJle j.2
    have : j₀ = j := Subtype.ext hj₀j
    rwa [← this]
  have hJcop : Nat.Coprime 2 (Nat.card J) := by
    have h1 := (pPrimeCore_coprime_card (p := 2) (G := ↥J))
    rwa [hJtop, Subgroup.card_top] at h1
  obtain ⟨Kh, hKh, hJsub, hJmap, -⟩ := hJpc
  have hJ'cop : Nat.Coprime 2 (Nat.card (J.subgroupOf (centralizer ({a} : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJa).toEquiv]
    exact hJcop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJle' := le_pPrimeCore_of_subnormal 2 hJsub hJ'cop
  have hKbot : Kh = ⊥ := by
    rw [← hJmap, eq_bot_iff]
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hJle' hc
  have hnt : Nontrivial Kh := CFSG.LocalCores.isQuasisimple_nontrivial hKh.1
  subst hKbot
  exact absurd hnt (not_nontrivial_iff_subsingleton.mpr inferInstance)

theorem IsUnbalancingTriple.gsUnbalancingTriple {a x : G} {J : Subgroup G}
    (h : IsUnbalancingTriple a x J) : GSUnbalancingTriple a x J := by
  obtain ⟨⟨ha, hJa, hJpc⟩, hx, hxa, hxN, hnot⟩ := h
  have hax : a * x = x * a := (mem_centralizer_singleton_iff.mp hxa).symm
  let H : Subgroup G := centralizer ({a} : Set G)
  let xH : H := ⟨x, hxa⟩
  let W : Subgroup G := pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊓ H
  let D : Subgroup H := W.subgroupOf H
  let L : Subgroup H := J.subgroupOf H
  have hJH : J ≤ H := hJa
  have hxH : orderOf xH = 2 := by
    rw [Subgroup.orderOf_mk, hx]
  have hL : IsPComponent 2 L := hJpc
  have hDC : D ≤ centralizer ({xH} : Set H) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hdW : ((d : H) : G) ∈ W := Subgroup.mem_subgroupOf.mp hd
    have hdC : ((d : H) : G) ∈ centralizer ({x} : Set G) :=
      CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_le (centralizer ({x} : Set G))
        (Subgroup.mem_inf.mp hdW).1
    exact Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hDn : (D.subgroupOf (centralizer ({xH} : Set H))).Normal := by
    refine ⟨fun d hd c => ?_⟩
    have hdW : ((d : H) : G) ∈ W :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hd)
    have hdO : ((d : H) : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
      (Subgroup.mem_inf.mp hdW).1
    have hdA : ((d : H) : G) ∈ H := (Subgroup.mem_inf.mp hdW).2
    have hcX : ((c : H) : G) ∈ centralizer ({x} : Set G) := by
      have hcx := Subgroup.mem_centralizer_singleton_iff.mp
        (c : centralizer ({xH} : Set H)).2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg (fun z : H => (z : G)) hcx)
    have hcA : ((c : H) : G) ∈ H := (c : H).2
    have hO : ((c : H) : G) * ((d : H) : G) * ((c : H) : G)⁻¹ ∈
        pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
      CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_normalized (centralizer ({x} : Set G)) hcX hdO
    have hA : ((c : H) : G) * ((d : H) : G) * ((c : H) : G)⁻¹ ∈ H :=
      mul_mem (mul_mem hcA hdA) (inv_mem hcA)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Subgroup.mem_inf.mpr ⟨hO, hA⟩
  have hDodd : Odd (Nat.card D) := by
    have hWodd : Odd (Nat.card W) :=
      Odd.of_dvd_nat (CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd (centralizer ({x} : Set G)))
        (Subgroup.card_dvd_of_le (show W ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) from inf_le_left))
    change Odd (Nat.card (W.subgroupOf H))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show W ≤ H from inf_le_right)).toEquiv]
    exact hWodd
  have hnormH : D ≤ normalizer (L : Set H) :=
    CFSG.ComponentClassification.UnbalancedLayer.odd_fixed_core_normalizes_two_components
      hxH hDC hDn hDodd L hL
  have hWN : W ≤ normalizer (J : Set G) := by
    intro w hw
    have hwH : w ∈ H := (Subgroup.mem_inf.mp hw).2
    have hwD : (⟨w, hwH⟩ : H) ∈ D := Subgroup.mem_subgroupOf.mpr hw
    have hwN : (⟨w, hwH⟩ : H) ∈ normalizer (L : Set H) := hnormH hwD
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      have hjH : (⟨j, hJH hj⟩ : H) ∈ L := Subgroup.mem_subgroupOf.mpr hj
      have hconj := (Subgroup.mem_normalizer_iff.mp hwN ⟨j, hJH hj⟩).mp hjH
      exact Subgroup.mem_subgroupOf.mp hconj
    · intro hj
      have hjH : (⟨w * j * w⁻¹, hJH hj⟩ : H) ∈ L :=
        Subgroup.mem_subgroupOf.mpr hj
      have hconj := (Subgroup.mem_normalizer_iff.mp (inv_mem hwN)
        ⟨w * j * w⁻¹, hJH hj⟩).mp hjH
      have := Subgroup.mem_subgroupOf.mp hconj
      simpa [mul_assoc] using this
  have hcent_iff : W ≤ centralizerSection J (pPrimeCoreOf 2 J) ↔
      ⁅J, W⁆ ≤ pPrimeCoreOf 2 J := by
    constructor
    · intro hWle
      exact Subgroup.commutator_le.mpr fun j hj w hw => (hWle hw).2.2 j hj
    · intro hcomm w hw
      exact ⟨hWN hw,
        CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (hWN hw),
        fun j hj => Subgroup.commutator_le.mp hcomm j hj w hw⟩
  have hnotComm : ¬ ⁅J, W⁆ ≤ pPrimeCoreOf 2 J :=
    fun hcomm => hnot (hcent_iff.mpr hcomm)
  have hLD : ¬ ⁅L, D⁆ ≤ (pPrimeCore 2 L).map L.subtype := by
    intro hle
    apply hnotComm
    have hmap : (⁅L, D⁆).map H.subtype ≤
        ((pPrimeCore 2 L).map L.subtype).map H.subtype :=
      Subgroup.map_mono hle
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH,
      Subgroup.map_subgroupOf_eq_of_le (show W ≤ H from inf_le_right)] at hmap
    change ⁅J, W⁆ ≤ (pPrimeCoreOf 2 L).map H.subtype at hmap
    rwa [← CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_eq_map_subgroupOf hJH] at hmap
  obtain ⟨-, -, hLD_eq, hLx_eq⟩ :=
    CFSG.ComponentClassification.UnbalancedLayer.odd_fixed_core_active_two_component
      hxH hDC hDn hDodd hL hLD
  have hzx : zpowers x = (zpowers xH).map H.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hJD_eq : ⁅J, W⁆ = J := by
    have hmap := congrArg (Subgroup.map H.subtype) hLD_eq
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH,
      Subgroup.map_subgroupOf_eq_of_le (show W ≤ H from inf_le_right)] at hmap
    exact hmap
  have hJx_eq : ⁅J, zpowers x⁆ = J := by
    have hmap := congrArg (Subgroup.map H.subtype) hLx_eq
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH,
      ← hzx] at hmap
    exact hmap
  exact gsUnbalancingTriple_iff.mpr ⟨ha, hx, hax, hJa, hJpc, hJx_eq, hJD_eq⟩

theorem exists_isUnbalancingTriple_of_not_le {a x : G} (ha : orderOf a = 2) (hx : orderOf x = 2)
    (hax : a * x = x * a)
    (h : ¬ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G) ≤
      pPrimeCoreOf 2 (centralizer ({a} : Set G))) :
    ∃ J : Subgroup G, IsUnbalancingTriple a x J := by
  rcases CFSG.ComponentClassification.UnbalancedLayer.commuting_involution_odd_core_unbalancing_triple
      ha hx hax with hle | ⟨J, hJ⟩
  · exact absurd hle h
  · exact ⟨J, isUnbalancingTriple_of_gsUnbalancingTriple hJ⟩

theorem IsUnbalancingTriple.isLocallyUnbalancing {x y : G} {K : Subgroup G}
    (h : IsUnbalancingTriple x y K) : IsLocallyUnbalancing x y K := by
  obtain ⟨hK, hy, hyx, hyN, hnot⟩ := h
  refine ⟨hK, hy, hyx, hyN, fun hle => hnot ?_⟩
  refine le_trans ?_ hle
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ centralizer ({x} : Set G)
    with hW
  set Z : Subgroup G := centralizer ({x, y} : Set G) with hZ
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hyx).symm
  have hZmem : ∀ z, z ∈ Z ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZ, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  have hWZ : W ≤ Z := by
    intro w hw
    rw [hZmem]
    refine ⟨?_, ?_⟩
    · exact mem_centralizer_singleton_iff.mp hw.2
    · exact mem_centralizer_singleton_iff.mp (pPrimeCoreOf_le_self _ hw.1)
  have key : ∀ z ∈ Z, ∀ w ∈ W, z * w * z⁻¹ ∈ W := by
    intro z hz w hw
    have hzx : z ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((hZmem z).mp hz).1
    have hzy : z ∈ centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((hZmem z).mp hz).2
    refine ⟨CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore hzy hw.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzx hw.2) (Subgroup.inv_mem _ hzx)
  refine le_pPrimeCoreOf_of_normal_odd hWZ ?_ ?_
  · rw [normal_subgroupOf_iff_le_normalizer hWZ]
    intro z hz
    rw [mem_normalizer_iff]
    intro w
    refine ⟨key z hz w, fun hw => ?_⟩
    have h1 := key z⁻¹ (inv_mem hz) _ hw
    rwa [show z⁻¹ * (z * w * z⁻¹) * z⁻¹⁻¹ = w by group] at h1
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf _)

omit [Finite G] in
theorem isBalancedWrt_of_forall {A : Subgroup G}
    (h : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      pPrimeCoreOf 2 (centralizer ({b} : Set G)) ⊓ centralizer ({a} : Set G) ≤
        pPrimeCoreOf 2 (centralizer ({a} : Set G))) : IsBalancedWrt A := by
  intro x hx hx1 y hy hy1
  apply le_antisymm
  · intro g hg
    exact ⟨pPrimeCoreOf_le_self _ hg.1, h y hy hy1 x hx hx1 hg⟩
  · intro g hg
    exact ⟨h x hx hx1 y hy hy1 ⟨hg.2, hg.1⟩, pPrimeCoreOf_le_self _ hg.2⟩

end Balance

end CFSG.GH74.GLS
