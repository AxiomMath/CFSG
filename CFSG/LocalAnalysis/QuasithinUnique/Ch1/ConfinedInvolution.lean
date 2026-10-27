module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentNormalization
public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.QuasithinUnique

open CFSG.Open
open scoped commutatorElement

section OddCore

variable {G : Type*} [Group G]

theorem oddCoreIn_le (H : Subgroup G) : oddCoreIn H ≤ H := Subgroup.map_subtype_le _

theorem le_normalizer_oddCoreIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro h hh _ ⟨y, hy, rfl⟩
  refine ⟨(⟨h, hh⟩ : H) * y * (⟨h, hh⟩ : H)⁻¹, ?_, rfl⟩
  exact (inferInstance : (fusionOddCore H).Normal).conj_mem y hy ⟨h, hh⟩

theorem odd_card_oddCoreIn [Finite G] (H : Subgroup G) : Odd (Nat.card (oddCoreIn H)) := by
  rw [oddCoreIn, Nat.card_congr ((fusionOddCore H).equivMapOfInjective H.subtype
    H.subtype_injective).toEquiv.symm]
  exact EscapingLocal.odd_card_oddCore H

theorem mem_oddCoreIn_iff (H : Subgroup G) (x : H) :
    (x : G) ∈ oddCoreIn H ↔ x ∈ CFSG.oddCore H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end OddCore

section FixedPointFree

variable {G : Type*} [Group G] [Finite G]

theorem inverts_and_commute_of_inf_centralizer_eq_bot {Y : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (hzY : z ∈ Subgroup.normalizer (Y : Set G))
    (hfix : Y ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) :
    (∀ y ∈ Y, z⁻¹ * y * z = y⁻¹) ∧ ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
  have hzinv : z⁻¹ = z := by
    have h1 : z * z = 1 := by rw [← sq]; exact hz2
    exact inv_eq_of_mul_eq_one_right h1
  let φ : MulAut Y := Y.normalizerMonoidHom ⟨z, hzY⟩
  have hφ : ∀ y : Y, ((φ y : Y) : G) = z * y * z⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨z, hzY⟩ y
  have hfpf : MonoidHom.FixedPointFree (⇑φ) := by
    intro y hy
    have h1 : (y : G) ∈ Y ⊓ Subgroup.centralizer ({z} : Set G) := by
      have := congrArg Subtype.val hy
      rw [hφ] at this
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (y : G) * z = z * y * z⁻¹ * z := by rw [this]
        _ = z * y := by group
    rw [hfix] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hinv : Function.Involutive (⇑φ) := by
    intro y
    apply Subtype.ext
    rw [hφ, hφ, hzinv]
    calc z * (z * (y : G) * z) * z = z ^ 2 * y * z ^ 2 := by simp [sq, mul_assoc]
      _ = y := by rw [hz2]; simp
  refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
  · have := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinv) ⟨y, hy⟩
    have h2 := congrArg Subtype.val this
    rw [hφ] at h2
    rw [hzinv]
    simpa [hzinv] using h2
  · have := MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinv ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this.eq

theorem CharTwo.eq_bot_of_odd_card {K Y : Subgroup G} (hK : CharTwo K) (hYK : Y ≤ K)
    (hYn : K ≤ Subgroup.normalizer (Y : Set G)) (hY : Odd (Nat.card Y)) : Y = ⊥ := by
  have hchar : CFSG.IsCharacteristicP 2 K := EscapingLocal.isCharacteristicP_of_charTwo hK
  have hN : (Y.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hYn
  have hcard : ¬ 2 ∣ Nat.card (Y.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
    exact hY.not_two_dvd_nat
  have hbot := (CFSG.characteristic_p_normal_prime_complement_trivial hchar).1 _ hN hcard
  have := Subgroup.map_subgroupOf_eq_of_le hYK
  rw [hbot, Subgroup.map_bot] at this
  exact this.symm

theorem oddCoreIn_inf_eq_bot {H A : Subgroup G} (hA : CharTwo A) (hAH : A ≤ H) :
    oddCoreIn H ⊓ A = ⊥ := by
  refine hA.eq_bot_of_odd_card inf_le_right ?_ ?_
  · exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf A _ _
      (hAH.trans (le_normalizer_oddCoreIn H)) Subgroup.le_normalizer
  · have hdvd : Nat.card (oddCoreIn H ⊓ A : Subgroup G) ∣ Nat.card (oddCoreIn H) :=
      Subgroup.card_dvd_of_le inf_le_left
    exact (odd_card_oddCoreIn H).of_dvd_nat hdvd

theorem confined_involution_inverts_oddCoreIn {H A : Subgroup G} (hA : CharTwo A) (hAH : A ≤ H)
    {z : G} (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hC : H ⊓ Subgroup.centralizer ({z} : Set G) ≤ A) :
    oddCoreIn H ⊓ A = ⊥ ∧ oddCoreIn H ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ ∧
      (∀ y ∈ oddCoreIn H, z⁻¹ * y * z = y⁻¹) ∧
      ∀ x ∈ oddCoreIn H, ∀ y ∈ oddCoreIn H, x * y = y * x := by
  have hYA := oddCoreIn_inf_eq_bot hA hAH
  have hYC : oddCoreIn H ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hYA]
    exact fun y hy => ⟨hy.1, hC ⟨oddCoreIn_le H hy.1, hy.2⟩⟩
  obtain ⟨hinv, hcomm⟩ := inverts_and_commute_of_inf_centralizer_eq_bot hz2
    (le_normalizer_oddCoreIn H hzH) hYC
  exact ⟨hYA, hYC, hinv, hcomm⟩

end FixedPointFree

section CentralSylow

variable {H : Type*} [Group H] [Finite H]

theorem central_sylow_normalizes_components_of_abelian_pPrimeCore {p : ℕ} [Fact p.Prime]
    (hab : ∀ x ∈ CFSG.pPrimeCore p H, ∀ y ∈ CFSG.pPrimeCore p H, x * y = y * x)
    (S : Sylow p H) {z : H} (hz : z ∈ Subgroup.centralizer ((S : Subgroup H) : Set H))
    {L : Subgroup H} (hL : CFSG.IsComponent L) : z ∈ Subgroup.normalizer (L : Set H) := by
  by_contra hnorm
  let M : Subgroup H := L.map (MulAut.conj z⁻¹).toMonoidHom
  have hmemM : ∀ x : H, x ∈ M ↔ z * x * z⁻¹ ∈ L := mem_map_conj_inv_iff L z
  have hM : CFSG.IsComponent M := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z⁻¹) hL
  have hne : L ≠ M := fun h =>
    hnorm (Subgroup.mem_normalizer_iff.mpr fun x => (SetLike.ext_iff.mp h x).trans (hmemM x))
  have hLM : ⁅L, M⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hM).resolve_left hne
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_inf_of_subnormal S hL.2
  have : Group.IsPerfect L := hL.1.1
  have hTZ : (T : Subgroup L) ≤ Subgroup.center L := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    have htS : (t : H) ∈ (S : Subgroup H) ⊓ L := hT ▸ Subgroup.mem_map_of_mem _ ht
    have hfix : z * (t : H) * z⁻¹ = t := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hz t htS.1).symm
    have htM : (t : H) ∈ M := (hmemM t).mpr (by rw [hfix]; exact t.2)
    have hg := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLM g.2) t htM
    exact Subtype.ext hg.symm
  have hT1 := sylow_eq_bot_of_le_center T hTZ
  have hπ : CFSG.IsPiSubgroup {q : Nat.Primes | q.val ≠ p} L := fun q hq hqp =>
    T.ne_bot_of_dvd_card (hqp ▸ hq) hT1
  have htop : CFSG.piCore {q : Nat.Primes | q.val ≠ p} L = ⊤ :=
    top_le_iff.mp (CFSG.LocalCores.le_piCore_of_normal inferInstance
      (by rwa [CFSG.IsPiSubgroup, Subgroup.card_top]))
  have hcore := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ p} hL.2
  rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hcore
  have hLle : L ≤ CFSG.pPrimeCore p H := by
    rw [CFSG.pPrimeCore_eq_piCore]
    exact inf_eq_left.mp hcore.symm
  have hsolv : Group.IsSolvable L :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hab a (hLle a.2) b (hLle b.2))
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  exact Group.IsPerfect.not_isSolvable L hsolv

end CentralSylow

section ComponentAction

variable {G : Type*} [Group G] [Finite G]

theorem not_le_of_isComponentIn_of_charTwo {H A L : Subgroup G} (hA : CharTwo A) (hAH : A ≤ H)
    (hL : IsComponentIn L H) : ¬ L ≤ A := by
  intro hLA
  have hlayer : CFSG.layer A = ⊥ :=
    CFSG.layer_eq_bot_of_isCharacteristicP A 2 (EscapingLocal.isCharacteristicP_of_charTwo hA)
  have hquasi : CFSG.IsQuasisimple (L.subgroupOf A) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hL.1).trans (Subgroup.subgroupOfEquivOfLe hLA).symm) hL.2.1
  have hsn : (L.subgroupOf A).IsSubnormal := by
    have := hL.2.2.comap (Subgroup.inclusion hAH)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hle : L.subgroupOf A ≤ CFSG.layer A := le_sSup ⟨hquasi, hsn⟩
  rw [hlayer] at hle
  have : Nontrivial (L.subgroupOf A) := CFSG.LocalCores.isQuasisimple_nontrivial hquasi
  obtain ⟨x, hx⟩ := exists_ne (1 : L.subgroupOf A)
  exact hx (Subtype.ext (Subgroup.mem_bot.mp (hle x.2)))

theorem confined_sylow_central_involution_component_action {H A S : Subgroup G} (hA : CharTwo A)
    (hAH : A ≤ H) (hS : IsSylowTwoOf S H) {z : G} (hzS : z ∈ S)
    (hzc : z ∈ Subgroup.centralizer (S : Set G)) (hz2 : z ^ 2 = 1)
    (hC : H ⊓ Subgroup.centralizer ({z} : Set G) ≤ A) {L : Subgroup G}
    (hL : IsComponentIn L H) :
    z ∈ Subgroup.normalizer (L : Set G) ∧ ¬ L ≤ A ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧
      CharTwo (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hzH : z ∈ H := hS.1 hzS
  obtain ⟨-, -, -, hab⟩ := confined_involution_inverts_oddCoreIn hA hAH hzH hz2 hC
  have hwL : z ∈ Subgroup.normalizer (L : Set G) := by
    have hS2 : IsPGroup 2 (S.subgroupOf H) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    let P : Sylow 2 H := hS2.toSylow hS.2.2
    have hwz : (⟨z, hzH⟩ : H) ∈ Subgroup.centralizer ((P : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (y : G) (show (y : G) ∈ S from hy))
    have hab' : ∀ x ∈ CFSG.pPrimeCore 2 H, ∀ y ∈ CFSG.pPrimeCore 2 H, x * y = y * x := by
      intro x hx y hy
      rw [← EscapingLocal.oddCore_eq_pPrimeCore] at hx hy
      exact Subtype.ext (hab _ ((mem_oddCoreIn_iff H x).mpr hx) _ ((mem_oddCoreIn_iff H y).mpr hy))
    have hnormH := central_sylow_normalizes_components_of_abelian_pPrimeCore hab' P hwz hL.2
    have h2 : z ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H)).map H.subtype :=
      ⟨_, hnormH, rfl⟩
    rw [map_subtype_normalizer hL.1] at h2
    exact h2.2
  have hLA : ¬ L ≤ A := not_le_of_isComponentIn_of_charTwo hA hAH hL
  have hDL : ⁅L, Subgroup.zpowers z⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := (Subgroup.zpowers_le.mpr hwL) hy
    have h1 : y * x⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (L.inv_mem hx)
    have h2 : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact L.mul_mem hx h1
  have hDnorm : ((⁅L, Subgroup.zpowers z⁆ : Subgroup G).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr
      (Subgroup.normalizer_commutator_ge_left L _)
  have hQ : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hcomm : ⁅L, Subgroup.zpowers z⁆ = L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hDnorm with htop | hcent
    · refine le_antisymm hDL fun x hx => ?_
      have : (⟨x, hx⟩ : L) ∈ (⁅L, Subgroup.zpowers z⁆ : Subgroup G).subgroupOf L :=
        htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hDcent : ⁅⁅L, Subgroup.zpowers z⁆, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro d hd'
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hdc : (⟨d, hDL hd'⟩ : L) ∈ Subgroup.center L :=
          hcent (show (⟨d, hDL hd'⟩ : L) ∈ (⁅L, Subgroup.zpowers z⁆ : Subgroup G).subgroupOf L
            from hd')
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hdc ⟨l, hl⟩)
      have h1 : ⁅L, Subgroup.zpowers z⁆ = ⊥ :=
        CFSG.LocalCores.perfect_double_commutator hQ.1 hDcent
      have h2 : L ≤ Subgroup.centralizer ({z} : Set G) := by
        intro x hx
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hx
        exact Subgroup.centralizer_le
          (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z)) this
      exact hLA fun x hx => hC ⟨hL.1 hx, h2 hx⟩
  have hzA : z ∈ A := hC ⟨hzH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzpA : Subgroup.zpowers z ≤ A := Subgroup.zpowers_le.mpr hzA
  have hzpp : IsPGroup 2 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hz2]
  have hK := hA.inf_centralizer hzpA hzpp
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hK
  have hXK : L ⊓ Subgroup.centralizer ({z} : Set G) ≤ A ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun x hx => ⟨hC ⟨hL.1 hx.1, hx.2⟩, hx.2⟩
  have hKH : A ⊓ Subgroup.centralizer ({z} : Set G) ≤ H := inf_le_left.trans hAH
  have hsn : (L.subgroupOf (A ⊓ Subgroup.centralizer ({z} : Set G))).IsSubnormal := by
    have := hL.2.2.comap (Subgroup.inclusion hKH)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hsn' : ((L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf
      (A ⊓ Subgroup.centralizer ({z} : Set G))).IsSubnormal := by
    have heq : (L ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf
        (A ⊓ Subgroup.centralizer ({z} : Set G)) =
        L.subgroupOf (A ⊓ Subgroup.centralizer ({z} : Set G)) := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩
    rw [heq]
    exact hsn
  exact ⟨hwL, hLA, hcomm, CharTwo.of_isSubnormal hK hXK hsn'⟩

end ComponentAction

end CFSG.QuasithinUnique
