module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Setup

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

section Sylow

variable {G : Type} [Group G]

theorem mem_conjSub_iff_inv {g x : G} {X : Subgroup G} :
    x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conj_mem_oddCoreOf {H : Subgroup G} {g : G} (hg : g ∈ H) {x : G}
    (hx : x ∈ AltStdSec.oddCoreOf H) : g * x * g⁻¹ ∈ AltStdSec.oddCoreOf H := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem exists_conj_eq_of_sylow [Finite G] {T O : Subgroup G}
    (hTN : T ≤ normalizer (O : Set G)) (hT : IsPGroup 2 T) (hO : Nat.Coprime 2 (Nat.card O))
    (S : Sylow 2 ↥(T ⊔ O)) :
    ∃ o ∈ O, (S : Subgroup ↥(T ⊔ O)).map (T ⊔ O).subtype = conjSub o T := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hOT : O ⊓ T = ⊥ :=
    inf_eq_bot_of_coprime (by rw [ha]; exact (Nat.Coprime.pow_left a hO).symm)
  have hcard : Nat.card ↥(T ⊔ O) = Nat.card T * Nat.card O := by
    rw [sup_comm, card_sup_of_inf_eq_bot hTN hOT, mul_comm]
  have hTK : T ≤ T ⊔ O := le_sup_left
  have hT' : IsPGroup 2 (T.subgroupOf (T ⊔ O)) := hT.of_equiv (subgroupOfEquivOfLe hTK).symm
  have hidx : ¬ 2 ∣ (T.subgroupOf (T ⊔ O)).index := by
    have h1 := Subgroup.card_mul_index (T.subgroupOf (T ⊔ O))
    rw [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv, hcard] at h1
    have h2 : (T.subgroupOf (T ⊔ O)).index = Nat.card O :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    obtain ⟨m, hm⟩ := Nat.coprime_two_left.1 hO
    omega
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥(T ⊔ O) (hT'.toSylow hidx) S
  have hmemS : ∀ x : ↥(T ⊔ O), x ∈ (S : Subgroup ↥(T ⊔ O)) ↔ (k : G)⁻¹ * x * k ∈ T := by
    intro x
    rw [← hk, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, mem_pointwise_smul_iff_inv_smul_mem,
      mem_subgroupOf, MulAut.smul_def, MulAut.conj_inv_apply]
    rfl
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left O T hTN
  have hk' : (k : G) ∈ (O : Set G) * (T : Set G) := by
    rw [← hm, sup_comm]
    exact k.2
  obtain ⟨o, ho, t, ht, hot⟩ := Set.mem_mul.1 hk'
  refine ⟨o, ho, ?_⟩
  ext y
  rw [mem_conjSub_iff_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (hmemS x).1 hx
    rw [← hot] at hx'
    have : o⁻¹ * (T ⊔ O).subtype x * o = t * ((o * t)⁻¹ * x * (o * t)) * t⁻¹ := by
      rw [Subgroup.coe_subtype]
      group
    rw [this]
    exact mul_mem (mul_mem ht hx') (inv_mem ht)
  · intro hy
    have hyK : y ∈ T ⊔ O := by
      have : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (mem_sup_right ho) (mem_sup_left hy)) (inv_mem (mem_sup_right ho))
    refine ⟨⟨y, hyK⟩, (hmemS _).2 ?_, rfl⟩
    rw [← hot]
    show (o * t)⁻¹ * y * (o * t) ∈ T
    have : (o * t)⁻¹ * y * (o * t) = t⁻¹ * (o⁻¹ * y * o) * t := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem ht) hy) ht

theorem exists_conj_eq_of_le [Finite G] {T O K : Subgroup G}
    (hTN : T ≤ normalizer (O : Set G)) (hT : IsPGroup 2 T) (hO : Nat.Coprime 2 (Nat.card O))
    (hK : K ≤ T ⊔ O) (hKp : IsPGroup 2 K) (hKc : Nat.card K = Nat.card T) :
    ∃ o ∈ O, K = conjSub o T := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hOT : O ⊓ T = ⊥ :=
    inf_eq_bot_of_coprime (by rw [ha]; exact (Nat.Coprime.pow_left a hO).symm)
  have hcard : Nat.card ↥(T ⊔ O) = Nat.card T * Nat.card O := by
    rw [sup_comm, card_sup_of_inf_eq_bot hTN hOT, mul_comm]
  have hK' : IsPGroup 2 (K.subgroupOf (T ⊔ O)) := hKp.of_equiv (subgroupOfEquivOfLe hK).symm
  have hidx : ¬ 2 ∣ (K.subgroupOf (T ⊔ O)).index := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf (T ⊔ O))
    rw [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv, hKc, hcard] at h1
    have h2 : (K.subgroupOf (T ⊔ O)).index = Nat.card O :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    obtain ⟨m, hm⟩ := Nat.coprime_two_left.1 hO
    omega
  obtain ⟨o, ho, hSo⟩ := exists_conj_eq_of_sylow hTN hT hO (hK'.toSylow hidx)
  refine ⟨o, ho, ?_⟩
  rw [← hSo, IsPGroup.toSylow_coe, subgroupOf_map_subtype, inf_eq_left.2 hK]

theorem exists_cent_conj {O T : Subgroup G} {z o : G} (hz : z * z = 1)
    (hzO : ∀ x ∈ O, z * x * z⁻¹ ∈ O) (hO : ∀ x ∈ O, Odd (orderOf x))
    (hzT : z ∈ normalizer (T : Set G)) (ho : o ∈ O)
    (hzT' : z ∈ normalizer (conjSub o T : Set G)) :
    ∃ c ∈ O, c * z = z * c ∧ conjSub c T = conjSub o T := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hz'T : o⁻¹ * z * o ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    have h1 := (mem_normalizer_iff.1 hzT') (o * t * o⁻¹)
    rw [mem_conjSub_iff_inv, mem_conjSub_iff_inv] at h1
    have e1 : o⁻¹ * (o * t * o⁻¹) * o = t := by group
    have e2 : o⁻¹ * (z * (o * t * o⁻¹) * z⁻¹) * o = o⁻¹ * z * o * t * (o⁻¹ * z * o)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  obtain ⟨u, hu⟩ : ∃ u, u = o⁻¹ * z * o * z := ⟨_, rfl⟩
  have huO : u ∈ O := by
    have : u = o⁻¹ * (z * o * z⁻¹) := by
      rw [hu, hzi]
      group
    rw [this]
    exact mul_mem (inv_mem ho) (hzO o ho)
  have huT : u ∈ normalizer (T : Set G) := by
    rw [hu]
    exact mul_mem hz'T hzT
  have hinv : z * u * z⁻¹ = u⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    calc u * (z * u * z⁻¹) = o⁻¹ * z * o * (z * z) * o⁻¹ * z * o := by
          rw [hu]
          group
      _ = o⁻¹ * z * o * 1 * o⁻¹ * z * o := by rw [hz]
      _ = o⁻¹ * (z * z) * o := by group
      _ = 1 := by
          rw [hz]
          group
  obtain ⟨k, hk⟩ := hO u huO
  have hu1 : u ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one u
  obtain ⟨r, hr⟩ : ∃ r, r = u ^ (k + 1) := ⟨_, rfl⟩
  have hrO : r ∈ O := by
    rw [hr]
    exact pow_mem huO _
  have hrT : r ∈ normalizer (T : Set G) := by
    rw [hr]
    exact pow_mem huT _
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    rw [hr, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  have hzr' : z * r⁻¹ = r * z := by
    have h2 : z * r⁻¹ * z⁻¹ = r := by
      calc z * r⁻¹ * z⁻¹ = (z * r * z⁻¹)⁻¹ := by group
        _ = r := by rw [hzr, inv_inv]
    calc z * r⁻¹ = z * r⁻¹ * z⁻¹ * z := by group
      _ = r * z := by rw [h2]
  have hrr : r * r = u := by
    rw [hr, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ u (2 * k + 1),
      hu1, one_mul]
  have hrz : r * z * r⁻¹ = o⁻¹ * z * o := by
    calc r * z * r⁻¹ = r * (z * r⁻¹) := by group
      _ = r * (r * z) := by rw [hzr']
      _ = r * r * z := by group
      _ = u * z := by rw [hrr]
      _ = o⁻¹ * z * o * (z * z) := by
          rw [hu]
          group
      _ = o⁻¹ * z * o := by rw [hz, mul_one]
  refine ⟨o * r, mul_mem ho hrO, ?_, ?_⟩
  · have h3 : o * r * z * (o * r)⁻¹ = z := by
      calc o * r * z * (o * r)⁻¹ = o * (r * z * r⁻¹) * o⁻¹ := by group
        _ = z := by
            rw [hrz]
            group
    calc o * r * z = o * r * z * (o * r)⁻¹ * (o * r) := by group
      _ = z * (o * r) := by rw [h3]
  · ext y
    rw [mem_conjSub_iff_inv, mem_conjSub_iff_inv]
    have e : (o * r)⁻¹ * y * (o * r) = r⁻¹ * (o⁻¹ * y * o) * r := by group
    rw [e]
    exact ((mem_normalizer_iff''.1 hrT) (o⁻¹ * y * o)).symm

end Sylow

section Start

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem cover_of_N0Data (c : Config G L Q n θ z) {T : Subgroup G} (hT : N0Data θ c.hn8 z T)
    (hTp : IsPGroup 2 T) (M : GL (Fin 3) (ZMod 2)) :
    ∃ g ∈ KA L z T, ∀ v : Fin 3 → ZMod 2,
      g * epsV θ c.hn8 v * g⁻¹ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  set N := N0 θ c.hn8 z with hN
  set O := AltStdSec.oddCoreOf N with hO
  have hON : O ≤ N := Subgroup.map_subtype_le _
  have hOconj : ∀ g ∈ N, ∀ x ∈ O, g * x * g⁻¹ ∈ O := fun g hg x hx => conj_mem_oddCoreOf hg hx
  have hOodd : Nat.Coprime 2 (Nat.card O) := coprime_card_oddCoreOf N
  have hOord : ∀ x ∈ O, Odd (orderOf x) := by
    intro x hx
    have h1 : orderOf x ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (Nat.coprime_two_left.1 hOodd) h1
  have hTN : T ≤ N := hT.le
  have hTO : T ≤ normalizer (O : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hOconj t (hTN ht) x hx, fun hx => ?_⟩
    have := hOconj t⁻¹ (inv_mem (hTN ht)) _ hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at this
  have hzN : z ∈ N := Subgroup.le_normalizer (N0.z_mem_B0 c.hn8 c)
  have hEN : E θ c.hn8 ≤ N := le_sup_left.trans Subgroup.le_normalizer
  set κ := ModIso.kap θ c.hn8 M with hκ
  have hκL : κ ∈ L := ModIso.kap_mem_L θ c.hn8 M
  have hκN : κ ∈ N :=
    N0.mem_N0_of_mem_L c.hn8 c hκL fun i => ⟨_, ModIso.kap_conj_eps θ c.hn8 M i⟩
  have hκz : κ * z = z * κ := N0.comm_z_of_mem_L c hκL
  have hK : conjSub κ T ≤ T ⊔ O := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hT.normal κ hκN t ht
  have hKp : IsPGroup 2 (conjSub κ T) := hTp.map _
  have hKc : Nat.card (conjSub κ T) = Nat.card T :=
    card_map_of_injective (f := (MulAut.conj κ).toMonoidHom) (MulAut.conj κ).injective
  obtain ⟨o, ho, hKo⟩ := exists_conj_eq_of_le hTO hTp hOodd hK hKp hKc
  have hzK : z ∈ normalizer (conjSub o T : Set G) := by
    rw [← hKo, mem_normalizer_iff]
    intro x
    rw [mem_conjSub_iff_inv, mem_conjSub_iff_inv]
    have e : κ⁻¹ * (z * x * z⁻¹) * κ = z * (κ⁻¹ * x * κ) * z⁻¹ := by
      have hκz' : κ⁻¹ * z = z * κ⁻¹ := by
        calc κ⁻¹ * z = κ⁻¹ * (z * κ) * κ⁻¹ := by group
          _ = κ⁻¹ * (κ * z) * κ⁻¹ := by rw [hκz]
          _ = z * κ⁻¹ := by group
      calc κ⁻¹ * (z * x * z⁻¹) * κ = (κ⁻¹ * z) * x * (z⁻¹ * κ) := by group
        _ = (z * κ⁻¹) * x * (κ * z⁻¹) := by
            rw [hκz', show z⁻¹ * κ = κ * z⁻¹ by
              calc z⁻¹ * κ = z⁻¹ * (κ * z) * z⁻¹ := by group
                _ = z⁻¹ * (z * κ) * z⁻¹ := by rw [hκz]
                _ = κ * z⁻¹ := by group]
        _ = z * (κ⁻¹ * x * κ) * z⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 hT.norm _
  obtain ⟨c₀, hc₀O, hc₀z, hc₀T⟩ :=
    exists_cent_conj (z_mul_self c) (hOconj z hzN) hOord hT.norm ho hzK
  rw [← hKo] at hc₀T
  have hc₀N : c₀ ∈ N := hON hc₀O
  have hc₀C : c₀ ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hc₀z
  have hc₀free : c₀ ∈ Lfree L z := mem_Lfree_of_N0_of_odd c ⟨hc₀N, hc₀C⟩ (hOord c₀ hc₀O)
  have hc₀E : ∀ v, c₀ * epsV θ c.hn8 v = epsV θ c.hn8 v * c₀ := by
    intro v
    set e := epsV θ c.hn8 v with he
    have heE : e ∈ E θ c.hn8 := epsV_mem_E θ c.hn8 v
    have hc₀NL : c₀ ∈ normalizer (L : Set G) :=
      AltStdCycTwo.cent_le_normalizer c.ot.std c.ot.cyc hc₀C
    have h1 : c₀ * e * c₀⁻¹ ∈ E θ c.hn8 :=
      ModIso.mem_E_of_mem_sup c ((mem_normalizer_iff.1 hc₀N e).1 (mem_sup_left heE))
        ((mem_normalizer_iff.1 hc₀NL e).1 (epsV_mem_L θ c.hn8 v))
    have h2 : c₀ * e * c₀⁻¹ * e⁻¹ ∈ E θ c.hn8 := mul_mem h1 (inv_mem heE)
    have h3 : c₀ * e * c₀⁻¹ * e⁻¹ ∈ O := by
      have : c₀ * e * c₀⁻¹ * e⁻¹ = c₀ * (e * c₀⁻¹ * e⁻¹) := by group
      rw [this]
      exact mul_mem hc₀O (hOconj e (hEN heE) _ (inv_mem hc₀O))
    have h4 : c₀ * e * c₀⁻¹ * e⁻¹ = 1 := by
      set x := c₀ * e * c₀⁻¹ * e⁻¹
      have hx2 : x ^ 2 = 1 := sq_eq_one_of_mem_E θ c.hn8 h2
      have hxo := hOord x h3
      have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hxo
        exact absurd hxo (by decide)
    calc c₀ * e = c₀ * e * c₀⁻¹ * e⁻¹ * (e * c₀) := by group
      _ = e * c₀ := by rw [h4, one_mul]
  refine ⟨c₀⁻¹ * κ, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, fun v => ?_⟩
  · rw [mem_normalizer_iff]
    intro t
    have e : c₀⁻¹ * κ * t * (c₀⁻¹ * κ)⁻¹ = c₀⁻¹ * (κ * t * κ⁻¹) * c₀ := by group
    rw [e, ← inv_inv c₀, ← mem_conjSub_iff_inv, inv_inv, hc₀T, mem_conjSub_iff_inv]
    rw [show κ⁻¹ * (κ * t * κ⁻¹) * κ = t by group]
  · rw [mem_centralizer_singleton_iff]
    have hc₀z' : c₀⁻¹ * z = z * c₀⁻¹ := by
      calc c₀⁻¹ * z = c₀⁻¹ * (z * c₀) * c₀⁻¹ := by group
        _ = c₀⁻¹ * (c₀ * z) * c₀⁻¹ := by rw [hc₀z]
        _ = z * c₀⁻¹ := by group
    calc c₀⁻¹ * κ * z = c₀⁻¹ * (κ * z) := by group
      _ = c₀⁻¹ * (z * κ) := by rw [hκz]
      _ = (c₀⁻¹ * z) * κ := by group
      _ = z * (c₀⁻¹ * κ) := by rw [hc₀z']; group
  · exact mul_mem (inv_mem hc₀free) (mem_sup_left hκL)
  · have e : c₀⁻¹ * κ * epsV θ c.hn8 v * (c₀⁻¹ * κ)⁻¹ =
        c₀⁻¹ * (κ * epsV θ c.hn8 v * κ⁻¹) * c₀ := by group
    rw [e, hκ, kap_conj_epsV, mul_assoc, ← hc₀E, ← mul_assoc, inv_mul_cancel, one_mul]

theorem levelDatum_of_N0Data (c : Config G L Q n θ z) {T : Subgroup G}
    (hT : N0Data θ c.hn8 z T) (φ : T ≃* Multiplicative (Fin 3 → ZMod 4)) :
    LevelDatum θ c.hn8 z 2 T := by
  let φ' : T ≃* Multiplicative (Fin 3 → ZMod (2 ^ 2)) := φ
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy => comm_of_coords φ' hx hy
  have hTcard : Nat.card T = 2 ^ 6 := card_of_coords φ'
  have hTp : IsPGroup 2 T := IsPGroup.of_card hTcard
  have hsq : ∀ e ∈ E θ c.hn8, ∃ x ∈ T, x ^ 2 = e := by
    intro e he
    obtain ⟨x, rfl⟩ := exists_el_eq φ' (hT.E_le he)
    have h2 : el φ' x ^ 2 = 1 := sq_eq_one_of_mem_E θ c.hn8 he
    rw [← el_nsmul, el_eq_one_iff] at h2
    have hx : ∀ i, ∃ b : ZMod 2, x i = 2 ^ (2 - 1) * (b.val : ZMod (2 ^ 2)) := by
      intro i
      refine (Homo.two_mul_eq_zero_iff (by norm_num) (x i)).1 ?_
      have := congrFun h2 i
      simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply] using this
    choose b hb using hx
    refine ⟨el φ' (fun i => ((b i).val : ZMod (2 ^ 2))), el_mem φ' _, ?_⟩
    rw [← el_nsmul]
    congr 1
    funext i
    rw [hb i, Pi.smul_apply, nsmul_eq_mul]
    norm_num
  obtain ⟨ι, hι⟩ := coords_of_sq (ecoords_iotaE θ c.hn8) (A' := T) hTc hsq
    (by rw [hTcard, card_E]; norm_num)
  have hι2 : ECoords θ c.hn8 2 T ι := hι
  have hcov := cover_of_N0Data c hT hTp
  have hzT : ∀ a ∈ T, z * a * z⁻¹ ∈ T := fun a ha => (mem_normalizer_iff.1 hT.norm a).1 ha
  have hΓ : ∀ a ∈ T, a * (z * a * z⁻¹) ∈ E θ c.hn8 := by
    intro a ha
    rw [← hT.cent]
    refine Subgroup.mem_inf.2 ⟨mul_mem ha (hzT a ha), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm := hTc a ha _ (hzT a ha)
    have hzz := z_mul_self c
    have hzi := z_inv c
    calc a * (z * a * z⁻¹) * z = a * z * a := by group
      _ = (z * z) * a * z⁻¹ * a := by rw [hzz, one_mul, hzi]
      _ = z * ((z * a * z⁻¹) * a) := by group
      _ = z * (a * (z * a * z⁻¹)) := by rw [hcomm]
  have hcov' : ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ normalizer (T : Set G) ⊓ centralizer ({z} : Set G),
      ∀ v, g * epsV θ c.hn8 v * g⁻¹ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) :=
    fun M => by
      obtain ⟨g, hg, hgv⟩ := hcov M
      exact ⟨g, hg.1, hgv⟩
  rcases zact_of_M1 hι2 hzT hΓ (x2 := x2G) (y2 := y2G) M1 hcov' with h1 | h1
  · exact ⟨le_rfl, hT.E_le, ⟨ι, hι2.toAdd_eps⟩, Or.inl h1, hcov⟩
  · exfalso
    have hle : T ≤ E θ c.hn8 := by
      intro a ha
      rw [← hT.cent]
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h2 : z * a * z⁻¹ = a := by
        rw [h1 a ha, show (2 : ℕ) ^ (2 - 1) = 2 by norm_num, sq]
        group
      calc a * z = z * a * z⁻¹ * z := by rw [h2]
        _ = z * a := by group
    have := Subgroup.card_le_of_le hle
    rw [hTcard, card_E] at this
    norm_num at this

theorem g2Start_holds : G2Start := by
  intro G _ _ L Q n θ z c T hT hφ
  obtain ⟨φ⟩ := hφ
  exact levelDatum_of_N0Data c hT φ

end Start

end CFSG.OddStandard.AltStdSmall4.G2
