module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFusion
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

theorem eq_or_eq_mul_of_conj_eq' [Finite G] {L : Subgroup G} {t : G}
    (hLt : L ≤ centralizer ({t} : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {x l : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hl : l ∈ L)
    (hxl : ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) : x = l ∨ x = l * t := by
  have hlC : l⁻¹ * x ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := hxl y hy
    calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
      _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = l⁻¹ * x * y := by group
  have hz : l⁻¹ * x ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hlC, mul_mem (inv_mem (hLt hl)) hx⟩
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hz with h1 | h1
  · left
    calc x = l * (l⁻¹ * x) := by group
      _ = l := by rw [h1, mul_one]
  · right
    calc x = l * (l⁻¹ * x) := by group
      _ = l * t := by rw [h1]

theorem mul_mem_of_commute_sylow [Finite G] {L : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (U : Sylow 2 L) {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hgU : ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    t * (g⁻¹ * t * g) ∈ L := by
  set s := g⁻¹ * t * g with hs
  set β : MulAut L := L.normalizerMonoidHom ⟨s, hCN hgC⟩
  have hβ : ∀ l : L, ((β l : L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hCN hgC⟩ l
  obtain ⟨c, hc⟩ := hAutU U β fun u hu => Subtype.ext (by
    rw [hβ, ← hgU u hu, mul_inv_cancel_right])
  have hsc : ∀ y ∈ L, s * y * s⁻¹ = c * y * (c : G)⁻¹ := fun y hy => by
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hc
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [← hβ ⟨y, hy⟩, ← h]
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  rcases eq_or_eq_mul_of_conj_eq' hLt ht hKt hgC c.2 hsc with h | h
  · exact absurd hgU (hnot U g (by rw [← hs, h]; exact c.2))
  · have hct : (c : G) * t = t * c := mem_centralizer_singleton_iff.1 (hLt c.2)
    have e : t * s = c := by
      rw [h, ← mul_assoc, ← hct, mul_assoc, htt, mul_one]
    rw [e]
    exact c.2

variable [Finite G]

theorem exists_conj_eq_mul_of_two_dvd_index_of_autU {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hA : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      (∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) →
        t * (g⁻¹ * t * g) ∈ L)
    (h2 : 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({t} : Set G) with hMdef
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨U⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨P, hUP⟩ := (U.isPGroup'.map (inclusion hLt)).exists_le_sylow
  set S : Subgroup G := (P : Subgroup M).map M.subtype with hSdef
  have hSM : S ≤ M := map_subtype_le _
  have hmemS : ∀ y : M, (y : G) ∈ S ↔ y ∈ P := fun y => mem_map_iff_mem M.subtype_injective
  have hPS : S.subgroupOf M = P := by
    rw [hSdef, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  have hUS : ∀ u ∈ (U : Subgroup L), (u : G) ∈ S := fun u hu =>
    (hmemS (inclusion hLt u)).2 (hUP ⟨u, hu, rfl⟩)
  have hNS : ∀ x (hxM : x ∈ M), IsPGroup 2 (zpowers (⟨x, hxM⟩ : M)) →
      x ∈ normalizer (S : Set G) → x ∈ S := by
    intro x hxM hx2 hxN
    have hxN' : (⟨x, hxM⟩ : M) ∈ normalizer ((P : Subgroup M) : Set M) := by
      rw [← hPS, ← subgroupOf_normalizer_eq hSM, mem_subgroupOf]
      exact hxN
    have hxP := mem_inf.2 ⟨mem_zpowers (⟨x, hxM⟩ : M), hxN'⟩
    exact (hmemS _).2 (mem_inf.1 ((hx2.inf_normalizer_sylow P).le hxP)).2
  have htS : t ∈ S :=
    hNS t htM (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, ht, pow_one]))
      (F4Pilot.mem_normalizer_of_le_centralizer_singleton hSM)
  obtain ⟨Sst, hSS⟩ := (P.isPGroup'.map M.subtype).exists_le_sylow
  have hlt : S.subgroupOf Sst < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    exact Sst.not_dvd_index (h2.trans (index_dvd_of_le ((subgroupOf_eq_top.1 h).trans hSM)))
  have : Group.IsNilpotent Sst := Sst.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hSS, mem_subgroupOf] at hyN
  rw [mem_subgroupOf] at hyS
  set x : G := (y : G) with hxdef
  have hxtS : x⁻¹ * t * x ∈ S := (mem_normalizer_iff''.1 hyN t).1 htS
  have hcomm : ∀ s ∈ S, s * (x⁻¹ * t * x) = x⁻¹ * t * x * s := by
    intro s hs
    have h' : x * s * x⁻¹ * t = t * (x * s * x⁻¹) :=
      mem_centralizer_singleton_iff.1 (hSM ((mem_normalizer_iff.1 hyN _).1 hs))
    calc s * (x⁻¹ * t * x) = x⁻¹ * (x * s * x⁻¹ * t) * x := by group
      _ = x⁻¹ * (t * (x * s * x⁻¹)) * x := by rw [h']
      _ = x⁻¹ * t * x * s := by group
  have hzL : t * (x⁻¹ * t * x) ∈ L :=
    hA U x (hSM hxtS) fun u hu => hcomm u (hUS u hu)
  refine ⟨x, t * (x⁻¹ * t * x), hzL, by rw [← mul_assoc, htt, one_mul], ?_, U,
    fun u hu => ?_⟩
  · intro hz1
    have hxt : x⁻¹ * t * x = t := by
      rw [eq_inv_of_mul_eq_one_right hz1, inv_eq_of_mul_eq_one_right htt]
    have hxM : x ∈ M := by
      rw [hMdef, mem_centralizer_singleton_iff]
      calc x * t = x * (x⁻¹ * t * x) := by rw [hxt]
        _ = t * x := by group
    refine hyS (hNS x hxM ?_ hyN)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Sst.isPGroup' y
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, orderOf_mk, hxdef, orderOf_coe, hk])
  · have hs := hUS u hu
    have hst : (u : G) * t = t * u := mem_centralizer_singleton_iff.1 (hSM hs)
    calc (u : G) * (t * (x⁻¹ * t * x)) = t * (u * (x⁻¹ * t * x)) := by
          rw [← mul_assoc, hst, mul_assoc]
      _ = t * (x⁻¹ * t * x) * u := by rw [hcomm u hs]; simp only [mul_assoc]

omit [Finite G] in
theorem mem_sylow_of_le_centralizer {t : G} (ht : orderOf t = 2) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G)) : t ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htN : t ∈ normalizer ((S : Subgroup G) : Set G) :=
    F4Pilot.mem_normalizer_of_le_centralizer_singleton hSt
  exact (mem_inf.1 ((h2.inf_normalizer_sylow S).le (mem_inf.2 ⟨mem_zpowers t, htN⟩))).2

theorem mem_normalizer_of_forall_inv_conj_mem {S : Subgroup G} {g : G}
    (hg : ∀ y ∈ S, g⁻¹ * y * g ∈ S) : g ∈ normalizer (S : Set G) := by
  have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hg y hy
  have hcard : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Nat.card_congr (S.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).toEquiv.symm
  have heq : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    exact hg y hy
  · intro hy
    rw [← heq] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    have e : g⁻¹ * y' * g = g⁻¹ * y * g := by simpa [MulAut.conj_apply] using hyy'
    have hyy : y' = y := mul_left_cancel (mul_right_cancel e)
    rw [← hyy]
    exact hy'

theorem commutator_ne_top_of_sylow_le_centralizer {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htL : t ∉ L) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (habel : ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L)
    (hN : ∀ g ∈ normalizer ((S : Subgroup G) : Set G), t * (g⁻¹ * t * g) ∈ L) :
    commutator G ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal S habel
    (mem_sylow_of_le_centralizer ht S hSt) htL (by rw [sq, htt]) fun g hg => ?_
  have hg' : ∀ y ∈ (S : Subgroup G), g⁻¹ * y * g ∈ (S : Subgroup G) := fun y hy =>
    hg y (mem_inf.2 ⟨hy, hSt hy⟩)
  rw [htinv]
  exact hN g (mem_normalizer_of_forall_inv_conj_mem hg')

theorem exists_conj_eq_mul_of_commutator_eq_top (hperf : commutator G = ⊤) {L : Subgroup G}
    {t : G} (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      (∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) →
        t * (g⁻¹ * t * g) ∈ L :=
    fun U g hgC hgU => mul_mem_of_commute_sylow ht hLt hCN hKt hnot hAutU U hgC hgU
  by_cases h2 : 2 ∣ (centralizer ({t} : Set G)).index
  · exact exists_conj_eq_mul_of_two_dvd_index_of_autU ht hLt hA h2
  · exfalso
    obtain ⟨S, -, hSt⟩ := CFSG.SeitzReduction.exists_sylow_mem_le_of_not_dvd_index h2
      (mem_centralizer_singleton_iff.2 rfl) (ht.trans (pow_one 2).symm)
    obtain ⟨U₀⟩ : Nonempty (Sylow 2 L) := inferInstance
    have htL : t ∉ L := fun htL => hnot U₀ 1 (by simpa using htL) fun u _ => by
      simpa using (mem_centralizer_singleton_iff.1 (hLt u.2))
    refine commutator_ne_top_of_sylow_le_centralizer ht htL S hSt
      (habel S hSt) (fun g hg => ?_) hperf
    have htS := mem_sylow_of_le_centralizer ht S hSt
    have hgS : g⁻¹ * t * g ∈ (S : Subgroup G) := (mem_normalizer_iff''.1 hg t).1 htS
    have hcomm : ∀ s ∈ (S : Subgroup G), s * (g⁻¹ * t * g) = g⁻¹ * t * g * s := by
      intro s hs
      have hs' : g * s * g⁻¹ ∈ (S : Subgroup G) := (mem_normalizer_iff.1 hg s).1 hs
      have h' : g * s * g⁻¹ * t = t * (g * s * g⁻¹) :=
        mem_centralizer_singleton_iff.1 (hSt hs')
      calc s * (g⁻¹ * t * g) = g⁻¹ * (g * s * g⁻¹ * t) * g := by group
        _ = g⁻¹ * (t * (g * s * g⁻¹)) * g := by rw [h']
        _ = g⁻¹ * t * g * s := by group
    have hKn : (L.subgroupOf (centralizer ({t} : Set G))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hLt).2 hCN
    have hodd : ¬ 2 ∣ ((S : Subgroup G).subgroupOf L).index := by
      have h := CFSG.QuasiDihedralFusion.not_dvd_relIndex_of_normal (S.subtype hSt)
        (L.subgroupOf (centralizer ({t} : Set G)))
      rw [Sylow.coe_subtype] at h
      have e : (((S : Subgroup G).subgroupOf (centralizer ({t} : Set G))).subgroupOf
          (L.subgroupOf (centralizer ({t} : Set G)))).index =
            ((S : Subgroup G).subgroupOf L).index :=
        Subgroup.relIndex_subgroupOf hLt
      rwa [e] at h
    have hSLp : IsPGroup 2 ((S : Subgroup G).subgroupOf L) := S.isPGroup'.comap_subtype
    set U : Sylow 2 L := hSLp.toSylow hodd with hUdef
    have hUS : ∀ u ∈ (U : Subgroup L), (u : G) ∈ (S : Subgroup G) := by
      intro u hu
      rw [hUdef, IsPGroup.toSylow_coe] at hu
      exact Subgroup.mem_subgroupOf.1 hu
    exact hA U g (hSt hgS) fun u hu => hcomm u (hUS u hu)

theorem zmod_two_mul_eq_one : ∀ u : Multiplicative (ZMod 2), u ≠ 1 →
    ∀ v : Multiplicative (ZMod 2), v ≠ 1 → u * v = 1 := by
  decide

theorem exists_normal_index_two_or_conj_mem_of_min {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U) (hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y) :
    (∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∨
      ∃ g : G, g⁻¹ * x * g ∈ U ∧
        ∀ c ∈ T ⊓ centralizer ({x} : Set G),
          g⁻¹ * c * g ∈ T ⊓ centralizer ({g⁻¹ * x * g} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨x, hxT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hxT ht hxU htU⟩
  have hord2 : 2 ∣ orderOf x := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT (⟨x, hxT⟩ : T)
    have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hxT⟩ : T)).trans hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hx1 : x = 1 := orderOf_eq_one_iff.1 (hk'.trans (pow_zero 2))
      exact hxU (by rw [hx1]; exact U.one_mem)
    rw [hk']
    exact dvd_pow_self 2 hk0
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U := by
    intro g k hgT
    by_contra hgU
    have hle := hmin _ hgT hgU
    have hpow : (x ^ (2 * k)) ^ orderOf (x ^ 2) = 1 := by
      rw [pow_mul x 2 k, pow_right_comm (x ^ 2) k, pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf (g⁻¹ * x ^ (2 * k) * g) ∣ orderOf (x ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      have hc := conj_pow (a := g⁻¹) (b := x ^ (2 * k)) (i := orderOf (x ^ 2))
      rw [inv_inv] at hc
      rw [hc, hpow]
      group
    have h2 : orderOf (x ^ 2) = orderOf x / 2 := orderOf_pow_of_dvd (by norm_num) hord2
    have h3 : orderOf (g⁻¹ * x ^ (2 * k) * g) ≤ orderOf (x ^ 2) :=
      Nat.le_of_dvd (orderOf_pos _) hdvd
    have h4 := orderOf_pos x
    omega
  have hc : ∀ g : G, g⁻¹ * x * g ∈ T →
      CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 T (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ U ∨ x⁻¹ * (g⁻¹ * x * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * x * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hxT hgT hxU hgU)
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hxT hxU hb hc
    with ⟨N, hN, -, hNp, hxN⟩ | ⟨g, hg, -, hcall⟩
  · left
    have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hxN
      have h1 : (QuotientGroup.mk x : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM
    refine ⟨M.comap (QuotientGroup.mk' N), (Subgroup.normal_of_index_eq_two hMidx).comap _, ?_⟩
    exact (Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
      QuotientGroup.mk_surjective).trans hMidx
  · exact Or.inr ⟨g, hg, hcall⟩

theorem exists_normal_index_two_of_rigid {t : G} (ht : orderOf t = 2) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (χ : centralizer ({t} : Set G) →* Multiplicative (ZMod 2))
    (hχS : ∃ s : G, ∃ hs : s ∈ (S : Subgroup G), χ ⟨s, hSt hs⟩ ≠ 1)
    (hrig : ∀ g y : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      ∀ (hy : y ∈ centralizer ({t} : Set G)) (hgy : g * y * g⁻¹ ∈ centralizer ({t} : Set G)),
        y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y → χ ⟨y, hy⟩ = χ ⟨g * y * g⁻¹, hgy⟩) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := (S : Subgroup G) ⊓ χ.ker.map (centralizer ({t} : Set G)).subtype with hMdef
  have hmemM : ∀ y (hy : y ∈ (S : Subgroup G)), y ∈ M ↔ χ ⟨y, hSt hy⟩ = 1 := by
    intro y hy
    constructor
    · rintro ⟨-, ⟨z, hz, hzy⟩⟩
      have : z = ⟨y, hSt hy⟩ := Subtype.ext hzy
      rw [← this]
      exact hz
    · intro h
      exact ⟨hy, ⟨⟨y, hSt hy⟩, h, rfl⟩⟩
  have hMS : M ≤ (S : Subgroup G) := inf_le_left
  obtain ⟨s₀, hs₀, hχs₀⟩ := hχS
  have hMidx : M.relIndex (S : Subgroup G) = 2 := by
    rw [relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨s₀, hs₀, fun h => hχs₀ ((hmemM s₀ hs₀).1 h), fun b hb => ?_⟩
    have hmul : χ ⟨b * s₀, hSt (mul_mem hb hs₀)⟩ = χ ⟨b, hSt hb⟩ * χ ⟨s₀, hSt hs₀⟩ := by
      rw [← map_mul]
      rfl
    by_cases hbM : χ ⟨b, hSt hb⟩ = 1
    · exact Or.inr ((hmemM b hb).2 hbM)
    · left
      rw [hmemM _ (mul_mem hb hs₀), hmul]
      exact zmod_two_mul_eq_one _ hbM _ hχs₀
  classical
  have hex : ∃ k : ℕ, ∃ y ∈ (S : Subgroup G), y ∉ M ∧ orderOf y = k :=
    ⟨_, s₀, hs₀, fun h => hχs₀ ((hmemM s₀ hs₀).1 h), rfl⟩
  set k₀ := Nat.find hex with hk₀
  obtain ⟨x, hxS, hxM, hxk⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ (S : Subgroup G), y ∉ M → orderOf x ≤ orderOf y := by
    intro y hy hyM
    rw [hxk]
    exact Nat.find_min' hex ⟨y, hy, hyM, rfl⟩
  rcases exists_normal_index_two_or_conj_mem_of_min S.isPGroup' S.not_dvd_index hMS hMidx hxS hxM
    hmin with h | ⟨g, hgM, hcall⟩
  · exact h
  · exfalso
    have htS : t ∈ (S : Subgroup G) := mem_sylow_of_le_centralizer ht S hSt
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hSt hxS)
    have htC : t ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
      ⟨htS, mem_centralizer_singleton_iff.2 hxt.symm⟩
    obtain ⟨hgtS, hgtC⟩ := hcall t htC
    set y := g⁻¹ * x * g with hydef
    have hyS : y ∈ (S : Subgroup G) := hMS hgM
    have hgy : g * y * g⁻¹ = x := by rw [hydef]; group
    have hyt : y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y := (mem_centralizer_singleton_iff.1 hgtC).symm
    have h := hrig g y (hSt hgtS) (hSt hyS) (by rw [hgy]; exact hSt hxS) hyt
    have h1 : χ ⟨y, hSt hyS⟩ = 1 := (hmemM y hyS).1 hgM
    have h2 : χ ⟨g * y * g⁻¹, by rw [hgy]; exact hSt hxS⟩ = χ ⟨x, hSt hxS⟩ := by
      congr 1
      exact Subtype.ext hgy
    exact hxM ((hmemM x hxS).2 (by rw [← h2, ← h, h1]))

end CFSG.SeitzReduction.LinearPilot
