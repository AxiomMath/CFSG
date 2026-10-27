module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionGeneric
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddCentralizer

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms CFSG.EvenSmallLie
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_centralizer_singleton_of_mem_centralizer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) : L ≤ centralizer ({t} : Set G) :=
  fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)

section Commutators

theorem commutator_mem_of_isCyclic_outer {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hOut : IsCyclic (Outer L)) :
    ∀ y ∈ centralizer ({t} : Set G), ∀ z ∈ centralizer ({t} : Set G),
      y * z * y⁻¹ * z⁻¹ ∈ L := by
  set A := centralizer ({t} : Set G) with hAdef
  have hLA : L ≤ A := le_centralizer_singleton_of_mem_centralizer htC
  set N : Subgroup A := L.subgroupOf A with hNdef
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hLA).2 hCN
  set φ : A →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp (L.normalizerMonoidHom.comp (inclusion hCN)) with hφ
  have hφ1 : ∀ a : A, φ a = 1 ↔ ∃ l : L, ∀ y ∈ L, (a : G) * y * (a : G)⁻¹ = l * y * (l : G)⁻¹ := by
    intro a
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, fun y hy => ?_⟩
      have h3 := congrArg (fun β : MulAut L => ((β ⟨y, hy⟩ : L) : G)) hl
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [h3]
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    · rintro ⟨l, hl⟩
      refine ⟨l, ?_⟩
      ext y
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, coe_inclusion]
      exact (hl y y.2).symm
  have hNφ : N ≤ φ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker, hφ1]
    exact ⟨⟨a, mem_subgroupOf.1 ha⟩, fun y _ => rfl⟩
  set f : A ⧸ N →* Outer L := QuotientGroup.lift N φ hNφ with hf
  have hker : f.ker ≤ center (A ⧸ N) := by
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, hf, QuotientGroup.lift_mk, hφ1] at hq
    obtain ⟨l, hl⟩ := hq
    rcases F4Pilot.eq_or_eq_mul_of_conj_eq htC ht hK a.2 l.2 hl with h | h
    · have ha : a ∈ N := mem_subgroupOf.2 (by rw [h]; exact l.2)
      rw [(QuotientGroup.eq_one_iff a).2 ha]
      exact one_mem _
    · have hmk : ((a : A) : A ⧸ N) = ((⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : A) : A ⧸ N) := by
        rw [QuotientGroup.eq]
        refine mem_subgroupOf.2 ?_
        have htt : t⁻¹ = t := by
          rw [inv_eq_iff_mul_eq_one, ← sq, ← ht, pow_orderOf_eq_one]
        have hlt' : (l : G)⁻¹ * t = t * (l : G)⁻¹ := by
          have hlt : (l : G) * t = t * l := mem_centralizer_iff.1 htC l l.2
          calc (l : G)⁻¹ * t = (l : G)⁻¹ * (t * l) * (l : G)⁻¹ := by group
            _ = (l : G)⁻¹ * (l * t) * (l : G)⁻¹ := by rw [hlt]
            _ = t * (l : G)⁻¹ := by group
        have e : ((a⁻¹ * ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : A) : G) = (l : G)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, h]
          calc ((l : G) * t)⁻¹ * t = t⁻¹ * ((l : G)⁻¹ * t) := by group
            _ = t⁻¹ * (t * (l : G)⁻¹) := by rw [hlt']
            _ = (l : G)⁻¹ := by group
        rw [e]
        exact inv_mem l.2
      rw [hmk, mem_center_iff]
      intro q'
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 b.2)
  have hcomm := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  intro y hy z hz
  have h := hcomm.is_comm.comm ((⟨y, hy⟩ : A) : A ⧸ N) ((⟨z, hz⟩ : A) : A ⧸ N)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h' := mem_subgroupOf.1 h
  have e : (((⟨y, hy⟩ : A) * ⟨z, hz⟩)⁻¹ * (⟨z, hz⟩ * ⟨y, hy⟩) : A) = (z⁻¹ * y⁻¹ * z * y : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
  rw [e] at h'
  have e2 : y * z * y⁻¹ * z⁻¹ = (y * z) * (z⁻¹ * y⁻¹ * z * y)⁻¹ * (y * z)⁻¹ := by group
  rw [e2]
  have hyzN : y * z ∈ normalizer (L : Set G) := hCN (mul_mem hy hz)
  exact (mem_normalizer_iff.1 hyzN _).1 (inv_mem h')

theorem commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer [Finite G] {L : Subgroup G}
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hOut : IsCyclic (Outer L)) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L :=
  fun _ hSt y hy z hz => commutator_mem_of_isCyclic_outer htC ht hCN hK hOut y (hSt hy) z (hSt hz)

theorem isCyclic_of_card_le_two {X : Type*} [Group X] [Finite X] (h : Nat.card X ≤ 2) :
    IsCyclic X := by
  have h1 : 0 < Nat.card X := Nat.card_pos
  rcases (show Nat.card X = 1 ∨ Nat.card X = 2 by omega) with h1 | h2
  · have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

variable [Finite G]

theorem commutator_mem_of_card_outer_le_two {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hOut : Nat.card (Outer L) ≤ 2) :
    ∀ y ∈ centralizer ({t} : Set G), ∀ z ∈ centralizer ({t} : Set G),
      y * z * y⁻¹ * z⁻¹ ∈ L :=
  commutator_mem_of_isCyclic_outer htC ht hCN hK (isCyclic_of_card_le_two hOut)

theorem commutator_mem_of_sylow_le_centralizer_of_card_outer_le_two {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hOut : Nat.card (Outer L) ≤ 2) :
    ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L :=
  fun _ hSt y hy z hz =>
    commutator_mem_of_card_outer_le_two htC ht hCN hK hOut y (hSt hy) z (hSt hz)

end Commutators

section OneSided

variable [Finite G]

theorem commutator_eq_top_of_standardSetting {L : Subgroup G} (hset : StandardSetting G L) :
    commutator G = ⊤ := by
  have := hset.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hset.nonab
    have hc : ⁅a, b⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact absurd hc hab
  · exact h

theorem exists_conj_eq_mul_twoCentral_of_card_outer_le_two {L : Subgroup G}
    (hset : StandardSetting G L) (hOut : Nat.card (Outer L) ≤ 2) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hCN := centralizer_le_normalizer_of_standard hset.standard htC ht
  exact LinearPilot.exists_conj_eq_mul_of_commutator_eq_top
    (commutator_eq_top_of_standardSetting hset) ht
    (le_centralizer_singleton_of_mem_centralizer htC) hCN
    hKt hnot hAutU (commutator_mem_of_sylow_le_centralizer_of_card_outer_le_two htC ht hCN hKt hOut)

end OneSided

section TwoSided

private def conjugateEquiv (L : Subgroup G) (x : G) : L ≃* CFSG.conjugate L x where
  toFun l := ⟨x⁻¹ * l * x, mem_conjugate_iff_conj_mem.2 (by
    have e : x * (x⁻¹ * (l : G) * x) * x⁻¹ = l := by group
    rw [e]
    exact l.2)⟩
  invFun y := ⟨x * y * x⁻¹, mem_conjugate_iff_conj_mem.1 y.2⟩
  left_inv l := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

variable [Finite G]

theorem exists_normalizer_of_two_dvd_index {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G)) (U : Sylow 2 L)
    (h2 : 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ (S : Subgroup G) (x : G), S ≤ centralizer ({t} : Set G) ∧
      (∀ u ∈ (U : Subgroup L), (u : G) ∈ S) ∧ t ∈ S ∧ x ∈ normalizer (S : Set G) ∧
      x⁻¹ * t * x ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({t} : Set G) with hMdef
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
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
  refine ⟨S, y, hSM, hUS, htS, hyN, fun hxt => hyS ?_⟩
  have hxM : (y : G) ∈ M := by
    rw [hMdef, mem_centralizer_singleton_iff]
    calc (y : G) * t = y * ((y : G)⁻¹ * t * y) := by rw [hxt]
      _ = t * y := by group
  refine hNS _ hxM ?_ hyN
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 Sst.isPGroup' y
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, orderOf_mk, orderOf_coe, hk])

theorem exists_conj_eq_mul_twoSided_of_two_dvd_index {L : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (h2 : 2 ∣ (centralizer ({t} : Set G)).index) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨U⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨S, x, hSt, hUS, htS, hxN, hxt⟩ := exists_normalizer_of_two_dvd_index ht hLt U h2
  set t' := x⁻¹ * t * x with ht'def
  have hxS : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs => (mem_normalizer_iff''.1 hxN s).1 hs
  have hxS' : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.1 hxN s).1 hs
  have hst : ∀ s ∈ S, s * t = t * s := fun s hs => mem_centralizer_singleton_iff.1 (hSt hs)
  have ht'S : t' ∈ S := hxS t htS
  have hcomm : ∀ s ∈ S, s * t' = t' * s := by
    intro s hs
    have h' := hst _ (hxS' s hs)
    calc s * t' = x⁻¹ * (x * s * x⁻¹ * t) * x := by rw [ht'def]; group
      _ = x⁻¹ * (t * (x * s * x⁻¹)) * x := by rw [h']
      _ = t' * s := by rw [ht'def]; group
  have htt' : t * t' = t' * t := (hst t' ht'S).symm
  have hzL : t * t' ∈ L :=
    LinearPilot.mul_mem_of_commute_sylow ht hLt hCN hKt hnot hAutU U (g := x) (hSt ht'S)
      fun u hu => hcomm u (hUS u hu)
  have hxtC : x⁻¹⁻¹ * t * x⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, inv_inv]
    calc x * t * x⁻¹ * t = x * (t * t') * x⁻¹ := by rw [ht'def]; group
      _ = x * (t' * t) * x⁻¹ := by rw [htt']
      _ = t * (x * t * x⁻¹) := by rw [ht'def]; group
  have hxtU : ∀ u ∈ (U : Subgroup L), (u : G) * (x⁻¹⁻¹ * t * x⁻¹) = (x⁻¹⁻¹ * t * x⁻¹) * u := by
    intro u hu
    rw [inv_inv]
    have h' := hst _ (hxS _ (hUS u hu))
    calc (u : G) * (x * t * x⁻¹) = x * ((x⁻¹ * u * x) * t) * x⁻¹ := by group
      _ = x * (t * (x⁻¹ * u * x)) * x⁻¹ := by rw [h']
      _ = x * t * x⁻¹ * u := by group
  have hz'L : t * (x⁻¹⁻¹ * t * x⁻¹) ∈ L :=
    LinearPilot.mul_mem_of_commute_sylow ht hLt hCN hKt hnot hAutU U hxtC hxtU
  rw [inv_inv] at hz'L
  have hzLx : t * t' ∈ CFSG.conjugate L x := by
    rw [mem_conjugate_iff_conj_mem]
    have e : x * (t * t') * x⁻¹ = (t * (x * t * x⁻¹))⁻¹ := by
      rw [ht'def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
      group
    rw [e]
    exact inv_mem hz'L
  have ht'C : ∀ l ∈ CFSG.conjugate L x, l * t' = t' * l := by
    intro l hl
    have hl' := mem_conjugate_iff_conj_mem.1 hl
    have h' : x * l * x⁻¹ * t = t * (x * l * x⁻¹) := mem_centralizer_singleton_iff.1 (hLt hl')
    calc l * t' = x⁻¹ * (x * l * x⁻¹ * t) * x := by rw [ht'def]; group
      _ = x⁻¹ * (t * (x * l * x⁻¹)) * x := by rw [h']
      _ = t' * l := by rw [ht'def]; group
  refine ⟨x, t * t', ⟨hzL, hzLx⟩, ?_, ?_, ⟨U, fun u hu => ?_⟩,
    ⟨Sylow.mapSurjective (f := (conjugateEquiv L x).toMonoidHom) (conjugateEquiv L x).surjective U,
      fun u hu => ?_⟩, fun l hl => ?_⟩
  · rw [← mul_assoc, htt, one_mul]
  · intro h1
    apply hxt
    calc x⁻¹ * t * x = t' := rfl
      _ = t * (t * t') := by rw [← mul_assoc, htt, one_mul]
      _ = t := by rw [h1, mul_one]
  · have hs := hUS u hu
    exact (Commute.mul_right (hst _ hs) (hcomm u hs)).eq
  · change u ∈ (U : Subgroup L).map (conjugateEquiv L x).toMonoidHom at hu
    rw [mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hvx : ((conjugateEquiv L x).toMonoidHom v : G) = x⁻¹ * v * x := rfl
    rw [hvx]
    have hvS : x⁻¹ * (v : G) * x ∈ S := hxS _ (hUS v hv)
    have hvL : x⁻¹ * (v : G) * x ∈ CFSG.conjugate L x := mem_conjugate_iff_conj_mem.2 (by
      have e : x * (x⁻¹ * (v : G) * x) * x⁻¹ = v := by group
      rw [e]
      exact v.2)
    exact (Commute.mul_right (hst _ hvS) (ht'C _ hvL)).eq
  · have h' := ht'C l hl
    calc t * l * t⁻¹ = t * (l * t') * t'⁻¹ * t⁻¹ := by group
      _ = t * (t' * l) * t'⁻¹ * t⁻¹ := by rw [h']
      _ = t * t' * l * (t * t')⁻¹ := by group

theorem two_dvd_index_of_commutator_eq_top (hperf : commutator G = ⊤) {L : Subgroup G}
    {t : G} (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    2 ∣ (centralizer ({t} : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h2
  obtain ⟨S, -, hSt⟩ := CFSG.SeitzReduction.exists_sylow_mem_le_of_not_dvd_index h2
    (mem_centralizer_singleton_iff.2 rfl) (ht.trans (pow_one 2).symm)
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 L) := inferInstance
  have htL : t ∉ L := fun htL => hnot U₀ 1 (by simpa using htL) fun u _ => by
    simpa using (mem_centralizer_singleton_iff.1 (hLt u.2))
  refine LinearPilot.commutator_ne_top_of_sylow_le_centralizer ht htL S hSt
    (habel S hSt) (fun g hg => ?_) hperf
  have htS := LinearPilot.mem_sylow_of_le_centralizer ht S hSt
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
  exact LinearPilot.mul_mem_of_commute_sylow ht hLt hCN hKt hnot hAutU U (hSt hgS)
    fun u hu => hcomm u (hUS u hu)

theorem exists_conj_eq_mul_twoSided_of_commutator_eq_top (hperf : commutator G = ⊤)
    {L : Subgroup G} {t : G} (ht : orderOf t = 2) (hLt : L ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ :=
  exists_conj_eq_mul_twoSided_of_two_dvd_index ht hLt hCN hKt hnot hAutU
    (two_dvd_index_of_commutator_eq_top hperf ht hLt hCN hKt hnot hAutU habel)

theorem exists_conj_eq_mul_twoCentral_twoSided {L : Subgroup G} (hset : StandardSetting G L)
    (hOut : Nat.card (Outer L) ≤ 2) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hCN := centralizer_le_normalizer_of_standard hset.standard htC ht
  exact exists_conj_eq_mul_twoSided_of_commutator_eq_top
    (commutator_eq_top_of_standardSetting hset) ht
    (le_centralizer_singleton_of_mem_centralizer htC) hCN
    hKt hnot hAutU (commutator_mem_of_sylow_le_centralizer_of_card_outer_le_two htC ht hCN hKt hOut)

theorem exists_conj_eq_mul_twoCentral_twoSided_of_isCyclic_outer {L : Subgroup G}
    (hset : StandardSetting G L) (hOut : IsCyclic (Outer L)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hCN := centralizer_le_normalizer_of_standard hset.standard htC ht
  exact exists_conj_eq_mul_twoSided_of_commutator_eq_top
    (commutator_eq_top_of_standardSetting hset) ht (le_centralizer_singleton_of_mem_centralizer htC)
    hCN hKt hnot hAutU
    (commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer htC ht hCN hKt hOut)

end TwoSided

end CFSG.SeitzReduction.SeitzQ2
