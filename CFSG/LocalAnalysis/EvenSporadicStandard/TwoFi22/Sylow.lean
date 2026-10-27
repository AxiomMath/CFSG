module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer

variable {G : Type} [Group G] {t : G}

theorem ncard_modEq_fixed [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) (D : Set G)
    (hD : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) :
    D.ncard ≡ {x ∈ D | ∀ s ∈ S, s * x * s⁻¹ = x}.ncard [MOD 2] := by
  let _ : MulAction S D :=
    { smul := fun g x => ⟨g * x * g⁻¹, hD g x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : S) : G) * (x : G) * ((1 : S) : G)⁻¹ = x
        simp)
      mul_smul := fun g h x => Subtype.ext (by
        show ((g * h : S) : G) * (x : G) * ((g * h : S) : G)⁻¹ =
          (g : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (g : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have key := hS.card_modEq_card_fixedPoints D
  rw [Nat.card_coe_set_eq] at key
  have himg : Subtype.val '' (MulAction.fixedPoints S D) = {x ∈ D | ∀ s ∈ S, s * x * s⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hfix, rfl⟩
      refine ⟨hy, fun s hs => ?_⟩
      have := congrArg Subtype.val (hfix ⟨s, hs⟩)
      exact this
    · rintro ⟨hx, hfix⟩
      exact ⟨⟨x, hx⟩, fun s => Subtype.ext (hfix s s.2), rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact key


theorem ncard_conjugatesOf_eq
    (M : Model G t) (ε : Bool) {x : centralizer ({t} : Set G)} (hx : M.ψ x ∈ starSet ε) :
    (conjugatesOf x).ncard = 3510 := by
  have himg : M.ψ '' conjugatesOf x = starSet ε := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hv
      rw [map_mul, map_mul, map_inv]
      exact starSet_conj (psi_comm_d M c) hx
    · intro hy
      obtain ⟨c, hc, hcxy⟩ := starSet_trans hx hy
      obtain ⟨v, rfl⟩ := (M.range c).1 hc
      exact ⟨v * x * v⁻¹, isConj_iff.2 ⟨v, rfl⟩, by rw [map_mul, map_mul, map_inv, hcxy]⟩
  rw [← Set.ncard_image_of_injective _ M.inj, himg, ncard_starSet]

theorem not_centralized [Finite G]
    (M : Model G t) {ε : Bool} {x : centralizer ({t} : Set G)} (hx : M.ψ x ∈ starSet ε)
    (P : Sylow 2 (centralizer ({t} : Set G))) : ¬ ∀ s ∈ P, s * x = x * s := by
  intro h
  have hle : (P : Subgroup (centralizer ({t} : Set G))) ≤
      Subgroup.centralizer ({x} : Set (centralizer ({t} : Set G))) := fun s hs =>
    mem_centralizer_singleton_iff.2 (h s hs)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_centralizer_eq_ncard, ncard_conjugatesOf_eq M ε hx] at hdvd
  exact P.not_dvd_index (dvd_trans (by norm_num : 2 ∣ 3510) hdvd)

theorem tL_mem_sylow (ht : orderOf t = 2) (P : Sylow 2 (centralizer ({t} : Set G))) :
    (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({t} : Set G)) ∈ P := by
  let tL : centralizer ({t} : Set G) := ⟨t, mem_centralizer_singleton_iff.2 rfl⟩
  have hnorm : (zpowers tL).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : g * tL = tL * g := Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
    have : g * tL * g⁻¹ = tL := by rw [hc]; group
    rw [← conj_zpow, this]
    exact mem_zpowers_iff.2 ⟨k, rfl⟩
  have htL2 : tL * tL = 1 := Subtype.ext (mul_self_of_orderOf_two ht)
  have hp : IsPGroup 2 (zpowers tL) := by
    refine IsPGroup.of_card (n := 1) ?_
    have h1 : tL ^ 2 = 1 := by rw [pow_two]; exact htL2
    have h2 : tL ≠ 1 := fun h => by
      have : (tL : G) = 1 := congrArg Subtype.val h
      rw [show (tL : G) = t from rfl] at this
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime h1 h2
  exact hp.le_sylow_of_normal P (mem_zpowers tL)

theorem index_map_subtype_odd [Finite G] {L : Subgroup G} (P : Sylow 2 L) (hL : ¬ 2 ∣ L.index) :
    ¬ 2 ∣ ((P : Subgroup L).map L.subtype).index := by
  have hSle : (P : Subgroup L).map L.subtype ≤ L := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hrel : ((P : Subgroup L).map L.subtype).relIndex L = (P : Subgroup L).index := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hidx : ((P : Subgroup L).map L.subtype).index = (P : Subgroup L).index * L.index := by
    rw [← hrel, Subgroup.relIndex_mul_index hSle]
  rw [hidx]
  exact fun h => ((Nat.Prime.dvd_mul Nat.prime_two).1 h).elim P.not_dvd_index hL

theorem index_centralizer_odd
    [Finite G] [IsSimpleGroup G]
    (M : Model G t) (hF : SquareFacts) (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2)
    (P : Sylow 2 (centralizer ({t} : Set G))) : ¬ 2 ∣ (centralizer ({t} : Set G)).index := by
  obtain ⟨ε, hε⟩ := Dt_eq_starSet M hF hnonab ht
  have hSle : (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hLidx : (centralizer ({t} : Set G)).index = (conjugatesOf t).ncard :=
    Subgroup.index_centralizer_eq_ncard t
  have hpg : IsPGroup 2 ((P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) := P.2.map _
  have hmod := ncard_modEq_fixed hpg (conjugatesOf t) (fun g x hx => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    exact isConj_iff.2 ⟨g * c, by group⟩)
  have htS : t ∈ (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype := ⟨_, tL_mem_sylow ht P, rfl⟩
  have hfix : {x ∈ conjugatesOf t | ∀ s ∈ (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype, s * x * s⁻¹ = x} = {t} := by
    ext x
    constructor
    · rintro ⟨hx, hfix⟩
      by_contra hne
      have hxt : x * t = t * x := by
        have := hfix t htS
        calc x * t = t * x * t⁻¹ * t := by rw [this]
          _ = t * x := by group
      have hmem : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hxt
      have hD : (⟨x, hmem⟩ : centralizer ({t} : Set G)) ∈ Dt t := ⟨hx, hne⟩
      refine not_centralized M ((hε _).1 hD) P fun s hs => ?_
      apply Subtype.ext
      have := hfix (s : G) ⟨s, hs, rfl⟩
      calc (s : G) * x = s * x * (s : G)⁻¹ * s := by group
        _ = x * s := by rw [this]
    · rintro rfl
      refine ⟨IsConj.refl x, fun s hs => ?_⟩
      have := mem_centralizer_singleton_iff.1 (hSle hs)
      rw [this]
      group
  rw [hfix, Set.ncard_singleton] at hmod
  rw [hLidx]
  intro h2
  have h := hmod
  rw [Nat.ModEq] at h
  omega

theorem index_map_odd
    [Finite G] [IsSimpleGroup G]
    (M : Model G t) (hF : SquareFacts) (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2)
    (P : Sylow 2 (centralizer ({t} : Set G))) :
    ¬ 2 ∣ ((P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype).index :=
  index_map_subtype_odd P (index_centralizer_odd M hF hnonab ht P)

end CFSG.EvenSporadicStandard.TwoFi22
