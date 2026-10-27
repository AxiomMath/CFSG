module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveBasic
public import CFSG.LocalAnalysis.SteinbergBNCyclicStandardOddCoreSplitting
public import CFSG.LocalAnalysis.SteinbergBNCyclicStandardSylowEscape
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

structure Sector (L : Subgroup G) (S : Sylow 2 (centralizer (L : Set G))) (t : G) : Prop where
  standard : standardComponentIsStandard L
  cyclic : IsCyclic (S : Subgroup (centralizer (L : Set G)))
  t_mem : t ∈ (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
  t_order : orderOf t = 2

@[expose] def sg (L : Subgroup G) (S : Sylow 2 (centralizer (L : Set G))) : Subgroup G :=
  (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype

@[expose] def oddKer (L : Subgroup G) : Subgroup G :=
  (CFSG.oddCore (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype

section Basic

variable {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}

theorem sg_le_centralizer : sg L S ≤ centralizer (L : Set G) := map_subtype_le _

theorem isPGroup_sg : IsPGroup 2 (sg L S) := S.isPGroup'.map _

theorem isCyclic_sg (hs : Sector L S t) : IsCyclic (sg L S) := by
  have := hs.cyclic
  have e : (S : Subgroup (centralizer (L : Set G))) ≃* sg L S :=
    (S : Subgroup (centralizer (L : Set G))).equivMapOfInjective _ (Subgroup.subtype_injective _)
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem card_sg : Nat.card (sg L S) = Nat.card (S : Subgroup (centralizer (L : Set G))) :=
  Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem t_mem_sg (hs : Sector L S t) : t ∈ sg L S := hs.t_mem

theorem t_mem_centralizer (hs : Sector L S t) : t ∈ centralizer (L : Set G) :=
  sg_le_centralizer hs.t_mem

theorem sg_comm (hs : Sector L S t) : ∀ u ∈ sg L S, ∀ w ∈ sg L S, u * w = w * u := by
  have := isCyclic_sg hs
  intro u hu w hw
  exact congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := sg L S)).is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)

theorem eq_t_of_orderOf_eq_two [Finite G] (hs : Sector L S t) {u : G} (hu : u ∈ sg L S)
    (hu2 : orderOf u = 2) : u = t :=
  CFSG.LocalAnalysis.eq_of_orderOf_eq_two_of_isCyclic_subgroup (isCyclic_sg hs) hu hs.t_mem hu2
    hs.t_order

theorem sg_maximal {T : Subgroup G} (hTC : T ≤ centralizer (L : Set G)) (hT : IsPGroup 2 T)
    (hle : sg L S ≤ T) : T = sg L S := by
  have hQ : IsPGroup 2 (T.subgroupOf (centralizer (L : Set G))) :=
    hT.of_equiv (subgroupOfEquivOfLe hTC).symm
  have hSQ : (S : Subgroup (centralizer (L : Set G))) ≤
      T.subgroupOf (centralizer (L : Set G)) := fun u hu => by
    rw [mem_subgroupOf]
    exact hle ⟨u, hu, rfl⟩
  have h1 := S.is_maximal' hQ hSQ
  refine le_antisymm (fun x hx => ?_) hle
  have hx' : (⟨x, hTC hx⟩ : centralizer (L : Set G)) ∈
      T.subgroupOf (centralizer (L : Set G)) := mem_subgroupOf.mpr hx
  rw [h1] at hx'
  exact ⟨_, hx', rfl⟩

end Basic

section Local

variable {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}

theorem sg_le_centralizer_t (hs : Sector L S t) : sg L S ≤ centralizer ({t} : Set G) := fun u hu =>
  mem_centralizer_singleton_iff.mpr (sg_comm hs t (t_mem_sg hs) u hu).symm

theorem sg_le_normalizer : sg L S ≤ normalizer (L : Set G) :=
  sg_le_centralizer.trans (centralizer_le_normalizer _)

theorem centralizer_normalized {m : G} (hm : m ∈ normalizer (L : Set G)) {c : G}
    (hc : c ∈ centralizer (L : Set G)) : m * c * m⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : m⁻¹ * l * m⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hm) l).mp hl
  rw [inv_inv] at hl'
  have h1 := hc _ hl'
  calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * l := by group

theorem centralizer_t_facts [Finite G] (hs : Sector L S t) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      L ≤ centralizer ({t} : Set G) ∧
      (L.subgroupOf (centralizer ({t} : Set G))).Normal ∧
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
  obtain ⟨h1, h2, h3, -, h5⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hs.standard
      (t_mem_centralizer hs) hs.t_order
  exact ⟨h1, h2, h3, h5⟩

end Local

section Kernel

variable {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}

theorem oddKer_le_centralizer : oddKer L ≤ centralizer (L : Set G) := map_subtype_le _

theorem oddKer_complement [Finite G] (hs : Sector L S t) :
    Odd (Nat.card (oddKer L)) ∧ oddKer L ⊓ sg L S = ⊥ ∧
      (oddKer L : Set G) * (sg L S : Set G) = centralizer (L : Set G) := by
  obtain ⟨-, hprodC, hinterC, ⟨-, hoddC, -, -⟩, -⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement S hs.cyclic
  rw [← CFSG.LocalAnalysis.oddCore_eq_pPrimeCore_two] at hprodC hinterC hoddC
  refine ⟨?_, ?_, ?_⟩
  · rw [show Nat.card (oddKer L) = Nat.card (CFSG.oddCore (centralizer (L : Set G))) from
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hoddC
  · show (CFSG.oddCore (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype ⊓
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = ⊥
    rw [← map_inf_eq _ _ _ (Subgroup.subtype_injective _), hinterC, Subgroup.map_bot]
  · ext x
    constructor
    · rintro ⟨k, hk, u, hu, rfl⟩
      exact mul_mem (oddKer_le_centralizer hk) (sg_le_centralizer hu)
    · intro hx
      have h1 : (⟨x, hx⟩ : centralizer (L : Set G)) ∈
          ((CFSG.oddCore (centralizer (L : Set G)) : Set (centralizer (L : Set G))) *
            (S : Set (centralizer (L : Set G)))) := by
        rw [hprodC]
        exact Set.mem_univ _
      obtain ⟨a, ha, b, hb, hab⟩ := h1
      exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, congrArg Subtype.val hab⟩

theorem oddKer_normalized [Finite G] (hs : Sector L S t) {m : G}
    (hm : m ∈ normalizer (L : Set G)) {k : G} (hk : k ∈ oddKer L) : m * k * m⁻¹ ∈ oddKer L := by
  obtain ⟨-, -, -, -, hcharC⟩ := CFSG.cyclic_sylow_normal_odd_complement S hs.cyclic
  rw [← CFSG.LocalAnalysis.oddCore_eq_pPrimeCore_two] at hcharC
  obtain ⟨c, hc, rfl⟩ := hk
  have hCnorm : ∀ m ∈ normalizer (L : Set G), ∀ c ∈ centralizer (L : Set G),
      m * c * m⁻¹ ∈ centralizer (L : Set G) := fun m hm c hc => centralizer_normalized hm hc
  have h1 := (characteristic_iff_map_eq.mp hcharC)
    (CFSG.LocalAnalysis.conjActOn hCnorm ⟨m, hm⟩)
  have h2 : CFSG.LocalAnalysis.conjActOn hCnorm ⟨m, hm⟩ c ∈
      CFSG.oddCore (centralizer (L : Set G)) := by
    rw [← h1]
    exact ⟨c, hc, rfl⟩
  exact ⟨_, h2, rfl⟩

theorem exists_generator_sg [Finite G] (hs : Sector L S t) :
    ∃ (g : G) (a : ℕ), sg L S = zpowers g ∧ orderOf g = 2 ^ a ∧ 1 ≤ a ∧
      Nat.card (sg L S) = 2 ^ a ∧ t = g ^ 2 ^ (a - 1) := by
  have hcyc := isCyclic_sg hs
  obtain ⟨g', hg'⟩ := hcyc.exists_generator
  obtain ⟨a, ha⟩ := (isPGroup_sg (L := L) (S := S)).exists_card_eq
  set g : G := (g' : G)
  have hgS : sg L S = zpowers g := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg' ⟨x, hx⟩)
      exact mem_zpowers_iff.mpr ⟨k, by have := congrArg Subtype.val hk; simpa using this⟩
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact zpow_mem g'.2 k
  have hord : orderOf g = 2 ^ a := by
    rw [← ha, ← Nat.card_zpowers, ← hgS]
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exfalso
      have h1 : orderOf g = 1 := by rw [hord, h0]; rfl
      have : t ∈ zpowers g := hgS ▸ hs.t_mem
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp this
      have : g = 1 := orderOf_eq_one_iff.mp h1
      rw [this, one_zpow] at hk
      have h2 := hs.t_order
      rw [← hk, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h0
  refine ⟨g, a, hgS, hord, ha1, ha, ?_⟩
  exact eq_pow_of_mem_zpowers_of_orderOf_eq_two hord (hgS ▸ hs.t_mem) hs.t_order

theorem exists_sq_eq_t [Finite G] (hs : Sector L S t) (h4 : 4 ≤ Nat.card (sg L S)) :
    ∃ w ∈ sg L S, w * w = t := by
  obtain ⟨g, a, hgS, hord, ha1, hcard, ht⟩ := exists_generator_sg hs
  have ha2 : 2 ≤ a := by
    by_contra h
    have h1 : a = 1 := by omega
    rw [h1] at hcard
    norm_num at hcard
    omega
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  refine ⟨g ^ 2 ^ b, hgS ▸ pow_mem (mem_zpowers g) _, ?_⟩
  rw [ht, ← pow_add]
  have h' : b + 2 - 1 = b + 1 := by omega
  rw [h', pow_succ]
  congr 1
  omega

theorem commute_of_mem_centralizer_of_normalizes [Finite G] (hs : Sector L S t) {r : G}
    (hr : r ∈ centralizer (L : Set G)) (hrn : ∀ u ∈ sg L S, r * u * r⁻¹ ∈ sg L S) :
    ∀ u ∈ sg L S, r * u = u * r := by
  obtain ⟨-, hKS, hprod⟩ := oddKer_complement hs
  have hr' : r ∈ (oddKer L : Set G) * (sg L S : Set G) := by rw [hprod]; exact hr
  obtain ⟨k, hk, s', hs', rfl⟩ := hr'
  intro u hu
  have h1 : (k * s') * u * (k * s')⁻¹ ∈ sg L S := hrn u hu
  have h2 : (k * s') * u * (k * s')⁻¹ = k * u * k⁻¹ := by
    have := sg_comm hs s' hs' u hu
    calc (k * s') * u * (k * s')⁻¹ = k * (s' * u) * s'⁻¹ * k⁻¹ := by group
      _ = k * (u * s') * s'⁻¹ * k⁻¹ := by rw [this]
      _ = k * u * k⁻¹ := by group
  rw [h2] at h1
  have h3 : k * u * k⁻¹ * u⁻¹ ∈ sg L S := mul_mem h1 (inv_mem hu)
  have h4 : k * u * k⁻¹ * u⁻¹ ∈ oddKer L := by
    have h5 := mul_mem hk (oddKer_normalized hs (sg_le_normalizer hu) (inv_mem hk))
    simpa [mul_assoc] using h5
  have h5 : k * u * k⁻¹ * u⁻¹ ∈ oddKer L ⊓ sg L S := ⟨h4, h3⟩
  rw [hKS, mem_bot] at h5
  have h6 : k * u = u * k := by
    calc k * u = k * u * k⁻¹ * u⁻¹ * (u * k) := by group
      _ = u * k := by rw [h5, one_mul]
  calc k * s' * u = k * (s' * u) := by group
    _ = k * (u * s') := by rw [sg_comm hs s' hs' u hu]
    _ = (k * u) * s' := by group
    _ = (u * k) * s' := by rw [h6]
    _ = u * (k * s') := by group

end Kernel

end CFSG.OddStandard
