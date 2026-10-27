module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
import TauCeti.GroupTheory.Elementary
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

theorem sec8t84v_exists_mul_of_sylow {G : Type} [Group G] [Finite G] {N S M : Subgroup G}
    (hS : IsSylow2Of S N) (hMN : M ≤ N) (hnorm : N ≤ normalizer (M : Set G))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) ∈ M) : ∀ x ∈ N, ∃ s ∈ S, ∃ m ∈ M, x = s * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := IsSylow2Of.exists_sylow hS
  let P' : Subgroup ↥N := P
  have hP'map : P'.map N.subtype = S := hP
  obtain ⟨hSN, -, hndvdS⟩ := hS
  haveI : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr hnorm
  have hsub : S.subgroupOf N = P' := by
    rw [← hP'map]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective P'
  have hPi : ¬ 2 ∣ P'.index := by
    rw [Subgroup.relIndex, hsub] at hndvdS
    exact hndvdS
  have hquot : ∀ g : ↥N, ∃ k : ℕ, g ^ (2 ^ k) ∈ M.subgroupOf N := by
    intro g
    obtain ⟨k, hk⟩ := h2 (g : G) g.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have hq : IsPGroup 2 (↥N ⧸ M.subgroupOf N) :=
    TauCeti.isPGroup_quotient_of_forall_exists_pow_mem hquot
  set ρ : ↥N →* ↥N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N) with hρdef
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective (M.subgroupOf N)
  have htop : P'.map ρ = ⊤ := by
    have h1 : (P'.map ρ).index ∣ P'.index := Subgroup.index_map_dvd P' hρs
    obtain ⟨m, hm⟩ := hq.index (P'.map ρ)
    rw [← Subgroup.index_eq_one]
    by_contra hne
    have hm0 : m ≠ 0 := fun h0 => hne (by rw [hm, h0, pow_zero])
    exact hPi ((dvd_pow_self 2 hm0).trans (hm ▸ h1))
  intro x hx
  let x' : ↥N := ⟨x, hx⟩
  have hxmem : ρ x' ∈ P'.map ρ := by rw [htop]; trivial
  obtain ⟨t, htP, ht⟩ := Subgroup.mem_map.mp hxmem
  refine ⟨(t : G), ?_, (t : G)⁻¹ * x, ?_, by group⟩
  · have : (t : G) ∈ P'.map N.subtype := ⟨t, htP, rfl⟩
    rwa [hP'map] at this
  · have hmem : t⁻¹ * x' ∈ M.subgroupOf N := by
      have hker : ρ (t⁻¹ * x') = 1 := by rw [map_mul, map_inv, ht, inv_mul_cancel]
      rw [hρdef] at hker
      rw [← QuotientGroup.ker_mk' (M.subgroupOf N), MonoidHom.mem_ker]
      exact hker
    exact Subgroup.mem_subgroupOf.mp hmem

theorem sec8t84v_mem_normalizer_sup_centralizer {G : Type} [Group G] {L : Subgroup G} {n : G}
    (hn : n ∈ normalizer (L : Set G)) :
    n ∈ normalizer ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left ?_ hn
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc l hl
    have hml : m⁻¹ * l * m ∈ L := (Subgroup.mem_normalizer_iff''.mp hm l).mp hl
    have h1 := hc (m⁻¹ * l * m) hml
    calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
      _ = (m * c * m⁻¹) * l := by group
  · intro hc l hl
    have hml : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hm l).mp hl
    have h1 := hc (m * l * m⁻¹) hml
    calc l * c = m⁻¹ * ((m * l * m⁻¹) * (m * c * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * c * m⁻¹) * (m * l * m⁻¹)) * m := by rw [h1]
      _ = c * l := by group

theorem sec8t84v_mem_sup_centralizer {G : Type} [Group G] {L : Subgroup G} {x : G}
    (hx : x ∈ L ⊔ centralizer (L : Set G)) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), x = l * c := by
  have hLE : L ≤ normalizer (centralizer (L : Set G) : Subgroup G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have h : l * c * l⁻¹ = c := by rw [hc l hl, mul_assoc, mul_inv_cancel, mul_one]
      rw [h]; exact hc
    · intro hd
      have hcomm := Subgroup.mem_centralizer_iff.mp hd l hl
      have hdc : l * c * l⁻¹ = c := by
        rw [show (l * c * l⁻¹) * l = l * c by group] at hcomm
        exact mul_left_cancel hcomm
      rw [← hdc]; exact hd
  have hx' : x ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right L (centralizer (L : Set G)) hLE]
  obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.mp hx'
  exact ⟨l, hl, c, hc, hlc.symm⟩

theorem sec8t84v_exists_pow_mem_sup_centralizer (hM : Asc82Tab6M) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsOm6M L) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    ∃ k : ℕ, x ^ (2 ^ k) ∈ L ⊔ centralizer (L : Set G) := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨k, ?_⟩
  have hpow : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdvd : 2 ^ k ∣ orderOf x := by rw [hk]; exact dvd_mul_right _ _
  have horder : orderOf (x ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd hpow hdvd, hk,
      Nat.mul_div_cancel_left m (pow_pos (by norm_num : (0 : ℕ) < 2) k)]
  have hxN : x ^ (2 ^ k) ∈ normalizer (L : Set G) := pow_mem hx (2 ^ k)
  have hodd : Odd (orderOf (x ^ (2 ^ k))) := by rw [horder]; exact hm
  simpa only [InnerOn] using hM.out_two G L hL (x ^ (2 ^ k)) hxN hodd

private theorem sec8t84v_mem_sup_of_le_normalizer {G : Type} [Group G] {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h' ∈ H, ∃ k ∈ K, x = h' * k := by
  have hx' : x ∈ (H : Set G) * (K : Set G) := by
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right H K h]
  obtain ⟨h', hh', k, hk, hk'⟩ := Set.mem_mul.mp hx'
  exact ⟨h', hh', k, hk, hk'.symm⟩

theorem sec8t84v_cent_decomp (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {γ : G}
    (hγS : γ ∈ S) (hgen : S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L)) :
    ∀ x ∈ centralizer ({t} : Set G), ∃ b ∈ zpowers γ, ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G),
      x = b * l * c := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hnormN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hS
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hS.toSec3Setting
  have htS : t ∈ S := sec4_t_mem_S hctx.sylow hS.involution
  have htN : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hγN : γ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hγS
  have hnormM : centralizer ({t} : Set G) ≤ normalizer
      ((centralizer ({t} : Set G) ⊓ (L ⊔ centralizer (L : Set G)) : Subgroup G) : Set G) := by
    intro n hn
    have hnN : n ∈ normalizer (centralizer ({t} : Set G) : Set G) := Subgroup.le_normalizer hn
    have hn2 : n ∈ normalizer ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) :=
      sec8t84v_mem_normalizer_sup_centralizer (hnormN n hn)
    exact inf_normalizer_le_normalizer_inf ⟨hnN, hn2⟩
  have h2 : ∀ y ∈ centralizer ({t} : Set G), ∃ k : ℕ,
      y ^ (2 ^ k) ∈ centralizer ({t} : Set G) ⊓ (L ⊔ centralizer (L : Set G)) := by
    intro y hy
    obtain ⟨k, hk⟩ := sec8t84v_exists_pow_mem_sup_centralizer F.hM hLM (hnormN y hy)
    exact ⟨k, pow_mem hy (2 ^ k), hk⟩
  intro x hx
  obtain ⟨s, hsS, m, hmM, hxsm⟩ :=
    sec8t84v_exists_mul_of_sylow hctx.sylow inf_le_left hnormM h2 x hx
  obtain ⟨l₂, hl₂, c₁, hc₁, hmlc⟩ := sec8t84v_mem_sup_centralizer hmM.2
  have hG_le : zpowers γ ≤ S := by rw [hgen]; exact le_sup_right.trans le_sup_left
  have hP_le : S ⊓ L ≤ S := inf_le_left
  have ht_normP : t ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htS, hnormN t htN⟩
  have hγ_normP : γ ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hγS, hnormN γ hγN⟩
  have hAG_normP : zpowers t ⊔ zpowers γ ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr ht_normP) (Subgroup.zpowers_le.mpr hγ_normP)
  have hcent_eq : centralizer (zpowers γ : Set G) = centralizer ({γ} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hγt : t * γ = γ * t := Subgroup.mem_centralizer_iff.mp hγN t (Set.mem_singleton t)
  have ht_centG : t ∈ centralizer (zpowers γ : Set G) := by
    rw [hcent_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hγt
  have hA_normG : zpowers t ≤ normalizer (zpowers γ : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (zpowers γ : Set G) ht_centG)
  have hs_mem : s ∈ zpowers t ⊔ zpowers γ ⊔ (S ⊓ L) := by rw [← hgen]; exact hsS
  obtain ⟨k, hk, p, hp, hskp⟩ := sec8t84v_mem_sup_of_le_normalizer hAG_normP hs_mem
  obtain ⟨a, ha, b, hb, hkab⟩ := sec8t84v_mem_sup_of_le_normalizer hA_normG hk
  have ha_comm : ∀ y ∈ centralizer ({t} : Set G), a * y = y * a := by
    intro y hy
    have hty : t ∈ centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy t (Set.mem_singleton t))
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hty ha)
  refine ⟨b, hb, p * l₂, mul_mem hp.2 hl₂, a * c₁,
    mul_mem (Subgroup.zpowers_le.mpr htC ha) hc₁, ?_⟩
  rw [hxsm, hskp, hkab, hmlc]
  have hab : Commute a b := ha_comm b (hctx.sylow.1 (hG_le hb))
  have hap : Commute a p := ha_comm p (hctx.sylow.1 (hP_le hp))
  have hal : Commute a l₂ := ha_comm l₂ (hLt hl₂)
  have hu : Commute a (b * (p * l₂)) := hab.mul_right (hap.mul_right hal)
  calc (a * b * p) * (l₂ * c₁)
      = a * (b * (p * l₂)) * c₁ := by group
    _ = (b * (p * l₂)) * a * c₁ := by rw [hu.eq]
    _ = b * (p * l₂) * (a * c₁) := by group

end CFSG.OddStandard.SmallF3.Omega
