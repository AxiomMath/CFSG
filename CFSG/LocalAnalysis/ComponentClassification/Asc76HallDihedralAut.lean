module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76HallDihedralClosed

public section

namespace CFSG.ComponentClassification.Asc76X.HallDihedral

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec4
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G]

theorem isDihedralTwoGroup_of_rot {U R : Subgroup G} (hU : IsDihedralRot U R) :
    IsDihedralTwoGroup R := by
  obtain ⟨ρ, hρ, -⟩ := hU.exists_gen
  obtain ⟨s, hsR, hsU⟩ := hU.exists_not_mem
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hρR : ρ ∈ R := hU.le hρU
  have hss : s * s = 1 := hU.mul_self s hsR hsU
  have hconj : s * ρ * s⁻¹ = ρ⁻¹ := hU.conj_eq s hsR hsU ρ hρU
  have hgen : zpowers ρ ⊔ zpowers s = R := by
    apply le_antisymm
    · exact sup_le ((zpowers_le).mpr hρR) ((zpowers_le).mpr hsR)
    · intro r hr
      by_cases hrU : r ∈ U
      · exact mem_sup_left (hρ.symm ▸ hrU)
      · have hsr : s⁻¹ * r ∈ U := hU.mul_mem_of_not_mem (inv_mem hsR) hr
          (fun h => hsU (by simpa using inv_mem h)) hrU
        have e : r = s * (s⁻¹ * r) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left (hρ.symm ▸ hsr))
  have hDG : CFSG.ComponentClassification.AschbacherToolkit.HasDihedralGenerators R := by
    refine ⟨⟨ρ, hρR⟩, ⟨s, hsR⟩, ?_, ?_, ?_, ?_⟩
    · apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hgen
    · exact Subtype.ext (by simp [pow_two, hss])
    · exact Subtype.ext (by simpa using hconj)
    · intro hmem
      have hmem' : s ∈ zpowers ρ := by
        have := Subgroup.mem_map_of_mem R.subtype hmem
        rwa [MonoidHom.map_zpowers] at this
      exact hsU (hρ ▸ hmem')
  rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hU.isPGroup hDG with hc | hd
  · exact absurd (IsCyclic.isMulCommutative (α := R)) hU.not_isMulCommutative
  · exact hd

namespace Hyp

variable {Ω : Set (Subgroup G)} {S K R U : Subgroup G} {t z : G}

theorem t_mem_rPrime (h : Hyp Ω S K R U t z) : t ∈ h.rPrime :=
  h.mem_rPrime.mpr (Or.inr (by rw [h.t_mul]; exact U.one_mem))

theorem inv_t_conj (h : Hyp Ω S K R U t z) {u : G} (hu : u ∈ U) : t⁻¹ * u * t = u⁻¹ := by
  have h1 : t * u⁻¹ * t⁻¹ = u := by rw [h.outer_t.inv h u⁻¹ (inv_mem hu), inv_inv]
  calc t⁻¹ * u * t = t⁻¹ * (t * u⁻¹ * t⁻¹) * t := by rw [h1]
    _ = u⁻¹ := by group

theorem rot_rPrime (h : Hyp Ω S K R U t z) : IsDihedralRot U h.rPrime where
  le := fun u hu => h.mem_rPrime.mpr (Or.inl hu)
  isCyclic := h.rot.isCyclic
  relIndex_eq := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, h.t_mem_rPrime⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases h.mem_rPrime.mp b.2 with hb | hb
    · refine Or.inr ⟨hb, fun hbt => h.t_not_mem ?_⟩
      have e : t = (b : G)⁻¹ * (b * t) := by group
      rw [e]
      exact mul_mem (inv_mem hb) hbt
    · refine Or.inl ⟨hb, fun hbU => h.t_not_mem ?_⟩
      have e : t = (b : G)⁻¹ * (b * t) := by group
      rw [e]
      exact mul_mem (inv_mem hbU) hb
  four_le := h.rot.four_le
  isPGroup := h.sylow.isPGroup.to_le h.rPrime_le
  mul_self := by
    intro x hx hxU
    have hu : x * t ∈ U := (h.mem_rPrime.mp hx).resolve_left hxU
    calc x * x = (x * t) * (t⁻¹ * (x * t) * t) * (t * t)⁻¹ := by group
      _ = 1 := by rw [h.inv_t_conj hu, h.t_mul, inv_one, mul_one, mul_inv_cancel]
  conj_eq := by
    intro x hx hxU v hv
    have hu : x * t ∈ U := (h.mem_rPrime.mp hx).resolve_left hxU
    have hc : x * t * v⁻¹ = v⁻¹ * (x * t) := h.rot.commute_of_mem hu (inv_mem hv)
    calc x * v * x⁻¹ = (x * t) * (t⁻¹ * v * t) * (x * t)⁻¹ := by group
      _ = x * t * v⁻¹ * (x * t)⁻¹ := by rw [h.inv_t_conj hv]
      _ = v⁻¹ := by rw [hc]; group

theorem isDihedralTwoGroup_rPrime (h : Hyp Ω S K R U t z) : IsDihedralTwoGroup h.rPrime :=
  isDihedralTwoGroup_of_rot h.rot_rPrime

theorem pow_mem_centralizer (h : Hyp Ω S K R U t z) :
    ∀ n ∈ normalizer (h.rPrime : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ centralizer (h.rPrime : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn
  have hnU : n ∈ normalizer (U : Set G) := h.rot_rPrime.normalizer_le hn
  obtain ⟨m, hm⟩ := (h.rot.isPGroup.to_le h.rot.le).exists_card_eq
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := h.rot.four_le
      rw [hm, h0] at this
      norm_num at this
    · exact h0
  have : IsCyclic U := h.rot.isCyclic
  have hAut : IsPGroup 2 (MulAut U) := by
    refine IsPGroup.of_card (n := m - 1) ?_
    rw [IsCyclic.card_mulAut, hm, Nat.totient_prime_pow Nat.prime_two hm0]
    norm_num
  obtain ⟨k, hk⟩ := hAut (U.normalizerMonoidHom ⟨n, hnU⟩)
  have hnk : n ^ (2 ^ k) ∈ centralizer (U : Set G) := by
    have h1 : (⟨n, hnU⟩ : normalizer (U : Set G)) ^ (2 ^ k) ∈
        U.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_pow, hk]
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at h1
    simpa using h1
  set n' := n ^ (2 ^ k) with hn'
  have hn'N : n' ∈ normalizer (h.rPrime : Set G) := pow_mem hn _
  have hn'U : ∀ u ∈ U, n' * u = u * n' := fun u hu => (mem_centralizer_iff.mp hnk u hu).symm
  have hw : n' * t * n'⁻¹ * t⁻¹ ∈ U := by
    have h1 : n' * t * n'⁻¹ ∈ h.rPrime := (mem_normalizer_iff.mp hn'N t).mp h.t_mem_rPrime
    have h2 : n' * t * n'⁻¹ ∉ U := fun hU => h.t_not_mem (by
      have h3 := (mem_normalizer_iff.mp (h.rot_rPrime.normalizer_le hn'N) t).mpr hU
      exact h3)
    have h3 := (h.mem_rPrime.mp h1).resolve_left h2
    have e : n' * t * n'⁻¹ * t⁻¹ = n' * t * n'⁻¹ * t * (t * t)⁻¹ := by group
    rw [e, h.t_mul, inv_one, mul_one]
    exact h3
  set w := n' * t * n'⁻¹ * t⁻¹ with hwdef
  have hpow : ∀ j : ℕ, n' ^ j * t * (n' ^ j)⁻¹ = w ^ j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : n' * w ^ j = w ^ j * n' := hn'U _ (pow_mem hw j)
      calc n' ^ (j + 1) * t * (n' ^ (j + 1))⁻¹ = n' * (n' ^ j * t * (n' ^ j)⁻¹) * n'⁻¹ := by
            rw [pow_succ']
            group
        _ = n' * w ^ j * (t * n'⁻¹) := by rw [ih]; group
        _ = w ^ j * (n' * t * n'⁻¹ * t⁻¹) * t := by rw [hc]; group
        _ = w ^ (j + 1) * t := by rw [← hwdef, pow_succ]
  have hwU : w ^ Nat.card U = 1 := by
    have h1 : (⟨w, hw⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  refine ⟨k + m, ?_⟩
  have e : n ^ (2 ^ (k + m)) = n' ^ Nat.card U := by rw [hn', hm, ← pow_mul, ← pow_add]
  rw [e, mem_centralizer_iff]
  intro x hx
  have hct : n' ^ Nat.card U * t = t * n' ^ Nat.card U := by
    have h1 := hpow (Nat.card U)
    rw [hwU, one_mul] at h1
    calc n' ^ Nat.card U * t = n' ^ Nat.card U * t * (n' ^ Nat.card U)⁻¹ * n' ^ Nat.card U := by
          group
      _ = t * n' ^ Nat.card U := by rw [h1]
  have hcu : ∀ u ∈ U, n' ^ Nat.card U * u = u * n' ^ Nat.card U := fun u hu =>
    (Commute.pow_left (hn'U u hu) _).eq
  rcases h.mem_rPrime.mp hx with hxU | hxt
  · exact (hcu x hxU).symm
  · have e' : x = x * t * t⁻¹ := by group
    rw [e']
    have h1 := hcu _ hxt
    have h2 : n' ^ Nat.card U * t⁻¹ = t⁻¹ * n' ^ Nat.card U := by
      calc n' ^ Nat.card U * t⁻¹ = t⁻¹ * (t * n' ^ Nat.card U) * t⁻¹ := by group
        _ = t⁻¹ * (n' ^ Nat.card U * t) * t⁻¹ := by rw [hct]
        _ = t⁻¹ * n' ^ Nat.card U := by group
    calc x * t * t⁻¹ * n' ^ Nat.card U = x * t * (t⁻¹ * n' ^ Nat.card U) := by group
      _ = x * t * (n' ^ Nat.card U * t⁻¹) := by rw [h2]
      _ = (x * t * n' ^ Nat.card U) * t⁻¹ := by group
      _ = n' ^ Nat.card U * (x * t) * t⁻¹ := by rw [h1]
      _ = n' ^ Nat.card U * (x * t * t⁻¹) := by group

end Hyp

end CFSG.ComponentClassification.Asc76X.HallDihedral
