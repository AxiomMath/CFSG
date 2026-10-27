module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

abbrev blockInvolutions (J : Subgroup G) : Set G :=
  {t | orderOf t = 2 ∧ ∃ K ∈ block J, t ∈ centralizer (K : Set G)}

theorem conj_mem_centralizer_conjSub {K : Subgroup G} {t : G} (ht : t ∈ centralizer (K : Set G))
    (g : G) : g * t * g⁻¹ ∈ centralizer (conjSub g K : Set G) := by
  rw [← conjSub_centralizer]
  exact ⟨t, ht, by simp⟩

theorem orderOf_inv_mul_mul (g t : G) : orderOf (g⁻¹ * t * g) = orderOf t := by
  rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp, MulEquiv.orderOf_eq]

section Transporter

variable [Finite G] {J : Subgroup G}

theorem inv_mul_mul_mem_blockInvolutions (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {h : G}
    (hh : h ∈ normalizer (blockGroup J : Set G)) {t : G} (ht : t ∈ blockInvolutions J) :
    h⁻¹ * t * h ∈ blockInvolutions J := by
  obtain ⟨ht2, K, hK, htK⟩ := ht
  refine ⟨by rw [orderOf_inv_mul_mul, ht2], conjSub h⁻¹ K, ?_, ?_⟩
  · exact ((mem_normalizer_blockGroup_iff hq hJ heven h⁻¹).1 (inv_mem hh) K).1 hK
  · have := conj_mem_centralizer_conjSub htK h⁻¹
    rwa [inv_inv] at this

theorem blockInvolutions_subset (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    blockInvolutions J ⊆ normalizer (blockGroup J : Set G) := by
  rintro t ⟨ht2, K, hK, htK⟩
  exact centralizer_le_normalizer_blockGroup hJ heven hK htK ht2 (mem_centralizer_singleton t)
where
  mem_centralizer_singleton (t : G) : t ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.1 hs]

theorem mem_normalizer_of_inv_mul_mul_mem (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {t : G} (ht : t ∈ blockInvolutions J) {g : G}
    (hg : g⁻¹ * t * g ∈ blockInvolutions J) : g ∈ normalizer (blockGroup J : Set G) := by
  obtain ⟨ht2, K, hK, htK⟩ := ht
  obtain ⟨-, L, hL, htL⟩ := hg
  have hKcomp : CFSG.Assembly.IsComponentOf K (centralizer ({t} : Set G)) := by
    obtain ⟨a, rfl⟩ := hK.1
    exact isUniversalComponent_conjSub hJ a t htK ht2
  have hLcomp : CFSG.Assembly.IsComponentOf L (centralizer ({g⁻¹ * t * g} : Set G)) := by
    obtain ⟨a, rfl⟩ := hL.1
    exact isUniversalComponent_conjSub hJ a _ htL (by rw [orderOf_inv_mul_mul, ht2])
  have hKg := isComponentOf_map_conj hKcomp g⁻¹
  rw [map_conj_centralizer_singleton, inv_inv, ← conjSub] at hKg
  have hrel : CommRel L (conjSub g⁻¹ K) := isComponentOf_eq_or_commute hLcomp hKg
  have hKgΔ : conjSub g⁻¹ K ∈ block J :=
    ⟨isConjOf_conjSub hK.1 g⁻¹,
      commRel_trans hJ heven mem_block_self.1 hL.1 (isConjOf_conjSub hK.1 g⁻¹) hL.2 hrel⟩
  have := inv_mem (mem_normalizer_blockGroup hJ heven hK hKgΔ)
  rwa [inv_inv] at this

theorem commuting_block_factor_centralizer_involution_transporter
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) (hJ : IsUniversalComponent J) :
    let H := normalizer (blockGroup J : Set G)
    let D := blockInvolutions J
    D.Nonempty ∧ D ⊆ H ∧ (∀ h ∈ H, ∀ t ∈ D, h⁻¹ * t * h ∈ D) ∧
      (∀ t ∈ D, centralizer ({t} : Set G) ≤ H ∧ {g : G | g⁻¹ * t * g ∈ D} = H) ∧
      (∀ t ∈ D, {s | ∃ g : G, s = g⁻¹ * t * g} ∩ D = {s | ∃ h ∈ H, s = h⁻¹ * t * h}) ∧
      (∀ g : G, (D ∩ {s | ∃ d ∈ D, s = g⁻¹ * d * g}).Nonempty ↔ g ∈ H) ∧
      (2 ≤ (block J).ncard → ∀ K ∈ block J, ∀ t ∈ K, orderOf t = 2 → t ∈ D) ∧
      (H < ⊤ → (∀ t ∈ H, orderOf t = 2 → t ∈ D) → CFSG.IsStronglyEmbedded H) := by
  intro H D
  have hinv : ∀ h ∈ H, ∀ t ∈ D, h⁻¹ * t * h ∈ D := fun h hh t ht =>
    inv_mul_mul_mem_blockInvolutions hq hJ heven hh ht
  have hsub : D ⊆ H := blockInvolutions_subset hJ heven
  have htrans : ∀ t ∈ D, {g : G | g⁻¹ * t * g ∈ D} = H := fun t ht => by
    ext g
    exact ⟨fun hg => mem_normalizer_of_inv_mul_mul_mem hJ heven ht hg, fun hg => hinv g hg t ht⟩
  have hne : D.Nonempty := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (J : Set G)) 2
      (even_iff_two_dvd.1 hCeven)
    exact ⟨t, by rw [Subgroup.orderOf_coe, ht], J, mem_block_self, t.2⟩
  have hDD : ∀ g : G, (D ∩ {s | ∃ d ∈ D, s = g⁻¹ * d * g}).Nonempty ↔ g ∈ H := by
    intro g
    constructor
    · rintro ⟨s, hs, d, hd, rfl⟩
      exact mem_normalizer_of_inv_mul_mul_mem hJ heven hd hs
    · intro hg
      obtain ⟨d, hd⟩ := hne
      exact ⟨g⁻¹ * d * g, hinv g hg d hd, d, hd, rfl⟩
  refine ⟨hne, hsub, hinv, fun t ht => ⟨?_, htrans t ht⟩, fun t ht => ?_, hDD, ?_, ?_⟩
  · obtain ⟨ht2, K, hK, htK⟩ := ht
    exact centralizer_le_normalizer_blockGroup hJ heven hK htK ht2
  · ext s
    constructor
    · rintro ⟨⟨g, rfl⟩, hs⟩
      exact ⟨g, mem_normalizer_of_inv_mul_mul_mem hJ heven ht hs, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, hinv h hh t ht⟩
  · intro hΔ K hK t htK ht2
    have hnt : (block J).Nontrivial := (Set.one_lt_ncard_iff_nontrivial).1 hΔ
    obtain ⟨L, hL, hLK⟩ := hnt.exists_ne K
    rcases commRel_of_mem_block hJ heven hK hL with h | h
    · exact absurd h.symm hLK
    · refine ⟨ht2, L, hL, ?_⟩
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h htK
  · intro hlt hcov
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨hlt.ne, ?_, fun g hg => ?_⟩
    · obtain ⟨d, hd⟩ := hne
      have h2 : orderOf (⟨d, hsub hd⟩ : H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hd.1
      exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
    · rw [← Nat.not_even_iff_odd]
      intro hev
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ CFSG.conjugate H g)) 2
        (even_iff_two_dvd.1 hev)
      have hs2 : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe, hs]
      obtain ⟨hsH, u, huH, hus⟩ := Subgroup.mem_inf.1 s.2
      have hus' : (s : G) = g⁻¹ * u * g := by
        rw [← hus]; simp
      have hu2 : orderOf u = 2 := by rw [← orderOf_inv_mul_mul g u, ← hus', hs2]
      exact hg ((hDD g).1 ⟨s, hcov s hsH hs2, u, hcov u huH hu2, hus'⟩)

end Transporter

end CFSG.LocalAnalysis.ComponentInitial
