module

public import CFSG.GH74.Generic.S45.Final

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section Basic

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

omit [Finite G] in
theorem S45Conf.conj_mem_R (h : S45Conf x K T) {n r : G} (hn : n ∈ normalizer (T : Set G))
    (hr : r ∈ T ⊓ Pre x K) : n * r * n⁻¹ ∈ T ⊓ Pre x K := by
  have hT' : n * r * n⁻¹ ∈ T := conj_mem_T hn hr.1
  refine ⟨hT', ?_⟩
  by_contra hnot
  obtain ⟨g, hg⟩ := (h.fusion _ hT').2 hnot
  have hr' : ∃ g' : G, g' * x * g'⁻¹ = r := ⟨n⁻¹ * g, by
    calc n⁻¹ * g * x * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * x * g⁻¹) * n := by group
      _ = n⁻¹ * (n * r * n⁻¹) * n := by rw [hg]
      _ = r := by group⟩
  exact (h.fusion r hr.1).1 hr' hr.2

theorem S45Conf.exists_conj (h : S45Conf x K T) {t : G} (ht : t ∈ T) (htR : t ∉ Pre x K) :
    ∃ n ∈ normalizer (T : Set G), n * x * n⁻¹ = t := by
  obtain ⟨g, hg⟩ := (h.fusion t ht).2 htR
  obtain ⟨n, hn, hnx⟩ := exists_mem_normalizer_conj_eq h.sylow h.x_mem h.comm (g := g) (by
    rw [hg]; exact ht)
  exact ⟨n, hn, hnx.trans hg⟩

end Basic

section Orbit

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem S45Conf.mem_orbit_x_iff (h : S45Conf x K T) (y : ↥T) :
    y ∈ MulAction.orbit ↥T.normalizerMonoidHom.range (⟨x, h.x_mem⟩ : ↥T) ↔ (y : G) ∉ Pre x K := by
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨⟨n, hn⟩, hf⟩ := f.2
    have hy : ((f • (⟨x, h.x_mem⟩ : ↥T) : ↥T) : G) = n * x * n⁻¹ := by
      show (((f : MulAut ↥T) ⟨x, h.x_mem⟩ : ↥T) : G) = _
      rw [← hf]
      rfl
    rw [hy]
    exact (h.fusion (n * x * n⁻¹) (conj_mem_T hn h.x_mem)).1 ⟨n, rfl⟩
  · intro hy
    obtain ⟨n, hn, hnx⟩ := h.exists_conj y.2 hy
    refine ⟨⟨T.normalizerMonoidHom ⟨n, hn⟩, ⟨_, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hnx

theorem S45Conf.card_orbit_x (h : S45Conf x K T) :
    Nat.card (MulAction.orbit ↥T.normalizerMonoidHom.range (⟨x, h.x_mem⟩ : ↥T)) = 8 := by
  have hset : (MulAction.orbit ↥T.normalizerMonoidHom.range (⟨x, h.x_mem⟩ : ↥T) : Set ↥T) =
      {y : ↥T | (y : G) ∈ Pre x K}ᶜ := by
    ext y
    exact h.mem_orbit_x_iff y
  have hcard := Set.ncard_add_ncard_compl {y : ↥T | (y : G) ∈ Pre x K}
  have hR : ({y : ↥T | (y : G) ∈ Pre x K} : Set ↥T).ncard = 8 := by
    have h1 : ({y : ↥T | (y : G) ∈ Pre x K} : Set ↥T) =
        (((Pre x K).subgroupOf T : Subgroup ↥T) : Set ↥T) := rfl
    rw [h1, ← Nat.card_coe_set_eq]
    have h2 := card_subgroupOf_eq (Pre x K) T
    rw [inf_comm] at h2
    exact h2.trans h.R_card
  have hT : Nat.card ↥T = 16 := h.card
  have hc : ({y : ↥T | (y : G) ∈ Pre x K}ᶜ : Set ↥T).ncard = 8 := by omega
  rw [hset, Nat.card_coe_set_eq]
  exact hc

end Orbit

end CFSG.GH74.Generic.S45
