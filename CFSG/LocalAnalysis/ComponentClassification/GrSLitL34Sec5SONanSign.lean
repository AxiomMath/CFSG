module

public import CFSG.GroupTheory.Transfer.YoshidaParity
public import Mathlib.GroupTheory.IsPerfect


public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open Subgroup

theorem false_of_index_two_of_fusion {G : Type} [Group G] [Finite G] (hperf : Group.IsPerfect G)
    {M H : Subgroup G} (hHM : H ≤ M) (hH2 : H.relIndex M = 2) (hodd : Odd M.index) {t : G}
    (ht : t * t = 1) (_htM : t ∈ M) (htH : t ∉ H)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m) : False := by
  classical
  have hHn : (H.subgroupOf M).Normal := by
    apply Subgroup.normal_of_index_eq_two
    rw [← Subgroup.relIndex]
    exact hH2
  have hconj : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := by
    intro m hm h hh
    have := hHn.conj_mem ⟨h, hHM hh⟩ (mem_subgroupOf.mpr hh) ⟨m, hm⟩
    simpa [mem_subgroupOf] using this
  have hfree : ∀ ω : G ⧸ H, t • ω ≠ ω := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H g =>
      intro hfix
      have hmem : g⁻¹ * t * g ∈ H := by
        have h1 : ((t * g : G) : G ⧸ H) = (g : G ⧸ H) := hfix
        rw [QuotientGroup.eq] at h1
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
        have h2 : (t * g)⁻¹ * g = g⁻¹ * t * g := by
          rw [mul_inv_rev, htinv, mul_assoc]
        rwa [h2] at h1
      obtain ⟨m, hm, hgm⟩ := hfus g (hHM hmem)
      rw [hgm] at hmem
      have := hconj m hm _ hmem
      rw [show m * (m⁻¹ * t * m) * m⁻¹ = t by group] at this
      exact htH this
  have htc : t ∈ _root_.commutator G := by
    rw [@Group.IsPerfect.commutator_eq_top G _ hperf]
    exact mem_top t
  have h4 := CFSG.GroupTheory.four_dvd_card_sub_card_fixedBy (Ω := G ⧸ H) (pow_two t ▸ ht) htc
  have hfix : Nat.card (MulAction.fixedBy (G ⧸ H) t) = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun ω => hfree ω.1 ω.2⟩
  have hcard : Nat.card (G ⧸ H) = 2 * M.index := by
    rw [← Subgroup.index, ← Subgroup.relIndex_mul_index hHM, hH2]
  rw [hfix, Nat.sub_zero, hcard] at h4
  obtain ⟨k, hk⟩ := hodd
  omega

theorem exists_index_two_of_pair {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {N : Subgroup ↥M} [N.Normal] {L : Subgroup (↥M ⧸ N)} {t : G} (htM : t ∈ M)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ x : ↥M ⧸ N, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' N ⟨t, htM⟩)).toMonoidHom) :
    ∃ H : Subgroup G, H ≤ M ∧ H.relIndex M = 2 ∧ t ∉ H := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set tb := π ⟨t, htM⟩ with htb
  set Hb : Subgroup (↥M ⧸ N) := normalizer (L : Set (↥M ⧸ N)) with hHb
  have hmemHb : ∀ x, x ∈ Hb ↔ L.map (MulAut.conj x).toMonoidHom = L := fun x =>
    mem_normalizer_iff_map_conj_eq
  have hmul : ∀ (x y : ↥M ⧸ N) (K : Subgroup (↥M ⧸ N)), K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y K
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hone : ∀ K : Subgroup (↥M ⧸ N), K.map (MulAut.conj (1 : ↥M ⧸ N)).toMonoidHom = K := by
    intro K
    rw [map_one]
    exact Subgroup.map_id K
  have hinv : ∀ (x : ↥M ⧸ N) (K : Subgroup (↥M ⧸ N)),
      K.map (MulAut.conj x).toMonoidHom = L ↔ K = L.map (MulAut.conj x⁻¹).toMonoidHom := by
    intro x K
    constructor
    · rintro rfl
      rw [← hmul, inv_mul_cancel, hone]
    · rintro rfl
      rw [← hmul, mul_inv_cancel, hone]
  have hindex : Hb.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨tb, fun b => ?_⟩
    rw [hmemHb, hmemHb, hmul, hinv, hinv]
    rcases hpair b⁻¹ with h | h
    · rw [h]
      exact Or.inr ⟨rfl, hne⟩
    · rw [h]
      exact Or.inl ⟨rfl, fun h' => hne h'.symm⟩
  refine ⟨(Hb.comap π).map M.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.relIndex]
    change (((Hb.comap π).map M.subtype).comap M.subtype).index = 2
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective,
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hindex]
  · intro ht
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp ht
    have hy' : y = ⟨t, htM⟩ := Subtype.ext hyt
    rw [hy', Subgroup.mem_comap, hmemHb] at hy
    exact hne hy

end CFSG.ComponentClassification.GrSLit.L34Sec5S
