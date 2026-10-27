module

public import CFSG.GH74.Uniqueness.SU.SU5J2Emb
public import CFSG.GH74.Uniqueness.SU.SU5J2R

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem mem_zpowers_x0 {s : J2Syl} : s ∈ zpowers x0 ↔ s = 1 ∨ s = x0 := by
  have hne : x0 ≠ 1 := fun h => x0_not_mem_W (by rw [h]; exact W.one_mem)
  have hord : orderOf x0 = 2 := orderOf_eq_prime (by rw [pow_two]; exact x0_sq) hne
  constructor
  · rintro ⟨k, rfl⟩
    show x0 ^ k = 1 ∨ x0 ^ k = x0
    rw [← zpow_mod_orderOf, hord]
    have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · left; rw [h2]; simp
    · right; rw [h2]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem Cx_eq : Cx = zpowers x0 ⊔ Qs := by
  apply le_antisymm
  · intro s hs
    rcases Cx_cases s hs with h1 | h1
    · exact Subgroup.mem_sup_right (mem_Qs.2 ⟨h1, hs⟩)
    · have hq : x0 * s ∈ Qs := mem_Qs.2 ⟨h1, by
        have : ∀ s : J2Syl, s * x0 = x0 * s → (x0 * s) * x0 = x0 * (x0 * s) := by decide +kernel
        exact this s hs⟩
      have h2 : s = x0 * (x0 * s) := by
        rw [← mul_assoc, x0_sq, one_mul]
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers x0)) (Subgroup.mem_sup_right hq)
  · refine sup_le ?_ ?_
    · rintro s hs
      rcases mem_zpowers_x0.1 hs with rfl | rfl
      · exact one_mem _
      · exact rfl
    · intro s hs
      exact (mem_Qs.1 hs).2

theorem zpowers_inf_Qs : zpowers x0 ⊓ Qs = ⊥ := by
  rw [eq_bot_iff]
  rintro s ⟨hs1, hs2⟩
  rw [Subgroup.mem_bot]
  rcases mem_zpowers_x0.1 hs1 with h | h
  · exact h
  · exfalso
    rw [h] at hs2
    exact x0_not_mem_W (mem_Qs.1 hs2).1

theorem z0_mem_Qs : z0 ∈ Qs := by
  rw [mem_Qs]; decide +kernel

theorem Qs_center : ∀ q : J2Syl, q ∈ Qs → ((∀ q' : J2Syl, q' ∈ Qs → q * q' = q' * q) ↔
    (q = 1 ∨ q = z0)) := by decide +kernel

theorem le4_centralizer (s : J2Syl) (hs : s.right ≠ 1) (hs2 : s * s = 1)
    (E : Subgroup J2Syl) (hE : ∀ t ∈ E, t * s = s * t) (hEE : Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 4 := by
  have hE' := isElemAbelian_iff.1 hEE
  have hsub : ∀ t ∈ E, t ∈ ({1, s, z0, s * z0} : Finset J2Syl) := by
    intro t ht
    have h2 : t * t = 1 := by rw [← pow_two]; exact hE'.2 t ht
    have := cert_cent s t hs hs2 (hE t ht) h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact (card_le_card_of_subset_finset hsub).trans Finset.card_le_four

end J2Syl

section Emb2

variable {G : Type*} [Group G]

@[expose] def IsZGen (S : Subgroup G) (z : G) : Prop :=
  z ∈ S ∧ z ≠ 1 ∧ ∀ y ∈ S, ((∀ s ∈ S, y * s = s * y) ↔ (y = 1 ∨ y = z))

theorem IsZGen.unique {S : Subgroup G} {z z' : G} (hz : IsZGen S z) (hz' : IsZGen S z') :
    z = z' := by
  have hc : ∀ s ∈ S, z' * s = s * z' := (hz'.2.2 z' hz'.1).2 (Or.inr rfl)
  have h1 := (hz.2.2 z' hz'.1).1 hc
  rcases h1 with h | h
  · exact absurd h hz'.2.1
  · exact h.symm

theorem isZGen_f {f : J2Syl →* G} (hf : Function.Injective f) : IsZGen f.range (f J2Syl.z0) := by
  refine ⟨⟨_, rfl⟩, ?_, ?_⟩
  · intro h1
    exact J2Syl.z0_ne_one (hf (by rw [h1, map_one]))
  · rintro _ ⟨m, rfl⟩
    constructor
    · intro hc
      have h2 : ∀ t : J2Syl, m * t = t * m := fun t =>
        hf (by rw [map_mul, map_mul]; exact hc (f t) ⟨t, rfl⟩)
      rcases (J2Syl.center_iff m).1 h2 with h3 | h3
      · left; rw [h3, map_one]
      · right; rw [h3]
    · rintro (h1 | h1) _ ⟨t, rfl⟩
      · have : m = 1 := hf (by rw [h1, map_one])
        rw [this]; simp
      · have : m = J2Syl.z0 := hf h1
        rw [this]
        have := (J2Syl.center_iff J2Syl.z0).2 (Or.inr rfl) t
        rw [← map_mul, ← map_mul, this]

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem exists_zgen (h : J2Emb S T x) : ∃ z, IsZGen S z := by
  obtain ⟨f, hf, rfl, -, -⟩ := h
  exact ⟨_, isZGen_f hf⟩

theorem zgen_facts (h : J2Emb S T x) {z : G} (hz : IsZGen S z) : z ^ 2 = 1 ∧ z ∈ Zc T := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  rw [pow_two, ← map_mul, J2Syl.z0_sq, map_one, Zc_map hf, J2Syl.Zc_W]
  exact ⟨rfl, Subgroup.mem_map_of_mem f J2Syl.z0_mem_U⟩

theorem facts_Q (h : J2Emb S T x) {z : G} (hz : IsZGen S z) :
    Nonempty (↥(T ⊓ centralizer {x}) ≃* QuaternionGroup 2) ∧ z ∈ T ⊓ centralizer {x} ∧
    (∀ q ∈ T ⊓ centralizer {x}, ((∀ q' ∈ T ⊓ centralizer {x}, q * q' = q' * q) ↔
      (q = 1 ∨ q = z))) ∧
    S ⊓ centralizer {x} = zpowers x ⊔ (T ⊓ centralizer {x}) ∧
    zpowers x ⊓ (T ⊓ centralizer {x}) = ⊥ ∧ Nat.card ↥(S ⊓ centralizer {x}) = 16 := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  have hQ : J2Syl.W.map f ⊓ centralizer {f J2Syl.x0} = J2Syl.Qs.map f := by
    ext g
    constructor
    · rintro ⟨hgW, hgc⟩
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hgW
      refine Subgroup.mem_map.2 ⟨m, J2Syl.mem_Qs.2 ⟨hm, ?_⟩, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hgc (f J2Syl.x0) rfl
      exact hf (by rw [map_mul, map_mul]; exact h1.symm)
    · intro hg
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨hmW, hmc⟩ := J2Syl.mem_Qs.1 hm
      refine ⟨Subgroup.mem_map_of_mem f hmW, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ rfl
      rw [← map_mul, ← map_mul, hmc]
  have hC : f.range ⊓ centralizer {f J2Syl.x0} = J2Syl.Cx.map f := by
    ext g
    constructor
    · rintro ⟨⟨m, rfl⟩, hgc⟩
      refine Subgroup.mem_map.2 ⟨m, ?_, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hgc (f J2Syl.x0) rfl
      exact hf (by rw [map_mul, map_mul]; exact h1.symm)
    · intro hg
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
      refine ⟨⟨m, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ rfl
      rw [← map_mul, ← map_mul]
      exact congrArg f (J2Syl.mem_Cx.1 hm).symm
  rw [hQ, hC]
  refine ⟨⟨(Subgroup.equivMapOfInjective J2Syl.Qs f hf).symm.trans J2Syl.Qs_equiv.some⟩,
    Subgroup.mem_map_of_mem f J2Syl.z0_mem_Qs, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    constructor
    · intro hc
      have h2 : ∀ q' : J2Syl, q' ∈ J2Syl.Qs → m * q' = q' * m := fun q' hq' =>
        hf (by rw [map_mul, map_mul]; exact hc (f q') (Subgroup.mem_map_of_mem f hq'))
      rcases (J2Syl.Qs_center m hm).1 h2 with h3 | h3
      · left; rw [h3, map_one]
      · right; rw [h3]
    · intro hc q' hq'
      obtain ⟨q'', hq'', rfl⟩ := Subgroup.mem_map.1 hq'
      have h2 := (J2Syl.Qs_center m hm).2 (by
        rcases hc with h3 | h3
        · left; exact hf (by rw [h3, map_one])
        · right; exact hf h3)
      rw [← map_mul, ← map_mul, h2 q'' hq'']
  · rw [J2Syl.Cx_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
  · rw [← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ f hf, J2Syl.zpowers_inf_Qs,
      Subgroup.map_bot]
  · rw [Subgroup.card_map_of_injective hf, J2Syl.card_Cx]

end J2Emb

end Emb2

end CFSG.GH74.Uniqueness.SU.SU5
