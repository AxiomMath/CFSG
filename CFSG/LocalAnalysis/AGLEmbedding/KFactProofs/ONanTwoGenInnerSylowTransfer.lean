module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.QuasithinUnique

theorem card_normalizer_sylow_eq {G : Type*} [Group G] [Finite G] (P Q : Sylow 2 G) :
    Nat.card ↥(Subgroup.normalizer (P : Set G)) = Nat.card ↥(Subgroup.normalizer (Q : Set G)) := by
  have hP := P.card_eq_index_normalizer
  have hQ := Q.card_eq_index_normalizer
  have h1 := Subgroup.card_mul_index (Subgroup.normalizer (P : Set G))
  have h2 := Subgroup.card_mul_index (Subgroup.normalizer (Q : Set G))
  have hidx : (Subgroup.normalizer (P : Set G)).index = (Subgroup.normalizer (Q : Set G)).index :=
    hP.symm.trans hQ
  have hpos : 0 < (Subgroup.normalizer (P : Set G)).index := hP ▸ Nat.card_pos
  rw [hidx] at h1 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem forall_dvd_card_normalizer {G : Type*} [Group G] [Finite G] {m : ℕ} (P : Sylow 2 G)
    (h : m ∣ Nat.card ↥(Subgroup.normalizer (P : Set G))) (Q : Sylow 2 G) :
    m ∣ Nat.card ↥(Subgroup.normalizer (Q : Set G)) :=
  (card_normalizer_sylow_eq P Q) ▸ h

theorem exists_pow_eq_one_of_isPGroup {G : Type*} [Group G] {H : Subgroup G} (hH : IsPGroup 2 H)
    {x : G} (hx : x ∈ H) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_normalizer_of_mem_normalizer_map {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {g : G}
    (hg : (g : G ⧸ Subgroup.center G) ∈ Subgroup.normalizer
      (((P : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) :
        Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G))) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  have ht' : t ∈ (P : Subgroup G) := ht
  have h1 : (((g * t * g⁻¹ : G)) : G ⧸ Subgroup.center G) ∈
      (P : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) := by
    have := (Subgroup.mem_normalizer_iff.1 hg (t : G ⧸ Subgroup.center G)).1
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center G)) ht')
    simpa using this
  obtain ⟨t', ht'P, hπ⟩ := h1
  obtain ⟨z, hz, hyz⟩ : ∃ z ∈ Subgroup.center G, g * t * g⁻¹ = t' * z :=
    ⟨t'⁻¹ * (g * t * g⁻¹), QuotientGroup.eq.1 (by simpa using hπ), by rw [mul_inv_cancel_left]⟩
  have hcen : ∀ x : G, x * z = z * x := Subgroup.mem_center_iff.1 hz
  have hcomm : Commute t' (t' * z) := (Commute.refl t').mul_right (hcen t')
  obtain ⟨k1, hk1⟩ := exists_pow_eq_one_of_isPGroup P.isPGroup' ht'P
  obtain ⟨k2, hk2⟩ := exists_pow_eq_one_of_isPGroup P.isPGroup' ht'
  have hy2 : (t' * z) ^ 2 ^ k2 = 1 := by rw [← hyz, conj_pow, hk2]; group
  have hz2 : z ^ 2 ^ (k1 + k2) = 1 := by
    have h3 : (t' * z) ^ 2 ^ (k1 + k2) = 1 := by rw [add_comm, pow_add, pow_mul, hy2, one_pow]
    have h4 : t'⁻¹ ^ 2 ^ (k1 + k2) = 1 := by
      rw [pow_add, pow_mul, inv_pow, hk1, inv_one, one_pow]
    calc z ^ 2 ^ (k1 + k2) = (t'⁻¹ * (t' * z)) ^ 2 ^ (k1 + k2) := by rw [inv_mul_cancel_left]
      _ = 1 := by rw [hcomm.inv_left.mul_pow, h3, h4, one_mul]
  have hcard : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hz2)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hnorm : (Subgroup.zpowers z).Normal := ⟨fun n hn x => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hxz : Commute x z := hcen x
    rw [(hxz.zpow_right m).mul_inv_cancel]
    exact Subgroup.zpow_mem_zpowers z m⟩
  have hzP : z ∈ (P : Subgroup G) := hcard.le_sylow_of_normal P (Subgroup.mem_zpowers z)
  show g * t * g⁻¹ ∈ (P : Subgroup G)
  rw [hyz]
  exact (P : Subgroup G).mul_mem ht'P hzP

theorem dvd_card_normalizer_center_quotient {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) :
    Nat.card ↥(Subgroup.normalizer (((P : Subgroup G).map
      (QuotientGroup.mk' (Subgroup.center G)) : Subgroup (G ⧸ Subgroup.center G)) :
        Set (G ⧸ Subgroup.center G))) ∣ Nat.card ↥(Subgroup.normalizer (P : Set G)) := by
  set π : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) with hπ
  have hmem : ∀ x ∈ Subgroup.normalizer (P : Set G), π x ∈ Subgroup.normalizer
      (((P : Subgroup G).map π : Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G)) :=
    fun x hx => Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hx)
  let f : ↥(Subgroup.normalizer (P : Set G)) →* ↥(Subgroup.normalizer
      (((P : Subgroup G).map π : Subgroup (G ⧸ Subgroup.center G)) :
        Set (G ⧸ Subgroup.center G))) :=
    (π.comp (Subgroup.normalizer (P : Set G)).subtype).codRestrict _ fun x => hmem x x.2
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨g, mem_normalizer_of_mem_normalizer_map P hb⟩, Subtype.ext rfl⟩
  exact Subgroup.card_dvd_of_surjective hsurj

theorem card_normalizer_map_equiv {C A : Type*} [Group C] [Group A] (e : C ≃* A)
    (S : Subgroup C) :
    Nat.card ↥(Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup A) : Set A)) =
      Nat.card ↥(Subgroup.normalizer (S : Set C)) := by
  rw [← Subgroup.map_equiv_normalizer_eq S e]
  exact Subgroup.card_map_of_injective e.injective

@[expose] noncomputable def sylowOfIsSylowTwoOf {Y : Type*} [Group Y] {L T : Subgroup Y}
    (hT : IsSylowTwoOf T L) : Sylow 2 ↥L :=
  (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2

theorem coe_sylowOfIsSylowTwoOf {Y : Type*} [Group Y] {L T : Subgroup Y}
    (hT : IsSylowTwoOf T L) : (sylowOfIsSylowTwoOf hT : Subgroup ↥L) = T.subgroupOf L :=
  rfl

theorem card_inf_normalizer_eq {Y : Type*} [Group Y] {L T : Subgroup Y} (hTL : T ≤ L) :
    Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y)) =
      Nat.card ↥(Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTL, inf_comm, ← Subgroup.inf_subgroupOf_right]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : Subgroup.normalizer (T : Set Y) ⊓ L ≤ L)).toEquiv).symm

theorem dvd_card_inf_normalizer_of_equiv {Y : Type*} [Group Y] [Finite Y] {L T : Subgroup Y}
    (hT : IsSylowTwoOf T L) {A : Type*} [Group A] (e : (↥L ⧸ Subgroup.center ↥L) ≃* A) {m : ℕ}
    (hm : ∀ Q : Sylow 2 A, m ∣ Nat.card ↥(Subgroup.normalizer (Q : Set A))) :
    m ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y)) := by
  let P : Sylow 2 ↥L := sylowOfIsSylowTwoOf hT
  let Pbar : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _) P
  let Q : Sylow 2 A := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Pbar
  have h1 : m ∣ Nat.card ↥(Subgroup.normalizer
      (((Pbar : Subgroup (↥L ⧸ Subgroup.center ↥L)).map e.toMonoidHom : Subgroup A) : Set A)) :=
    hm Q
  rw [card_normalizer_map_equiv e] at h1
  rw [card_inf_normalizer_eq hT.1]
  exact h1.trans (dvd_card_normalizer_center_quotient P)

end CFSG.AGLEmbedding.TwoGenInner
