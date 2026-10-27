module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Gen
public import CFSG.GF2Type.Aschbacher1976Common.CyclicTICommute

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint CFSG.EvenSporadicStandard.Finkelstein77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_containing {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G}
    (hh : (Zc z).map (MulAut.conj h).toMonoidHom ≤ Hz z) :
    ∃ T : Subgroup G, T ≤ Hz z ∧ IsPGroup 2 T ∧
      (∀ Q : Subgroup G, Q ≤ Hz z → IsPGroup 2 Q → T ≤ Q → Q = T) ∧
      Fz z ≤ T ∧ (Zc z).map (MulAut.conj h).toMonoidHom ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup ↥(Hz z) := ((Zc z).map (MulAut.conj h).toMonoidHom).subgroupOf (Hz z)
  have hKcard : Nat.card ↥K = 4 := by
    have e := Subgroup.subgroupOfEquivOfLe hh
    rw [Nat.card_congr e.toEquiv, Subgroup.card_map_of_injective (MulAut.conj h).injective,
      card_Zc hZ hz]
  have hK : IsPGroup 2 ↥K := IsPGroup.of_card (n := 2) (by rw [hKcard]; norm_num)
  have hN : IsPGroup 2 (pCore 2 ↥(Hz z)) := pCore_isPGroup
  have hP : IsPGroup 2 ↥(K ⊔ pCore 2 ↥(Hz z)) := IsPGroup.to_sup_of_normal_right hK hN
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hKQ : K ≤ Q.toSubgroup := le_trans le_sup_left hQ
  have hNQ : pCore 2 ↥(Hz z) ≤ Q.toSubgroup := le_trans le_sup_right hQ
  refine ⟨Q.toSubgroup.map (Hz z).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · exact Q.isPGroup'.map (Hz z).subtype
  · intro Q' hQ'H hQ'p hTQ'
    have hQ''p : IsPGroup 2 ↥(Q'.subgroupOf (Hz z)) :=
      hQ'p.of_equiv (Subgroup.subgroupOfEquivOfLe hQ'H).symm
    have hle : Q.toSubgroup ≤ Q'.subgroupOf (Hz z) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hTQ' (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have heq := Q.is_maximal' hQ''p hle
    have h1 : (Q'.subgroupOf (Hz z)).map (Hz z).subtype = Q' := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQ'H]
    rw [← h1, heq]
  · rw [Fz_eq_inSubgroup_pCore hZ hz]
    exact Subgroup.map_mono hNQ
  · have hmap : (Zc z).map (MulAut.conj h).toMonoidHom = K.map (Hz z).subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hh]
    rw [hmap]
    exact Subgroup.map_mono hKQ

theorem map_conj_eq_conjugate {z h : G} :
    (Zc z).map (MulAut.conj h).toMonoidHom = conjugate (Zc z) h⁻¹ := by
  unfold conjugate
  simp

theorem commute_Zc_map {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {T : Subgroup G}
    (hT : IsPGroup 2 T) (hZT : Zc z ≤ T) {h : G}
    (hh : (Zc z).map (MulAut.conj h).toMonoidHom ≤ T) :
    ∀ x ∈ Zc z, ∀ y ∈ (Zc z).map (MulAut.conj h).toMonoidHom, x * y = y * x := by
  have hA : IsCyclic ↥(Zc z) := by
    obtain ⟨Z, A, hZeq, hcyc, -⟩ := unpack hZ hz
    rw [hZeq]
    exact hcyc
  have hA2 : IsPGroup 2 ↥(Zc z) := IsPGroup.of_card (n := 2) (by rw [card_Zc hZ hz]; norm_num)
  have hA4 : 4 ≤ Nat.card ↥(Zc z) := by rw [card_Zc hZ hz]
  have hg : conjugate (Zc z) 1 ≤ T := by
    rw [conjugate_Zc_eq hZ hz (Subgroup.one_mem _)]
    exact hZT
  have hh' : conjugate (Zc z) h⁻¹ ≤ T := by
    rw [← map_conj_eq_conjugate]
    exact hh
  have key := CFSG.GF2Type.Aschbacher1976Common.commute_of_conjugate_le hA hA2 hA4
    (TI_Zc hZ hz) hT hg hh'
  intro x hx y hy
  rw [← map_conj_eq_conjugate] at key
  refine key x ?_ y ?_ 
  · rw [conjugate_Zc_eq hZ hz (Subgroup.one_mem _)]
    exact hx
  · exact hy

theorem sq_mem_of_card_two {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {T : Subgroup G}
    (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) (hT : Nat.card ↥T = 2 * Nat.card ↥(Fz z)) {y : G}
    (hy : y ∈ T) (hyF : y ∉ Fz z) : y ^ 2 ∈ Fz z := by
  have hnormal : ((Fz z).subgroupOf T).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_Fz hZ hz (hTH g.2) hn
    simpa using this
  have hcard : Nat.card (↥T ⧸ (Fz z).subgroupOf T) = 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Fz z).subgroupOf T)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv] at h1
    have hF : 0 < Nat.card ↥(Fz z) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hF (h1.symm.trans (hT.trans (by ring)))
  have hqdvd : orderOf (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ (Fz z).subgroupOf T) ∣ 2 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hq1 : (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ (Fz z).subgroupOf T) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hyF h1
  have hq2 : orderOf (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ (Fz z).subgroupOf T) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hqdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq1
    · exact h
  have hsq := pow_orderOf_eq_one (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ (Fz z).subgroupOf T)
  rw [hq2, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hsq
  simpa using hsq

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
