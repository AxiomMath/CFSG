module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G]

theorem gamma_card_mul_le {X Y Z : Subgroup G} (hX : X ≤ Z) (hY : Y ≤ Z) :
    Nat.card X * Nat.card Y ≤ Nat.card ↥(X ⊓ Y) * Nat.card Z := by
  have h1 := Subgroup.relIndex_mul_card X Y
  have h2 := Subgroup.relIndex_mul_card X Z
  rw [inf_eq_left.mpr hX] at h2
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  have h3 : X.relIndex Y ≤ X.relIndex Z :=
    Subgroup.relIndex_le_of_le_right hY (fun h0 => by rw [h0, zero_mul] at h2; omega)
  calc Nat.card X * Nat.card Y
      = Nat.card X * (X.relIndex Y * Nat.card ↥(X ⊓ Y)) := by rw [h1]
    _ ≤ Nat.card X * (X.relIndex Z * Nat.card ↥(X ⊓ Y)) := by gcongr
    _ = (X.relIndex Z * Nat.card X) * Nat.card ↥(X ⊓ Y) := by ring
    _ = Nat.card ↥(X ⊓ Y) * Nat.card Z := by rw [h2, mul_comm]

theorem gamma_exists_inv_of_two_dvd {K : Subgroup G} (h : 2 ∣ Nat.card K) :
    ∃ s ∈ K, orderOf s = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem gamma_exists_inv_of_card_lt {X Y Z : Subgroup G} (hX : X ≤ Z) (hY : Y ≤ Z)
    (hlt : Nat.card Z < Nat.card X * Nat.card Y) {k : ℕ}
    (hk : Nat.gcd (Nat.card X) (Nat.card Y) ∣ 2 ^ k) : ∃ s ∈ X ⊓ Y, orderOf s = 2 := by
  have hdvdX : Nat.card ↥(X ⊓ Y) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
  have hdvdY : Nat.card ↥(X ⊓ Y) ∣ Nat.card Y := Subgroup.card_dvd_of_le inf_le_right
  have hdvdg : Nat.card ↥(X ⊓ Y) ∣ Nat.gcd (Nat.card X) (Nat.card Y) := Nat.dvd_gcd hdvdX hdvdY
  have hdvd2 : Nat.card ↥(X ⊓ Y) ∣ 2 ^ k := hdvdg.trans hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hne1 : Nat.card ↥(X ⊓ Y) ≠ 1 := by
    intro h1
    have hle := gamma_card_mul_le hX hY
    rw [h1, one_mul] at hle
    omega
  have hj0 : j ≠ 0 := by
    intro h0
    exact hne1 (by rw [hj, h0, pow_zero])
  exact gamma_exists_inv_of_two_dvd (by rw [hj]; exact dvd_pow_self 2 hj0)

variable {a z : G}

theorem gamma_card_orb2A (H : GammaHyps a z) : Nat.card ↥(orb2A a a) = 2200 := by
  obtain ⟨b, hb⟩ := ((H.hT5.self).partition.orbit 0).nonempty
  have hb2 : b ∈ orb2A a a := hb
  have hcomm : a * b = b * a := H.comm_of_orb2A (IsConj.refl a) hb2
  have ha' : a ∈ orb2A b b := by
    refine ⟨hb2.1.symm, ?_⟩
    exact (gamma_isConj_iff hb2.1 (b * a)).2 (hcomm ▸ hb2.2)
  have hcard_sbase : Nat.card ↥(sBase b a) = 2198 :=
    (H.hT4 b z hb2.1 (IsConj.refl z)).card a ha'
  have hset : orb2A a a = insert b (insert (b * a) (sBase b a)) := by
    ext c
    constructor
    · intro hc
      by_cases hcb : c = b
      · rw [hcb]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · by_cases hcba : c = b * a
        · rw [hcba]
          exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
        · refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr ?_)))
          exact ⟨(gamma_isConj_iff hb2.1 c).2 hc.1,
            (gamma_isConj_iff hb2.1 (a * c)).2 hc.2, hcb, hcba⟩
    · intro hc
      rw [Set.mem_insert_iff] at hc
      rcases hc with hcb | hc
      · rw [hcb]
        exact hb2
      · rw [Set.mem_insert_iff] at hc
        rcases hc with hcba | hc
        · rw [hcba]
          refine ⟨hcomm ▸ hb2.2, ?_⟩
          have h1 : a * (b * a) = b := by
            rw [← mul_assoc, hcomm, mul_assoc, H.mul_self_a (IsConj.refl a), mul_one]
          rw [h1]
          exact hb2.1
        · exact ⟨(gamma_isConj_iff hb2.1 c).1 hc.1,
            (gamma_isConj_iff hb2.1 (a * c)).1 hc.2.1⟩
  have hb_ne_ba : b ≠ b * a := by
    intro h
    have h1 : (1 : G) = a := mul_left_cancel (by simpa using h : b * 1 = b * a)
    exact H.ne_one_a (IsConj.refl a) h1.symm
  have hb_not : b ∉ insert (b * a) (sBase b a) := by
    rw [Set.mem_insert_iff, not_or]
    exact ⟨hb_ne_ba, fun hs => hs.2.2.1 rfl⟩
  have hba_not : b * a ∉ sBase b a := fun hs => hs.2.2.2 rfl
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem hb_not,
    Set.ncard_insert_of_notMem hba_not, ← Nat.card_coe_set_eq, hcard_sbase]

theorem gamma_card_Gx (H : GammaHyps a z) : Nat.card ↥(Gx a) = 177408000 := by
  obtain ⟨c, hc⟩ := ((H.hT5.self).partition.orbit 0).nonempty
  have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 80640 := by
    simpa using (H.hT5.self).card_stab 0 c hc
  have hh := IsConjOrbit.card_mul_card_stab ((H.hT5.self).partition.orbit 0) hc
  rw [hstab] at hh
  have hlen : Nat.card ↥(tab5Set a z 0) = 2200 := by
    change Nat.card ↥(orb2A a a) = 2200
    exact gamma_card_orb2A H
  rw [hlen] at hh
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
