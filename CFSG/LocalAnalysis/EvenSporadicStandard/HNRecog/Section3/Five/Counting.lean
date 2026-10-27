module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem IsConjOrbit.card_mul_card_stab {K : Subgroup G} [Finite K] {S : Set G} (h : IsConjOrbit K S)
    {c : G} (hc : c ∈ S) : Nat.card ↥S * Nat.card ↥(K ⊓ Gx c) = Nat.card ↥K := by
  classical
  letI : MulAction ↥K G := MulAction.compHom G (MulAut.conj.comp K.subtype)
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  haveI : Fintype (MulAction.orbit ↥K c) :=
    (Finite.finite_mulAction_orbit (M := ↥K) c).fintype
  haveI : Fintype (MulAction.stabilizer ↥K c) := Fintype.ofFinite _
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥K) c
  have hsmul : ∀ (k : ↥K) (x : G), k • x = (k : G) * x * (k : G)⁻¹ := by
    intro k x
    change MulAut.conj (k : G) x = (k : G) * x * (k : G)⁻¹
    rw [MulAut.conj_apply]
  have horbit : (MulAction.orbit ↥K c : Set G) = S := by
    ext x
    constructor
    · intro hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      rw [hsmul]
      exact h.conj_mem (k : G) k.2 c hc
    · intro hx
      obtain ⟨k, hk, hk'⟩ := h.transitive c hc x hx
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨k, hk⟩, by rw [hsmul]; exact hk'⟩
  have hstab : MulAction.stabilizer ↥K c = (K ⊓ Gx c).subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      refine ⟨k.2, ?_⟩
      rw [hsmul] at hk
      rw [mem_Gx]
      exact (mul_inv_eq_iff_eq_mul.mp hk).symm
    · rintro ⟨-, hk⟩
      rw [hsmul]
      rw [mem_Gx] at hk
      exact mul_inv_eq_iff_eq_mul.mpr hk.symm
  have hcardS : Nat.card ↥S = Nat.card (MulAction.orbit ↥K c) :=
    (Nat.card_congr (Set.equivOfEq horbit)).symm
  have hcardK : Nat.card ↥(K ⊓ Gx c) = Nat.card (MulAction.stabilizer ↥K c) := by
    rw [hstab]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ Gx c ≤ K)).toEquiv).symm
  rw [hcardS, hcardK, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact hOS

theorem card_isConj_mul_card_centralizer [Finite G] (a : G) :
    Nat.card {c : G // IsConj a c} * Nat.card ↥(Gx a) = Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) a
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer a]
  have e : Nat.card {s : G // IsConj a s} = Nat.card (MulAction.orbit (ConjAct G) a) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by
      rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  rw [e, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card (α := MulAction.stabilizer (ConjAct G) a),
    Nat.card_eq_fintype_card (α := G), ← ConjAct.card]
  exact h

end CFSG.EvenSporadicStandard.HNRecog.Section3
