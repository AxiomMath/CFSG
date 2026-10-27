module

public import CFSG.Walter.AStar.Subnormal
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.LargeExtraspecial.S5

open Subgroup

variable {X : Type*} [Group X]

@[expose] def IsSylowTwoIn (P H : Subgroup X) : Prop :=
  P ≤ H ∧ IsPGroup 2 P ∧ ¬ 2 ∣ P.relIndex H

theorem relIndex_map_dvd {Y : Type*} [Group Y] (f : X →* Y) {P K : Subgroup X}
    (hPK : P ≤ K) : (P.map f).relIndex (K.map f) ∣ P.relIndex K := by
  have e : (P.subgroupOf K).map (f.subgroupMap K) = (P.map f).subgroupOf (K.map f) := by
    ext ⟨b, hb⟩
    rw [mem_subgroupOf, mem_map, mem_map]
    constructor
    · rintro ⟨y, hy, hyb⟩
      exact ⟨y, mem_subgroupOf.mp hy, congrArg Subtype.val hyb⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hPK hy⟩, mem_subgroupOf.mpr hy, rfl⟩
  have h := index_map_dvd (H := P.subgroupOf K) (f.subgroupMap_surjective K)
  rw [e] at h
  exact h

namespace IsSylowTwoIn

variable {P H : Subgroup X}

theorem le (h : IsSylowTwoIn P H) : P ≤ H := h.1

theorem isPGroup (h : IsSylowTwoIn P H) : IsPGroup 2 P := h.2.1

theorem not_dvd (h : IsSylowTwoIn P H) : ¬ 2 ∣ P.relIndex H := h.2.2

theorem exists_pow_eq_one (h : IsSylowTwoIn P H) {x : X} (hx : x ∈ P) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := h.isPGroup ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem eq_of_le [Finite X] (h : IsSylowTwoIn P H) {Q : Subgroup X} (hPQ : P ≤ Q) (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) : Q = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := relIndex_mul_relIndex P Q H hPQ hQH
  have hpQ : IsPGroup 2 (P.subgroupOf Q) :=
    (h.isPGroup).of_equiv (subgroupOfEquivOfLe hPQ).symm
  have hQ' : IsPGroup 2 Q := hQ
  obtain ⟨n, hn⟩ := hQ'.index (P.subgroupOf Q)
  have hrel : P.relIndex Q = 2 ^ n := hn
  rcases n with _ | n
  · rw [pow_zero] at hrel
    exact le_antisymm (relIndex_eq_one.mp hrel) hPQ
  · exfalso
    apply h.not_dvd
    rw [← hmul, hrel, pow_succ]
    exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

theorem map {Y : Type*} [Group Y] (h : IsSylowTwoIn P H) (f : X →* Y) :
    IsSylowTwoIn (P.map f) (H.map f) := by
  refine ⟨map_mono h.le, h.isPGroup.map f, fun hd => h.not_dvd ?_⟩
  exact hd.trans (relIndex_map_dvd f h.le)

theorem ne_bot [Finite X] (h : IsSylowTwoIn P H) (heven : 2 ∣ Nat.card H) : P ≠ ⊥ := by
  intro hP
  apply h.not_dvd
  rw [hP, relIndex_bot_left]
  exact heven

end IsSylowTwoIn

theorem exists_isSylowTwoIn_ge [Finite X] {H P : Subgroup X} (hPH : P ≤ H)
    (hP : IsPGroup 2 P) : ∃ T : Subgroup X, IsSylowTwoIn T H ∧ P ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hsub : ((Q : Subgroup H).map H.subtype).subgroupOf H = (Q : Subgroup H) :=
    comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · change ¬ 2 ∣ (((Q : Subgroup H).map H.subtype).subgroupOf H).index
    rw [hsub]
    exact Sylow.not_dvd_index Q
  · intro x hx
    exact ⟨⟨x, hPH hx⟩, hQ hx, rfl⟩

theorem IsSylowTwoIn.card_eq [Finite X] {P H : Subgroup X} (h : IsSylowTwoIn P H) :
    Nat.card P = 2 ^ (Nat.card H).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 H :=
    (h.isPGroup.of_equiv (subgroupOfEquivOfLe h.le).symm).toSylow h.not_dvd
  have h1 := Sylow.card_eq_multiplicity Q
  rw [← h1]
  exact (Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv).symm

theorem isSylowTwoIn_of_card_eq [Finite X] {P H : Subgroup X} (hPH : P ≤ H)
    (hc : Nat.card P = 2 ^ (Nat.card H).factorization 2) : IsSylowTwoIn P H := by
  refine ⟨hPH, IsPGroup.of_card hc, ?_⟩
  intro hdvd
  have h1 := relIndex_mul_card (H := P) (K := H)
  rw [inf_eq_left.2 hPH, hc] at h1
  have hHpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ^ ((Nat.card H).factorization 2 + 1) ∣ Nat.card H := by
    have h3 : 2 ^ ((Nat.card H).factorization 2 + 1) ∣
        P.relIndex H * 2 ^ (Nat.card H).factorization 2 := by
      rw [pow_succ']
      exact mul_dvd_mul hdvd dvd_rfl
    exact h3.trans (dvd_of_eq h1)
  have := (Nat.prime_two.pow_dvd_iff_le_factorization hHpos).1 h2
  omega

theorem IsSylowTwoIn.inf_of_isSubnormal [Finite X] {P H A : Subgroup X}
    (h : IsSylowTwoIn P H) (hA : CFSG.Open.IsSubnormal A H) : IsSylowTwoIn (P ⊓ A) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH := CFSG.ClassicalInvolution.isSubnormal_le hA
  let Q : Sylow 2 H :=
    (h.isPGroup.of_equiv (subgroupOfEquivOfLe h.le).symm).toSylow h.not_dvd
  have hsubA : (A.subgroupOf H).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      ((isSubnormal_subgroupOf_top_iff hAH).mpr hA) Subgroup.IsSubnormal.top
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsubA
  have hcard : Nat.card (P ⊓ A : Subgroup X) = Nat.card R := by
    have e1 : ((R : Subgroup (A.subgroupOf H)).map (A.subgroupOf H).subtype).map H.subtype =
        P ⊓ A := by
      rw [hR]
      change ((P.subgroupOf H) ⊓ (A.subgroupOf H)).map H.subtype = P ⊓ A
      ext x
      simp only [mem_map, mem_inf, mem_subgroupOf, subtype_apply]
      constructor
      · rintro ⟨y, ⟨hyP, hyA⟩, rfl⟩
        exact ⟨hyP, hyA⟩
      · rintro ⟨hxP, hxA⟩
        exact ⟨⟨x, h.le hxP⟩, ⟨hxP, hxA⟩, rfl⟩
    rw [← e1, card_map_of_injective H.subtype_injective,
      card_map_of_injective (A.subgroupOf H).subtype_injective]
  have hcardA : Nat.card (A.subgroupOf H) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv
  refine isSylowTwoIn_of_card_eq inf_le_right ?_
  rw [hcard, Sylow.card_eq_multiplicity R, hcardA]

@[expose] noncomputable def IsSylowTwoIn.toSylow [Finite X] {P K : Subgroup X}
    (h : IsSylowTwoIn P K) : Sylow 2 K :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (h.isPGroup.of_equiv (subgroupOfEquivOfLe h.le).symm).toSylow h.not_dvd

theorem IsSylowTwoIn.coe_toSylow [Finite X] {P K : Subgroup X} (h : IsSylowTwoIn P K) :
    (h.toSylow : Subgroup K) = P.subgroupOf K := rfl

theorem IsSylowTwoIn.exists_conj [Finite X] {P Q K : Subgroup X} (hP : IsSylowTwoIn P K)
    (hQ : IsSylowTwoIn Q K) : ∃ c ∈ K, ∀ y, y ∈ Q ↔ c⁻¹ * y * c ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K hP.toSylow hQ.toSylow
  refine ⟨c, c.2, fun y => ?_⟩
  have hmem : ∀ z : K, z ∈ (hQ.toSylow : Subgroup K) ↔ c⁻¹ * z * c ∈ (hP.toSylow : Subgroup K) := by
    intro z
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  constructor
  · intro hy
    have := (hmem ⟨y, hQ.le hy⟩).mp (show (⟨y, hQ.le hy⟩ : K) ∈ Q.subgroupOf K from hy)
    exact this
  · intro hy
    have hyK : y ∈ K := by
      have h1 : c⁻¹ * y * c ∈ K := hP.le hy
      have := K.mul_mem (K.mul_mem c.2 h1) (K.inv_mem c.2)
      simpa [mul_assoc] using this
    have := (hmem ⟨y, hyK⟩).mpr hy
    exact this

end CFSG.LargeExtraspecial.S5
