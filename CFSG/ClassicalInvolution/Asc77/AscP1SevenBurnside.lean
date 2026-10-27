module

public import CFSG.ClassicalInvolution.Asc77.AscL62Pair
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.ClassicalInvolution.Asc77.Thompson

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_fixed_mem_of_odd {V : Subgroup G} (hV : IsPGroup 2 ↥V) {C : Set G}
    (hC : ∀ v ∈ V, ∀ c ∈ C, v * c * v⁻¹ ∈ C) (hodd : Odd (Nat.card C)) :
    ∃ c ∈ C, ∀ v ∈ V, v * c * v⁻¹ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥V ↥C :=
    { smul := fun v c => ⟨(v : G) * c * (v : G)⁻¹, hC v v.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        show ((1 : ↥V) : G) * c * ((1 : ↥V) : G)⁻¹ = c
        simp)
      mul_smul := fun v w c => Subtype.ext (by
        show ((v * w : ↥V) : G) * c * ((v * w : ↥V) : G)⁻¹ =
          (v : G) * ((w : G) * c * (w : G)⁻¹) * (v : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hnd : ¬ 2 ∣ Nat.card ↥C := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hc⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card ↥C hnd
  refine ⟨c, c.2, fun v hv => ?_⟩
  have h1 : (⟨v, hv⟩ : ↥V) • c = c := hc ⟨v, hv⟩
  exact congrArg Subtype.val h1

theorem exists_odd_complement_of_isCyclic [Finite G] {H U : Subgroup G} (hU : IsSylow2In U H)
    (hUc : IsCyclic ↥U) :
    ∃ N₀ : Subgroup G, N₀ ≤ H ∧ Odd (Nat.card N₀) ∧
      (∀ h ∈ H, ∃ n ∈ N₀, ∃ u ∈ U, h = n * u) ∧
      ∀ x ∈ H, Odd (orderOf x) → x ∈ N₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Sylow 2 ↥H := AscL62.sylowOfIsSylow2In'' hU with hS
  have hSU : ∀ b : ↥H, b ∈ (S : Subgroup ↥H) ↔ (b : G) ∈ U := fun b => Iff.rfl
  have hScyc : IsCyclic ↥(S : Subgroup ↥H) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hU.1)).mpr hUc
  obtain ⟨-, hmul, hinf, ⟨hNn, hNodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  set N : Subgroup ↥H := CFSG.pPrimeCore 2 ↥H with hN
  refine ⟨N.map H.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hNodd
  · intro h hh
    have hmem : (⟨h, hh⟩ : ↥H) ∈ (N : Set ↥H) * (S : Set ↥H) := by rw [hmul]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
    refine ⟨a, ⟨a, ha, rfl⟩, b, (hSU b).mp hb, ?_⟩
    have := congrArg Subtype.val hab
    simpa using this.symm
  · intro x hx hodd
    have hmem : (⟨x, hx⟩ : ↥H) ∈ (N : Set ↥H) * (S : Set ↥H) := by rw [hmul]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
    have hNn' : N.Normal := hNn
    have hb1 : b = 1 := by
      have hmk : (QuotientGroup.mk' N) (⟨x, hx⟩ : ↥H) = (QuotientGroup.mk' N) b := by
        rw [← hab, map_mul,
          show (QuotientGroup.mk' N) a = 1 from (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
      have h1 : orderOf ((QuotientGroup.mk' N) b) ∣ orderOf (⟨x, hx⟩ : ↥H) := by
        rw [← hmk]
        exact orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨b, hb⟩
      have h2 : orderOf ((QuotientGroup.mk' N) b) ∣ 2 ^ k := by
        rw [← hk, Subgroup.orderOf_mk]
        exact orderOf_map_dvd _ _
      have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
      have h4 : (QuotientGroup.mk' N) b = 1 := orderOf_eq_one_iff.mp h3
      have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).mp h4
      have hbinf : b ∈ N ⊓ (S : Subgroup ↥H) := ⟨hbN, hb⟩
      rw [hinf] at hbinf
      exact Subgroup.mem_bot.mp hbinf
    rw [hb1, mul_one] at hab
    exact ⟨a, ha, by rw [hab]; rfl⟩

end CFSG.ClassicalInvolution.Asc77.Thompson
