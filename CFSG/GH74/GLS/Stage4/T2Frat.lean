module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.RestSetupRank

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem t2C_frattini {C C₁ S : Subgroup G} (hC₁C : C₁ ≤ C)
    (hnorm : ∀ c ∈ C, ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁) (hSC₁ : S ≤ C₁) (hS : IsPGroup 2 ↥S)
    (hSidx : ¬ 2 ∣ S.index) :
    ∀ c ∈ C, ∃ n ∈ C, (∀ s ∈ S, n * s * n⁻¹ ∈ S) ∧ ∃ k ∈ C₁, c = n * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : S ≤ C := hSC₁.trans hC₁C
  let Nn : Subgroup ↥C := C₁.subgroupOf C
  have hNn : Nn.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : G) g.2 (n : G) hn⟩
  let P₀ : Subgroup ↥C := S.subgroupOf C
  have hP₀p : IsPGroup 2 ↥P₀ := hS.comap_subtype
  have hP₀idx : ¬ 2 ∣ P₀.index := fun h =>
    hSidx (h.trans (Subgroup.relIndex_dvd_index_of_le hSC))
  let P : Sylow 2 ↥C := hP₀p.toSylow hP₀idx
  have hPcoe : (P : Subgroup ↥C) = P₀ := IsPGroup.toSylow_coe hP₀p hP₀idx
  have hPN : (P : Subgroup ↥C) ≤ Nn := by
    intro x hx
    rw [hPcoe] at hx
    exact Subgroup.mem_subgroupOf.2 (hSC₁ (Subgroup.mem_subgroupOf.1 hx))
  have hfrat := Sylow.normalizer_sup_eq_top' P hPN
  intro c hc
  have hcmem : (⟨c, hc⟩ : ↥C) ∈ (⊤ : Subgroup ↥C) := trivial
  rw [← hfrat] at hcmem
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 hcmem
  refine ⟨(n : G), n.2, ?_, (k : G), Subgroup.mem_subgroupOf.1 hk, ?_⟩
  · intro s hs
    have hsP : (⟨s, hSC hs⟩ : ↥C) ∈ (P : Subgroup ↥C) := by
      rw [hPcoe]; exact Subgroup.mem_subgroupOf.2 hs
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨s, hSC hs⟩).1 hsP
    rw [hPcoe] at h1
    simpa using Subgroup.mem_subgroupOf.1 h1
  · exact (congrArg Subtype.val hnk).symm

end Frattini

section TwoPart

variable {G : Type} [Group G] [Finite G]

theorem t2C_two_part (n : G) :
    ∃ s m : G, n = s * m ∧ s ∈ Subgroup.zpowers n ∧ m ∈ Subgroup.zpowers n ∧
      (∃ k : ℕ, s ^ (2 ^ k) = 1) ∧ Odd (orderOf m) := by
  have ho0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd ho0
  have hcop : Nat.Coprime (2 ^ a) b := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hb)
  obtain ⟨e₁, he₁a, he₁b⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨e₂, he₂a, he₂b⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨n ^ e₁, n ^ e₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_add]
    conv_lhs => rw [← pow_one n]
    rw [pow_eq_pow_iff_modEq, hab]
    refine ((Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨?_, ?_⟩)
    · simpa using (Nat.ModEq.add he₁a he₂a).symm
    · simpa using (Nat.ModEq.add he₁b he₂b).symm
  · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers n) _
  · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers n) _
  · refine ⟨a, ?_⟩
    have hdvd : b ∣ e₁ := (Nat.modEq_zero_iff_dvd).1 he₁b
    obtain ⟨c, hc⟩ := hdvd
    rw [← pow_mul, hc, show b * c * 2 ^ a = orderOf n * c by rw [hab]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · have hdvd : 2 ^ a ∣ e₂ := (Nat.modEq_zero_iff_dvd).1 he₂a
    obtain ⟨d, hd⟩ := hdvd
    have hmb : (n ^ e₂) ^ b = 1 := by
      rw [← pow_mul, hd, show 2 ^ a * d * b = orderOf n * d by rw [hab]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one hmb)

theorem t2C_mem_of_normalizes {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSidx : ¬ 2 ∣ S.index) {s : G}
    (hsn : ∀ y ∈ S, s * y * s⁻¹ ∈ S) (hs2 : ∃ k : ℕ, s ^ (2 ^ k) = 1) : s ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 G := hS2.toSylow hSidx
  have hQS : (Q : Subgroup G) = S := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨k, hk⟩ := hs2
  have hxp : IsPGroup 2 ↥(Subgroup.zpowers s) := by
    intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (g : G) ^ (2 ^ k) = 1
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hsnorm : s ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_fintype (fun y hy => ?_)
    have hy' : y ∈ S := by rw [← hQS]; exact hy
    have := hsn y hy'
    rw [← hQS] at this
    exact this
  have hmem : s ∈ Subgroup.zpowers s ⊓ Subgroup.normalizer (Q : Set G) :=
    ⟨Subgroup.mem_zpowers s, hsnorm⟩
  rw [hxp.inf_normalizer_sylow Q] at hmem
  rw [← hQS]
  exact hmem.2

end TwoPart

section SylowInf

variable {G : Type} [Group G] [Finite G]

theorem t2C_relIndex_inf_dvd {A : Type} [Group A] [Finite A] (S N : Subgroup A) [N.Normal] :
    (S ⊓ N).relIndex N ∣ S.index := by
  have hrel1 : (S ⊓ N).relIndex S * S.relIndex (S ⊔ N) = (S ⊓ N).relIndex (S ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have hrel2 : (S ⊓ N).relIndex N * N.relIndex (S ⊔ N) = (S ⊓ N).relIndex (S ⊔ N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h2a : N.relIndex (S ⊔ N) = N.relIndex S := Subgroup.relIndex_sup_right S N
  have h2a' : N.relIndex S = (S ⊓ N).relIndex S := (Subgroup.inf_relIndex_left S N).symm
  have hne : (S ⊓ N).relIndex S ≠ 0 := by
    have : ((S ⊓ N).subgroupOf S).FiniteIndex := inferInstance
    exact this.index_ne_zero
  have hkey : (S ⊓ N).relIndex N = S.relIndex (S ⊔ N) := by
    rw [h2a, h2a', ← hrel1] at hrel2
    have h3 : (S ⊓ N).relIndex N * (S ⊓ N).relIndex S = S.relIndex (S ⊔ N) * (S ⊓ N).relIndex S := by
      rw [hrel2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h3
  rw [hkey]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_left

theorem t2C_sylow_inf_odd {A S N : Subgroup G} (hNA : N ≤ A)
    (hnorm : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hSidx : ¬ 2 ∣ S.relIndex A) :
    ¬ 2 ∣ (S ⊓ N).relIndex N := by
  have hNn : (N.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : A) g.2 (n : G) hn⟩
  have h := t2C_relIndex_inf_dvd (S.subgroupOf A) (N.subgroupOf A)
  have e1 : ((S.subgroupOf A) ⊓ (N.subgroupOf A)).relIndex (N.subgroupOf A) =
      (S ⊓ N).relIndex N := by
    have e0 : (S.subgroupOf A ⊓ N.subgroupOf A) = (S ⊓ N).subgroupOf A := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [e0]
    exact Subgroup.relIndex_subgroupOf hNA
  rw [e1] at h
  intro h2
  exact hSidx (h2.trans h)

end SylowInf


end CFSG.GH74.GLS.Stage4.Rest
