module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem pow_two_pow_mem_of_sup_eq' {Y J T : Subgroup G}
    (hJn : Y ≤ normalizer (J : Set G)) (hTY : T ≤ Y) (hT2 : IsPGroup 2 T)
    (hsup : J ⊔ T = Y) : ∀ g ∈ Y, ∃ n : ℕ, g ^ 2 ^ n ∈ J := by
  intro g hg
  have hTn : T ≤ normalizer (J : Set G) := hTY.trans hJn
  have hg' : g ∈ J ⊔ T := by rw [hsup]; exact hg
  obtain ⟨j, hj, t, ht, rfl⟩ := CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul hTn hg'
  obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
  refine ⟨n, ?_⟩
  have ht1 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hpow : ∀ m : ℕ, ∃ j' ∈ J, (j * t) ^ m = j' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, J.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨j', hj', e⟩ := ih
      refine ⟨j' * (t ^ m * j * (t ^ m)⁻¹), J.mul_mem hj' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTn (T.pow_mem ht m)) j).mp hj
      · rw [pow_succ, e]
        group
  obtain ⟨j', hj', e⟩ := hpow (2 ^ n)
  rw [e, ht1, mul_one]
  exact hj'

theorem mem_of_odd_of_sup_eq {Y J T : Subgroup G}
    (hJn : Y ≤ normalizer (J : Set G)) (hTY : T ≤ Y) (hT2 : IsPGroup 2 T)
    (hsup : J ⊔ T = Y) {g : G} (hg : g ∈ Y) (hodd : Odd (orderOf g)) : g ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := pow_two_pow_mem_of_sup_eq' hJn hTY hT2 hsup g hg
  exact mem_of_not_dvd_orderOf_of_pow_mem
    (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)) hn

theorem centralizes_of_odd_trivial_factors [Finite G] {Q U : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hUQ : U ≤ Q) (hUn : Q ≤ normalizer (U : Set G)) {c : G}
    (hcQ : c ∈ normalizer (Q : Set G)) (hodd : Odd (orderOf c))
    (hcU : ∀ u ∈ U, c * u = u * c) (hdisp : ∀ x ∈ Q, x⁻¹ * (c * x * c⁻¹) ∈ U) :
    ∀ x ∈ Q, c * x = x * c := by
  classical
  let g0 : ↥(normalizer (Q : Set G)) := ⟨c, hcQ⟩
  let φ : MulAut ↥Q := Q.normalizerMonoidHom g0
  have hφ : ∀ x : ↥Q, ((φ x : ↥Q) : G) = c * x * c⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q g0 x
  have hN : (U.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUQ).2 hUn
  have hm : 1 ≤ orderOf c := orderOf_pos c
  have hφm : φ ^ orderOf c = 1 := by
    rw [← map_pow]
    have : g0 ^ orderOf c = 1 := by
      apply Subtype.ext
      simp [g0, pow_orderOf_eq_one]
    rw [this, map_one]
  have hNp : IsPGroup 2 ↥(U.subgroupOf Q) := hQ2.to_subgroup _
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hcop : (orderOf c).Coprime (Nat.card ↥(U.subgroupOf Q)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  have hid := CFSG.SectionRank.Ccomm.coprime_automorphism_trivial_normal_factors
    (U.subgroupOf Q) φ hm hφm hcop
    (fun n hn => by
      apply Subtype.ext
      rw [hφ]
      have := hcU (n : G) (Subgroup.mem_subgroupOf.mp hn)
      rw [this]
      group)
    (fun h => by
      rw [Subgroup.mem_subgroupOf]
      have := hdisp (h : G) h.2
      rw [Subgroup.coe_mul, hφ, Subgroup.coe_inv]
      exact this)
  intro x hx
  have h1 : ((φ ⟨x, hx⟩ : ↥Q) : G) = x := by
    rw [hid]; rfl
  rw [hφ] at h1
  calc c * x = c * x * c⁻¹ * c := by group
    _ = x * c := by rw [h1]

end Generic

end CFSG.QuasithinUnique.Setup.Wreath
