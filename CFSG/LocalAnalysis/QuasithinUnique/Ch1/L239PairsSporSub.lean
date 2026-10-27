
module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem commutator_zpowers_idem {G : Type*} [Group G] [Finite G] {Y : Subgroup G} [Y.Normal]
    (hY : IsPGroup 2 Y) {b : G} (hodd : Odd (orderOf b)) :
    ⁅⁅Y, Subgroup.zpowers b⁆, Subgroup.zpowers b⁆ = ⁅Y, Subgroup.zpowers b⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  refine CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime Y (Subgroup.zpowers b) ?_ ?_
  · rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => Subgroup.Normal.conj_mem inferInstance y hy g, fun hy => ?_⟩
    have := Subgroup.Normal.conj_mem inferInstance _ hy g⁻¹
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem commutator_le_of_isSubnormal {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : B.IsSubnormal) {Y : Subgroup G} [Y.Normal] (hY : IsPGroup 2 Y) {b : G} (hb : b ∈ B)
    (hodd : Odd (orderOf b)) : ⁅Y, Subgroup.zpowers b⁆ ≤ B := by
  induction hB with
  | top => exact le_top
  | step H K hHK hK hN ih =>
    have hC : ⁅Y, Subgroup.zpowers b⁆ ≤ K := ih (hHK hb)
    have hidem := commutator_zpowers_idem hY hodd
    rw [← hidem]
    rw [Subgroup.commutator_le]
    intro c hc p hp
    have hcK : c ∈ K := hC hc
    have hpH : p ∈ H := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
      exact H.zpow_mem hb n
    have hconj := (Subgroup.normal_subgroupOf_iff hHK).1 hN
    have h1 : c * p * c⁻¹ ∈ H := hconj p c hpH hcK
    have h2 : ⁅c, p⁆ = (c * p * c⁻¹) * p⁻¹ := by
      rw [commutatorElement_def]
    rw [h2]
    exact H.mul_mem h1 (H.inv_mem hpH)

end CFSG.QuasithinUnique.Vol2Native.L239
