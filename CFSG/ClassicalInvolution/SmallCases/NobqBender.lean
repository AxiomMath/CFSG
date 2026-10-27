module

public import CFSG.Open.FusionDefs
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Nobq

theorem centralizer_le_of_fusionStronglyEmbedded {G : Type*} [Group G] {M : Subgroup G}
    (hM : CFSG.Open.fusionStronglyEmbedded M) {z : G} (hzM : z ∈ M) (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hodd := hM.2.2 g hgM
  have hin : z ∈ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    refine ⟨hzM, z, hzM, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [this]
      _ = z := by group
  have hdvd : 2 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have := orderOf_dvd_natCard (⟨z, hin⟩ : ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom))
    rwa [Subgroup.orderOf_mk, hz] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem mem_sylow_of_mem_normalizer_of_pow_four {G : Type*} [Group G] [Finite G] (Q : Sylow 2 G)
    {s : G} (hs : s ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (h4 : s ^ 4 = 1) :
    s ∈ (Q : Subgroup G) := by
  set M := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hMdef
  have hQM : (Q : Subgroup G) ≤ M := Subgroup.le_normalizer
  have : ((Q : Subgroup G).subgroupOf M).Normal := Subgroup.normal_in_normalizer
  have hodd : ¬ 2 ∣ ((Q : Subgroup G).subgroupOf M).index := by
    intro h
    refine Q.not_dvd_index (h.trans ?_)
    rw [← Subgroup.relIndex_mul_index hQM]
    exact Dvd.intro _ rfl
  set x : M := ⟨s, hs⟩ with hx
  have hx4 : (QuotientGroup.mk x : M ⧸ (Q : Subgroup G).subgroupOf M) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ 4 = 1 := Subtype.ext h4
    rw [this, QuotientGroup.mk_one]
  have h1 : orderOf (QuotientGroup.mk x : M ⧸ (Q : Subgroup G).subgroupOf M) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one hx4
  have h2 : orderOf (QuotientGroup.mk x : M ⧸ (Q : Subgroup G).subgroupOf M) ∣
      ((Q : Subgroup G).subgroupOf M).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 4 (((Q : Subgroup G).subgroupOf M).index) := by
    have : Nat.Coprime 2 (((Q : Subgroup G).subgroupOf M).index) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    simpa using this.pow_left 2
  have h3 : orderOf (QuotientGroup.mk x : M ⧸ (Q : Subgroup G).subgroupOf M) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.ClassicalInvolution.Nobq
