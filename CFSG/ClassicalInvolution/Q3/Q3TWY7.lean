module

public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups commutatorElement


section Pow

theorem pow3_subgroupOf {H : Type*} [Group H] {Y N : Subgroup H} (hN : N ≤ Y) (hp : Pow3 N) :
    Pow3 (N.subgroupOf Y) := by
  intro l hl
  have h1 : (l : H) ^ 3 ∈ ⁅N, N⁆ := hp l (Subgroup.mem_subgroupOf.mp hl)
  have e : ⁅N.subgroupOf Y, N.subgroupOf Y⁆.map Y.subtype = ⁅N, N⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hN]
  have hmem : Y.subtype (l ^ 3) ∈ ⁅N.subgroupOf Y, N.subgroupOf Y⁆.map Y.subtype := by
    rw [e, map_pow]
    exact h1
  obtain ⟨y, hy, hyl⟩ := hmem
  have : y = l ^ 3 := Y.subtype_injective hyl
  rwa [← this]

variable {G : Type} [Group G] [Finite G]

theorem pow3_of_member3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {L : Subgroup G} (hL : L ∈ Ω) : Pow3 L := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex L hL)
  exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp) e

theorem fixed_of_locAut_pow3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {t z : G}
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (ht : t * z * t⁻¹ = z)
    {N : Subgroup G} (hN : N ≤ locLayer Ω z) (hNp : Pow3 N)
    (h : ∀ a ∈ locImg Ω z N, locAut hΩ.conjInvariant ht a = a) :
    N ≤ Subgroup.centralizer ({t} : Set G) := by
  intro n hn
  set Y := locLayer Ω z
  set O := classicalInvolutionOddCore ↥Y
  have hOc : ∀ b ∈ N.subgroupOf Y, b⁻¹ * layerAut hΩ.conjInvariant ht b ∈ O := by
    intro b hb
    have := h _ ⟨b, hb, rfl⟩
    have h2 : locMk Ω z (layerAut hΩ.conjInvariant ht b) = locMk Ω z b := this
    exact QuotientGroup.eq.mp h2.symm
  have hcop : ∀ x ∈ O, ¬ 3 ∣ orderOf x := by
    intro x hx h3
    have h1 : orderOf (⟨x, hx⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hO3 (h3.trans h1)
  have key := fixed_of_pow3_of_central (layerAut hΩ.conjInvariant ht).toMonoidHom
    (N := N.subgroupOf Y) (pow3_subgroupOf hN hNp) hP1 hcop hOc
  have := key ⟨n, hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h4 := congrArg Subtype.val this
  have h5 : t * n * t⁻¹ = n := h4
  rw [mul_inv_eq_iff_eq_mul] at h5
  exact h5.symm

theorem commutes_of_commutes_locImg_pow3 {Ω : Set (Subgroup G)} {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {L B : Subgroup G}
    (hL : L ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) (hLp : Pow3 L)
    (h : Commutes (locImg Ω x L) (locImg Ω x B)) : Commutes L B := by
  set Y := locLayer Ω x
  set O := classicalInvolutionOddCore ↥Y
  have hker : (QuotientGroup.mk' O).ker ≤ Subgroup.center ↥Y := by
    rw [QuotientGroup.ker_mk']
    exact hP1
  have hcop : ∀ n ∈ (QuotientGroup.mk' O).ker, ¬ 3 ∣ orderOf n := by
    intro n hn h3
    rw [QuotientGroup.ker_mk'] at hn
    have h1 : orderOf (⟨n, hn⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hO3 (h3.trans h1)
  have key := commutes_of_map_commute_exponent3 (QuotientGroup.mk' O) hker hcop
    (A := B.subgroupOf Y) (L := L.subgroupOf Y) (pow3_subgroupOf hL hLp)
    (fun a ha l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a, ha, rfl⟩).symm)
  intro a ha b hb
  have := key ⟨b, hB hb⟩ (Subgroup.mem_subgroupOf.mpr hb) ⟨a, hL ha⟩
    (Subgroup.mem_subgroupOf.mpr ha)
  exact (congrArg Subtype.val this).symm

end Pow

end CFSG.ClassicalInvolution.Q3.Q3TWY
