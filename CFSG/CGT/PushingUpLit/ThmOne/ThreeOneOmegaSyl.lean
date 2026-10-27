module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneSym
public import CFSG.CGT.PushingUpLit.ThmOne.SubnormalConj

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ThreeOneOmega.inf_centralizer_oTwoIn_le {M : Subgroup G} (hM : IsCharacteristicP 2 ↥M) :
    M ⊓ Subgroup.centralizer (oTwoIn M : Set G) ≤ oTwoIn M := by
  rintro g ⟨hgM, hgC⟩
  have hg : (⟨g, hgM⟩ : ↥M) ∈ Subgroup.centralizer (pCore 2 ↥M : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : (h : G) ∈ oTwoIn M := by
      rw [oTwoIn_eq_map]
      exact ⟨h, hh, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC _ h1)
  rw [oTwoIn_eq_map]
  exact ⟨_, hM hg, rfl⟩

omit [Finite G] in
theorem ThreeOneOmega.mem_normalizer_inf_centralizer_self {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := by
  have key : ∀ a ∈ Subgroup.normalizer (R : Set G), ∀ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
      a * z * a⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
    rintro a ha z ⟨hzR, hzC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp ha z).mp hzR,
      Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : a⁻¹ * q * a ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem ha) q).mp hq
    have h1 := Subgroup.mem_centralizer_iff.mp hzC _ hq'
    calc q * (a * z * a⁻¹) = a * ((a⁻¹ * q * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * q * a)) * a⁻¹ := by rw [h1]
      _ = a * z * a⁻¹ * q := by group
  refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨key g hg z, fun hz => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hz

theorem isSubnormal_normalizer_of_oTwoIn_le {Y M R : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hMc : IsCharacteristicP 2 ↥M) (hY : IsShortGroup ↥Y) (hYM : Y ≤ M)
    (hsub : (Y.subgroupOf M).IsSubnormal) (hR : IsPGroup 2 R) (hQR : oTwoIn M ≤ R)
    (hRC : R ≤ centralizerModCore Y) :
    Y ≤ Subgroup.normalizer (R : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal := by
  have hOR : oTwoIn Y ≤ R :=
    (ThreeFromEight.oTwoIn_le_oTwoIn_of_isSubnormal hYM hsub).trans hQR
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_of_oTwoIn_le_of_le_centralizerModCore hOR hRC
  refine ⟨hYR, threeThree (U := blockU Y) (Z := R ⊓ Subgroup.centralizer (R : Set G)) hsub
    (normalizer_oTwoIn_eq_of_isMaximalTwoLocal hM) hYR ?_ ?_ hQR ?_ ?_⟩
  · exact le_inf ((blockU_le_oTwoIn Y).trans hOR)
      (Subgroup.le_centralizer_iff.mp (le_centralizer_blockU_of_le_centralizerModCore hY hR hRC))
  · rintro z ⟨-, hzC⟩
    have hzQ : z ∈ Subgroup.centralizer (oTwoIn M : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQR) hzC
    have hzM : z ∈ M := by
      rw [← normalizer_oTwoIn_eq_of_isMaximalTwoLocal hM]
      exact Subgroup.centralizer_le_normalizer _ hzQ
    exact ThreeOneOmega.inf_centralizer_oTwoIn_le hMc ⟨hzM, hzQ⟩
  · intro g hg z hz
    exact (Subgroup.mem_normalizer_iff.mp
      (ThreeOneOmega.mem_normalizer_inf_centralizer_self hg) z).mp hz
  · intro r hr x hx
    exact commutator_mem_blockU_of_mem_centralizerModCore hY.residual_eq (hRC hr) hx

theorem exists_isSylowOf_isSubnormal_normalizer_inf {Y M H : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hMc : IsCharacteristicP 2 ↥M) (hY : IsShortGroup ↥Y)
    (hYM : Y ≤ M) (hsub : (Y.subgroupOf M).IsSubnormal) (hQH : oTwoIn M ≤ H) :
    ∃ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y ⊓ H) ∧ oTwoIn M ≤ R ∧
      Y ≤ Subgroup.normalizer (R : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer (R : Set G) ⊓ H)).IsSubnormal := by
  obtain ⟨R, hR, hQR⟩ := Nine.exists_isSylowOf_ge (isPGroup_oTwoIn M)
    (le_inf (oTwoIn_le_centralizerModCore_of_isSubnormal hY.residual_eq hYM hsub) hQH)
  obtain ⟨hYR, hs⟩ := isSubnormal_normalizer_of_oTwoIn_le hM hMc hY hYM hsub hR.2.1 hQR
    (hR.1.trans inf_le_left)
  exact ⟨R, hR, hQR, hYR, CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_left hs⟩

theorem conjugate_le_sup_inf_centralizer_blockU {M X : Subgroup G} (hMc : IsCharacteristicP 2 ↥M)
    (hX : IsBlockOfInX M X) {m : G} (hm : m ∈ M) :
    conjugate X m ≤ X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) := by
  have hY : IsBlockOfInX M (conjugate X m) :=
    ⟨CFSG.GroupTheory.conjugate_le_of_mem hX.1 hm, isSubnormal_conjugate hX.2.1 hm,
      inClassX_conjugate hX.2.2 m⟩
  by_cases hYX : conjugate X m = X
  · rw [hYX]
    exact le_sup_left
  · have hc := distinct_blocks_commute_of_isBlockOfInX hMc hX hY (Ne.symm hYX)
    have h1 : conjugate X m ≤ Subgroup.centralizer (X : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hc
    exact le_sup_of_le_right (le_inf hY.1
      (h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (blockU_le X)))))

theorem exists_conjugate_le_not_isSubnormal {X M H : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hMc : IsCharacteristicP 2 ↥M) (hH : IsMaximalTwoLocal H) (hX : InClassX ↥X) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal)
    (hXH : X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) ≤ H) (hne : H ≠ M) :
    ∃ m ∈ M, conjugate X m ≤ H ∧ ¬ ((conjugate X m).subgroupOf H).IsSubnormal := by
  have hle : ∀ m ∈ M, conjugate X m ≤ H := fun m hm =>
    (conjugate_le_sup_inf_centralizer_blockU hMc ⟨hXM, hsub, hX⟩ hm).trans hXH
  obtain ⟨m, hm, hns⟩ := exists_conjugate_not_isSubnormal hM hH hX hXM hsub
    (le_sup_right.trans hXH) hne hle
  exact ⟨m, hm, hle m hm, hns⟩

end CFSG.CGT.PushingUpLit.ThmOne
