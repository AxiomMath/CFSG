module

public import CFSG.CGT.PushingUpLit.ThmOne.EndField
public import CFSG.CGT.PushingUpLit.ThmOne.SubnormalConj

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ThreeSix.isMaximalTwoLocal_of_threeOne {X M : Subgroup G}
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    IsMaximalTwoLocal M := by
  have h : M ∈ maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) := by
    rw [h31]
    exact Set.mem_singleton M
  exact h.1

omit [Finite G] in
theorem ThreeSix.mem_oTwoIn_of_mem_centralizer {M : Subgroup G} (hM : IsCharacteristicP 2 ↥M)
    {g : G} (hgM : g ∈ M) (hg : g ∈ Subgroup.centralizer (oTwoIn M : Set G)) :
    g ∈ oTwoIn M := by
  have h1 : (⟨g, hgM⟩ : ↥M) ∈ Subgroup.centralizer (pCore 2 ↥M : Set ↥M) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hg (q : G) ⟨q, hq, rfl⟩)
  exact ⟨⟨g, hgM⟩, hM h1, rfl⟩

omit [Finite G] in
theorem ThreeSix.conj_mem_inf_centralizer_self {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {z : G}
    (hz : z ∈ R ⊓ Subgroup.centralizer (R : Set G)) :
    g * z * g⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
  obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzR,
    Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have hr' : g⁻¹ * r * g ∈ R := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
  have h1 := Subgroup.mem_centralizer_iff.mp hzC _ hr'
  calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * r := by group

theorem normalizer_blockU_le_of_threeOne {X M : Subgroup G} (hX : IsShortGroup ↥X)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    Subgroup.normalizer (blockU X : Set G) ≤ M := by
  obtain ⟨H, hNH, hH⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (isPLocal_normalizer_of_isPGroup ((isPGroup_oTwoIn X).to_le (blockU_le_oTwoIn X))
      (blockU_ne_bot_of_short hX))
  have hXC : X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) ≤
      Subgroup.normalizer (blockU X : Set G) :=
    sup_le (le_normalizer_blockU X)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hmem : H ∈ maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) :=
    ⟨hH, fun g hg => hNH (hXC hg)⟩
  rw [h31, Set.mem_singleton_iff] at hmem
  exact hmem ▸ hNH

theorem normalizer_le_of_threeOne {X M : Subgroup G} (hX : IsShortGroup ↥X)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  refine le_trans (fun g hg => ?_) (normalizer_blockU_le_of_threeOne hX h31)
  refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => conj_mem_blockU hg hu, fun hu => ?_⟩
  simpa [mul_assoc] using conj_mem_blockU (inv_mem hg) hu

theorem centralizerModCore_le_of_threeOne {X M : Subgroup G} (hX : IsShortGroup ↥X)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    centralizerModCore X ≤ M :=
  (Glue.centralizerModCore_le_normalizer X).trans (normalizer_le_of_threeOne hX h31)

theorem centralizerModCore_inf_eq_of_threeOne {X M : Subgroup G} (hX : IsShortGroup ↥X)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    centralizerModCore X ⊓ M = centralizerModCore X :=
  inf_eq_left.mpr (centralizerModCore_le_of_threeOne hX h31)

theorem isSylowOf_centralizerModCore_inf_iff_of_threeOne {X M R : Subgroup G}
    (hX : IsShortGroup ↥X)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M}) :
    IsSylowOf 2 R (centralizerModCore X ⊓ M) ↔ IsSylowOf 2 R (centralizerModCore X) := by
  rw [centralizerModCore_inf_eq_of_threeOne hX h31]

theorem ThreeSix.center_le_oTwoIn_of_isSylowOf_inf {X M R : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) :
    R ⊓ Subgroup.centralizer (R : Set G) ≤ oTwoIn M := by
  have hQR := oTwoIn_le_of_isSylowOf_centralizerModCore_inf hX hXM hsub hR
  intro z hz
  obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
  exact ThreeSix.mem_oTwoIn_of_mem_centralizer hMc (Subgroup.mem_inf.mp (hR.1 hzR)).2
    (Subgroup.mem_centralizer_iff.mpr fun q hq => Subgroup.mem_centralizer_iff.mp hzC q (hQR hq))

theorem le_normalizer_of_isSylowOf_inf {X M R : Subgroup G} (hXM : X ≤ M)
    (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) : X ≤ Subgroup.normalizer (R : Set G) :=
  le_normalizer_of_oTwoIn_le_of_le_centralizerModCore
    (oTwoIn_self_le_of_isSylowOf_centralizerModCore_inf hXM hR) (hR.1.trans inf_le_left)

theorem isSubnormal_normalizer_of_isSylowOf_inf {X M R : Subgroup G} (hX : IsShortGroup ↥X)
    (hM : IsMaximalTwoLocal M) (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) :
    (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal :=
  threeThree hsub (normalizer_oTwoIn_eq_of_isMaximalTwoLocal hM)
    (le_normalizer_of_isSylowOf_inf hXM hR) (blockU_le_inf_centralizer_of_isSylowOf hX hXM hR)
    (ThreeSix.center_le_oTwoIn_of_isSylowOf_inf hX.residual_eq hMc hXM hsub hR)
    (oTwoIn_le_of_isSylowOf_centralizerModCore_inf hX.residual_eq hXM hsub hR)
    (fun _ hg _ hz => ThreeSix.conj_mem_inf_centralizer_self hg hz)
    (fun _ hr _ hx => commutator_mem_blockU_of_mem_centralizerModCore hX.residual_eq
      (Subgroup.mem_inf.mp (hR.1 hr)).1 hx)

theorem isSubnormal_normalizer_of_threeOne {X M R : Subgroup G} (hX : IsShortGroup ↥X)
    (hMc : IsCharacteristicP 2 ↥M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (h31 : maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M})
    (hR : IsSylowOf 2 R (centralizerModCore X)) :
    X ≤ Subgroup.normalizer (R : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal := by
  have hR' := (isSylowOf_centralizerModCore_inf_iff_of_threeOne hX h31).mpr hR
  exact ⟨le_normalizer_of_isSylowOf_inf hXM hR', isSubnormal_normalizer_of_isSylowOf_inf hX
    (ThreeSix.isMaximalTwoLocal_of_threeOne h31) hMc hXM hsub hR'⟩

end CFSG.CGT.PushingUpLit.ThmOne
