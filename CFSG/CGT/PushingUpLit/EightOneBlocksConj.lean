module

public import CFSG.CGT.PushingUpLit.EightOneBlocksStruct

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

namespace EightOneBlocks

variable {G : Type} [Group G]

theorem le_iSup_conjugate {X L : Subgroup G} {l : G} (hl : l ∈ L) :
    conjugate X l ≤ ⨆ l ∈ L, conjugate X l :=
  le_iSup₂ (f := fun l _ => conjugate X l) l hl

theorem le_iSup_conjugate_self {X L : Subgroup G} : X ≤ ⨆ l ∈ L, conjugate X l := by
  have h := le_iSup_conjugate (X := X) (L := L) (one_mem L)
  rwa [ThreeFromEight.conjugate_one] at h

theorem iSup_conjugate_le {X L : Subgroup G} (hXL : X ≤ L) : (⨆ l ∈ L, conjugate X l) ≤ L :=
  iSup₂_le fun _ hl => CFSG.GroupTheory.conjugate_le_of_mem hXL hl

theorem conj_mem_iSup_conjugate {X L : Subgroup G} {g : G} (hg : g ∈ L) {m : G}
    (hm : m ∈ ⨆ l ∈ L, conjugate X l) : g * m * g⁻¹ ∈ ⨆ l ∈ L, conjugate X l := by
  have hle : (⨆ l ∈ L, conjugate X l) ≤
      (⨆ l ∈ L, conjugate X l).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun l hl x hx => ?_
    have hx' : l * x * l⁻¹ ∈ X := ThreeFromEight.mem_conjugate_iff.1 hx
    have hmem : g * x * g⁻¹ ∈ conjugate X (l * g⁻¹) := by
      rw [ThreeFromEight.mem_conjugate_iff]
      have e : l * g⁻¹ * (g * x * g⁻¹) * (l * g⁻¹)⁻¹ = l * x * l⁻¹ := by group
      rw [e]
      exact hx'
    exact le_iSup_conjugate (mul_mem hl (inv_mem hg)) hmem
  exact hle hm

theorem le_normalizer_iSup_conjugate (X L : Subgroup G) :
    L ≤ Subgroup.normalizer ((⨆ l ∈ L, conjugate X l : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => conj_mem_iSup_conjugate hg hm, fun hm => ?_⟩
  have := conj_mem_iSup_conjugate (inv_mem hg) hm
  simpa [mul_assoc] using this

end EightOneBlocks

open EightOneBlocks

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_eq {X L : Subgroup G} (hX : InClassX ↥X) (hL : InClassX ↥L) (hXL : X ≤ L)
    (hne : X ≠ L) (harrow : Arrow X L) : (⨆ l ∈ L, conjugate X l) = L :=
  eq_of_le_normalizer_of_not_le_oTwoIn hL.1 (arrow_top_simple hX hL hXL hne harrow).1
    (iSup_conjugate_le hXL) (le_normalizer_iSup_conjugate X L)
    (not_le_oTwoIn_of_inClassX hX le_iSup_conjugate_self)

theorem isSubnormal_of_conjClosure {X L K : Subgroup G} (hLK : L ≤ K)
    (hgen : (⨆ l ∈ L, conjugate X l) = L) (hXK : (X.subgroupOf K).IsSubnormal) :
    (L.subgroupOf K).IsSubnormal := by
  have hconj : ∀ l : ↥L, conjugate X (l : G) ≤ K := fun l =>
    ((le_iSup_conjugate l.2).trans hgen.le).trans hLK
  have hjoin := CFSG.GroupTheory.isSubnormal_iSup_of_pair
    (fun A B => CFSG.GroupTheory.isSubnormal_sup)
    (fun l : ↥L => (conjugate X (l : G)).subgroupOf K)
    fun l => isSubnormal_conjugate hXK (hLK l.2)
  have heq : (⨆ l : ↥L, (conjugate X (l : G)).subgroupOf K) = L.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le hLK]
    calc (⨆ l : ↥L, ((conjugate X (l : G)).subgroupOf K).map K.subtype)
        = ⨆ l : ↥L, conjugate X (l : G) :=
          iSup_congr fun l => Subgroup.map_subgroupOf_eq_of_le (hconj l)
      _ = ⨆ l ∈ L, conjugate X l := (iSup_subtype' (p := fun l => l ∈ L)
          (f := fun l _ => conjugate X l)).symm
      _ = L := hgen
  rwa [heq] at hjoin

end CFSG.CGT.PushingUpLit
