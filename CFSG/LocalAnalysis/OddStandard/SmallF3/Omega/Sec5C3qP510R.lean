module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec510Q (G : Type) [Group G] (L : Subgroup G) (z : G) (Q₁ Q₂ : Subgroup G) : Prop where
  le₁ : Q₁ ≤ L
  le₂ : Q₂ ≤ L
  iso₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)
  iso₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2)
  comm : ⁅Q₁, Q₂⁆ = ⊥
  card : Nat.card ↥(Q₁ ⊔ Q₂) = 32
  center : centerIn (Q₁ ⊔ Q₂) = zpowers z
  not_central : z ∉ centerIn L

@[expose] def sec5p510_R (S Q₁ Q₂ : Subgroup G) : Subgroup G :=
  S ⊓ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G}

theorem sec5p510_t_mem_S (h : Sec5Ctx G t L S z) : t ∈ S :=
  sec4_t_mem_S h.sylow h.involution

theorem sec5p510_L_le_centralizer_t (h : Sec5Ctx G t L S z) :
    L ≤ centralizer ({t} : Set G) :=
  h.component.1

theorem sec5p510_t_mem_R (h : Sec5Ctx G t L S z) (hQ : Sec510Q G L z Q₁ Q₂) :
    t ∈ sec5p510_R S Q₁ Q₂ := by
  refine ⟨sec5p510_t_mem_S h, ?_⟩
  show t ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxL : x ∈ L := (sup_le hQ.le₁ hQ.le₂) hx
  have hxc : x ∈ centralizer ({t} : Set G) := sec5p510_L_le_centralizer_t h hxL
  rw [Subgroup.mem_centralizer_singleton_iff] at hxc
  exact hxc

theorem sec5p510_z_mem_R (h : Sec5Ctx G t L S z) (hQ : Sec510Q G L z Q₁ Q₂) :
    z ∈ sec5p510_R S Q₁ Q₂ := by
  refine ⟨h.mem_S, ?_⟩
  show z ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hz : z ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [hQ.center]
    exact Subgroup.mem_zpowers z
  exact ((sec5_mem_centerIn_iff.mp hz).2 x hx).symm

theorem sec5p510_R_le_normalizer (hy : Sec5B59Hyp) (h : Sec5Ctx G t L S z) :
    sec5p510_R S Q₁ Q₂ ≤ normalizer (L : Set G) := fun x hx =>
  sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB x (h.sylow.1 hx.1)

theorem sec5p510_t_mem_centralizer_L (h : Sec5Ctx G t L S z) : t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxc : x ∈ centralizer ({t} : Set G) := sec5p510_L_le_centralizer_t h hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hxc
  exact hxc

theorem sec5p510_R_inf_centralizer (h : Sec5Ctx G t L S z) (hQ : Sec510Q G L z Q₁ Q₂)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t) :
    sec5p510_R S Q₁ Q₂ ⊓ centralizer (L : Set G) = zpowers t := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ S ⊓ centralizer (L : Set G) := ⟨hx.1.1, hx.2⟩
    rwa [hCS] at hx'
  · exact le_inf (Subgroup.zpowers_le.mpr (sec5p510_t_mem_R h hQ))
      (Subgroup.zpowers_le.mpr (sec5p510_t_mem_centralizer_L h))

theorem sec5p510_R_index (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h : Sec5Ctx G t L S z)
    (hQ : Sec510Q G L z Q₁ Q₂) :
    (centralizer (L : Set G)).relIndex (sec5p510_R S Q₁ Q₂) ∣ 8 ∧
      ((centralizer (L : Set G)).relIndex (sec5p510_R S Q₁ Q₂) = 8 →
        ∃ a ∈ sec5p510_R S Q₁ Q₂, ∃ b ∈ sec5p510_R S Q₁ Q₂,
          a * b * a⁻¹ * b⁻¹ ∉ centralizer (L : Set G)) :=
  hD G L z h.toSec5Setting.isOm6Z2 h.pocket Q₁ Q₂ hQ.le₁ hQ.le₂ hQ.iso₁ hQ.iso₂ hQ.comm hQ.card
    hQ.center hQ.not_central (sec5p510_R S Q₁ Q₂) (sec5p510_R_le_normalizer hy h) inf_le_right

theorem sec5p510_R_card (h : Sec5Ctx G t L S z) (hQ : Sec510Q G L z Q₁ Q₂)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t) :
    Nat.card ↥(sec5p510_R S Q₁ Q₂) =
      (centralizer (L : Set G)).relIndex (sec5p510_R S Q₁ Q₂) * 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (L : Set G))
    (K := sec5p510_R S Q₁ Q₂)
  have h2 : centralizer (L : Set G) ⊓ sec5p510_R S Q₁ Q₂ = zpowers t := by
    rw [inf_comm]
    exact sec5p510_R_inf_centralizer h hQ hCS
  rw [h2, Nat.card_zpowers, h.involution] at h1
  exact h1.symm

theorem sec5p510_R_card_dvd (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h : Sec5Ctx G t L S z)
    (hQ : Sec510Q G L z Q₁ Q₂) (hCS : S ⊓ centralizer (L : Set G) = zpowers t) :
    Nat.card ↥(sec5p510_R S Q₁ Q₂) ∣ 16 := by
  rw [sec5p510_R_card h hQ hCS]
  have := (sec5p510_R_index hy hD h hQ).1
  exact (Nat.mul_dvd_mul_right this 2 : _ ∣ 8 * 2)

end CFSG.OddStandard.SmallF3.Omega
