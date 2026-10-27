module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem sec5ophyp_h_normal {G : Type} [Group G] (z : G) :
    ((zpowers z).subgroupOf (centralizer ({z} : Set G))).Normal := by
  have hzH : zpowers z ≤ centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine (Subgroup.normal_subgroupOf_iff hzH).mpr ?_
  intro a b ha hb
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hcomm : Commute b z := Subgroup.mem_centralizer_singleton_iff.mp hb
  have hcz : b * z ^ n = z ^ n * b := hcomm.zpow_right n
  have h1 : b * z ^ n * b⁻¹ = z ^ n := by
    rw [hcz, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, h1.symm⟩

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5op_exists_hyp_gen (h : Sec510Ctx G t L S z r ρ B A φ)
    (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b) :
    ∃ (X : Type) (_ : Group X) (π : ↥(centralizer ({z} : Set G)) →* X),
      Sec5OPHyp t z (sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))) π := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let N : Subgroup ↥H := (zpowers z).subgroupOf H
  haveI : N.Normal := sec5ophyp_h_normal z
  refine ⟨↥H ⧸ N, inferInstance, QuotientGroup.mk' N, ?_⟩
  exact
    { tH := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h.central t (sec5p510_t_mem_S h.toSec5Ctx)
      ht := h.involution
      hz := h.pocket.1
      surj := QuotientGroup.mk'_surjective N
      ker := QuotientGroup.ker_mk' N
      tT := Subgroup.subset_closure ⟨sec5p510_t_mem_conj t z,
        sec5p510_t_mem_R h.toSec5Ctx hs.pk.q⟩
      zT := by
        rcases hs.T_cases with hTE | hTR
        · rw [hTE]; exact sec5p510_z_mem_E h hs.ab
        · rw [hTR]; exact sec5p510_z_mem_R h.toSec5Ctx hs.pk.q
      TH := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h.central x (sec5p510_T_le_R t z _ hx).1
      TY := Subgroup.closure_mono fun _ hx => hx.1
      t_not_mem := by
        intro ht
        exact hs.pk.t_not_mem ((Subgroup.zpowers_le.mpr hs.pk.z_mem) ht)
      nconj := h.nconj }

end CFSG.OddStandard.SmallF3.Omega
