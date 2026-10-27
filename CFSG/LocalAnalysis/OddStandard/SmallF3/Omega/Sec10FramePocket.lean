module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSyl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem isSubnormal_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {H : Subgroup A} {H' : Subgroup B} (h : ∀ a, a ∈ H ↔ e a ∈ H') :
    H.IsSubnormal ↔ H'.IsSubnormal := by
  constructor
  · intro hH
    have : H' = H.comap e.symm.toMonoidHom := by
      ext b
      simp [Subgroup.mem_comap, h]
    rw [this]
    exact hH.comap _
  · intro hH'
    have : H = H'.comap e.toMonoidHom := by
      ext a
      simp [Subgroup.mem_comap, h]
    rw [this]
    exact hH'.comap _

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L) {K C : Subgroup G}

theorem isSL23Mod_img_iff (hX : K ≤ L) : IsSL23Mod ↥(F.img K) ↔ IsSL23Mod ↥K :=
  ⟨isSL23Mod_of_mulEquiv (F.imgEquiv hX).symm, isSL23Mod_of_mulEquiv (F.imgEquiv hX)⟩

theorem isSubnormal_img_iff (hKC : K ≤ C) (hC : C ≤ L) :
    (K.subgroupOf C).IsSubnormal ↔ ((F.img K).subgroupOf (F.img C)).IsSubnormal := by
  refine isSubnormal_iff_of_mulEquiv (F.imgEquiv hC) fun a => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, imgEquiv_apply]
  exact (psi_mem_img (F := F) (l := ⟨(a : G), hC a.2⟩)).symm

theorem sl23PocketIn_img_iff {z : G} (hz : z ∈ L) (hK : K ≤ L) :
    Sl23PocketIn L z K ↔
      Sl23PocketIn QP45.originalSubgroup (F.ψ ⟨z, hz⟩) (F.img K) := by
  have hC : F.img (L ⊓ centralizer ({z} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({F.ψ ⟨z, hz⟩} : Set P45) :=
    F.img_inf_centralizer_singleton ⟨z, hz⟩
  have hCL : L ⊓ centralizer ({z} : Set G) ≤ L := inf_le_left
  unfold Sl23PocketIn
  rw [← hC, (psi_mem_img (F := F) (l := ⟨z, hz⟩)), img_le_img_iff hK hCL, F.isSL23Mod_img_iff hK]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (F.isSubnormal_img_iff h2 hCL).1 h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (F.isSubnormal_img_iff h2 hCL).2 h3, h4⟩

theorem le_of_sl23PocketIn {z : G} (h : Sl23PocketIn L z K) : K ≤ L :=
  h.2.1.trans inf_le_left

theorem isI4PlusIn_img_iff {z : G} (hz : z ∈ L) :
    IsI4PlusIn L z ↔ IsI4PlusIn QP45.originalSubgroup (F.ψ ⟨z, hz⟩) := by
  have hord : orderOf (F.ψ ⟨z, hz⟩) = orderOf z := F.orderOf_psi ⟨z, hz⟩
  unfold IsI4PlusIn
  rw [hord]
  constructor
  · rintro ⟨h2, K, hK⟩
    exact ⟨h2, F.img K, (F.sl23PocketIn_img_iff hz (le_of_sl23PocketIn hK)).1 hK⟩
  · rintro ⟨h2, K', hK'⟩
    have hK'P : K' ≤ QP45.originalSubgroup := hK'.2.1.trans inf_le_left
    refine ⟨h2, F.pre K', (F.sl23PocketIn_img_iff hz (pre_le K')).2 ?_⟩
    rwa [img_pre hK'P]

theorem mem_of_isI4PlusIn {z : G} (h : IsI4PlusIn L z) : z ∈ L := by
  obtain ⟨-, K, hK⟩ := h
  exact (le_of_sl23PocketIn hK) hK.1

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
