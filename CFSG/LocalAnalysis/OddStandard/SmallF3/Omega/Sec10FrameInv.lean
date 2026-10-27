module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10LayerS6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

theorem img_inf_centralizer_phi {s : G} (hs : s ∈ normalizer (L : Set G)) :
    F.img (L ⊓ centralizer ({s} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({F.φ ⟨s, hs⟩} : Set P45) := by
  ext p
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_img]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨F.ψ_mem l, ?_⟩
    have h := (Subgroup.mem_inf.1 hl).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact ((F.comm_phi_psi_iff ⟨s, hs⟩ l).2 h.symm).symm
  · rintro ⟨hp, hc⟩
    obtain ⟨l, rfl⟩ := F.ψ_surj hp
    refine ⟨l, Subgroup.mem_inf.2 ⟨l.2, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((F.comm_phi_psi_iff ⟨s, hs⟩ l).1 hc.symm).symm

theorem exists_equiv_perm_six {s : G} (hs : s ∈ normalizer (L : Set G))
    (hInv : InvCent 1440 (F.φ ⟨s, hs⟩)) :
    Nonempty (↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨g, hg, hgy⟩ := MoInv.exists_conj_r4 hInv
  have himg := (F.conj g hg).img_inf_centralizer_phi hs
  have hφ : (F.conj g hg).φ ⟨s, hs⟩ = Certificates.OmegaInv.r4 () := hgy
  rw [hφ] at himg
  obtain ⟨e6⟩ := MoInv.equiv_perm_six
  exact ⟨(((F.conj g hg).imgEquiv inf_le_left).trans (MulEquiv.subgroupCongr himg)).trans e6⟩

end PspFrame

theorem exists_equiv_perm_six_of_inducesTypeSome
    {G : Type} [Group G] {L : Subgroup G} (hL : IsPSp43 L)
    {s : G} (h : InducesTypeSome L s 5 1 4 (-1)) :
    Nonempty (↥(L ⊓ centralizer ({s} : Set G)) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨F⟩ := exists_pspFrame hL
  obtain ⟨hs, hInv⟩ := (TyDict.inducesTypeSome_four_minus_iff hL F s).1 h
  exact F.exists_equiv_perm_six hs hInv

theorem layerCent_ne_bot_of_inducesTypeSome
    {G : Type} [Group G] {L : Subgroup G} (hL : IsPSp43 L)
    {s : G} (h : InducesTypeSome L s 5 1 4 (-1)) : layerCent L s ≠ ⊥ := by
  obtain ⟨e⟩ := exists_equiv_perm_six_of_inducesTypeSome hL h
  exact LayerS6.layerCent_ne_bot_of_equiv e

end CFSG.OddStandard.SmallF3.Omega
