module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_perfect_lift_quotient_pCore {L T : Subgroup G}
    (Y : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hYperf : ⁅Y, Y⁆ = Y)
    (hYT : ∀ t ∈ T, ((Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype).map
        (MulAut.conj t).toMonoidHom =
      (Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype) :
    ∃ K : Subgroup G, K ≤ L ∧ ⁅K, K⁆ = K ∧ T ≤ normalizer (K : Set G) ∧
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∧
      (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Y := by
  classical
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set R0 : Subgroup ↥L := Y.comap π with hR0
  set R : Subgroup G := R0.map L.subtype with hR
  set K : Subgroup G := Hinf R with hK
  have hKR : K ≤ R := uc22p21c_Hinf_le R
  have hRL : R ≤ L := Subgroup.map_subtype_le R0
  have hKL : K ≤ L := hKR.trans hRL
  have hKeq : K = (Hinf R0).map L.subtype := by rw [hK, hR, Hinf_map]
  have hKsub : K.subgroupOf L = Hinf R0 := by
    rw [hKeq]
    show ((Hinf R0).map L.subtype).comap L.subtype = Hinf R0
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hYinf : Hinf Y = Y := le_antisymm (uc22p21c_Hinf_le Y) (uc22p21c_le_Hinf le_rfl hYperf)
  have hR0map : R0.map π = Y :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Y
  have himage : (K.subgroupOf L).map π = Y := by
    rw [hKsub, Hinf_map, hR0map, hYinf]
  refine ⟨K, hKL, uc22p21c_Hinf_perfect R, ?_, ?_, himage⟩
  · intro t ht
    have hmap : K.map (MulAut.conj t).toMonoidHom = K := by
      rw [hK, Hinf_map, hYT t ht]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : t * h * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
        ⟨h, hh, by simp [MulAut.conj_apply]⟩
      rwa [hmap] at this
    · intro hh
      rw [← hmap] at hh
      obtain ⟨k, hk, hkeq⟩ := hh
      have : k = h := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkeq
        exact mul_left_cancel (mul_right_cancel hkeq)
      rwa [← this]
  · let f : ↥K →* ↥Y :=
      (π.comp (Subgroup.inclusion hKL)).codRestrict Y (fun k => by
        have hk : (Subgroup.inclusion hKL k) ∈ K.subgroupOf L := by
          simp [Subgroup.mem_subgroupOf]
        have : π (Subgroup.inclusion hKL k) ∈ (K.subgroupOf L).map π := ⟨_, hk, rfl⟩
        rwa [himage] at this)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      rw [← himage] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨⟨(x : G), hx⟩, ?_⟩
      apply Subtype.ext
      rfl
    have hker : IsPGroup 2 ↥f.ker := by
      rintro ⟨k, hk⟩
      have hk1 : π (Subgroup.inclusion hKL k) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
        simpa [f] using this
      have hmem : Subgroup.inclusion hKL k ∈ CFSG.pCore 2 ↥L := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
      refine ⟨n, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hn
      simpa using this
    exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hf hker

end CFSG.GroupTheory

end
