module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLet
public import Certificates.Data.FzJtN

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus
  Certificates.FzJt

variable {G : Type} [Group G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
  {π : Model →* G}

theorem fzJt_pi_mem (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (g : Model) : π g ∈ T₂ :=
  hd.mem_T₂_iff.mpr ⟨g, rfl⟩

theorem fzJt_mem_calZ_iff (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (m : Model) :
    π m ∈ fzCalZ x₁ x₂ lam T₂ ↔ InZ m := by
  have hz1 := (hd.isInvM_iff z1M).mp (zList_invol z1M (by simp [zList]))
  have hz3 := (hd.isInvM_iff z3M).mp (zList_invol z3M (by simp [zList]))
  have hcomm : π z1M * π z3M = π z3M * π z1M := by
    rw [← map_mul, ← map_mul, z1M_z3M_comm]
  rw [hd.z1M_eq] at hz1 hcomm
  rw [hd.z3M_eq] at hz3 hcomm
  have hz1mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz3mem : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  constructor
  · rintro (⟨h1, hZ⟩ | ⟨h, hh, hm⟩)
    · rcases fzfus_mem_four hz1.1 hz3.1 hcomm hZ with h | h | h | h
      · exact absurd h h1
      · refine ⟨z1M, by simp [zList], (hd.eq_iff _ _).mp ?_⟩
        rw [h, hd.z1M_eq]
      · refine ⟨z3M, by simp [zList], (hd.eq_iff _ _).mp ?_⟩
        rw [h, hd.z3M_eq]
      · refine ⟨z2M, by simp [zList], ?_⟩
        refine KEq.trans ((hd.eq_iff _ _).mp ?_) z2M_keq_prod.symm
        rw [h, map_mul, hd.z1M_eq, hd.z3M_eq]
    · obtain ⟨g, rfl⟩ := hd.mem_T₂_iff.mp hh
      refine ⟨g * lamM * g⁻¹, lamConj_mem g, (hd.eq_iff _ _).mp ?_⟩
      rw [hm, map_mul, map_mul, map_inv, hd.lam_eq]
  · rintro ⟨z, hz, hmz⟩
    have hπ : π m = π z := (hd.eq_iff _ _).mpr hmz
    rw [hπ]
    simp only [zList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hz
    rcases hz with (rfl | rfl | rfl) | ⟨p, -, rfl⟩
    · exact Or.inl ⟨by rw [hd.z1M_eq]; exact hz1.2, by rw [hd.z1M_eq]; exact hz1mem⟩
    · have hz2 : π z2M = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
        rw [(hd.eq_iff _ _).mpr z2M_keq_prod, map_mul, hd.z1M_eq, hd.z3M_eq]
      refine Or.inl ⟨?_, by rw [hz2]; exact mul_mem hz1mem hz3mem⟩
      intro h2
      have hz2' := (hd.isInvM_iff z2M).mp (zList_invol z2M (by simp [zList]))
      exact hz2'.2 h2
    · exact Or.inl ⟨by rw [hd.z3M_eq]; exact hz3.2, by rw [hd.z3M_eq]; exact hz3mem⟩
    · refine Or.inr ⟨π (mkE p 1 1), fzJt_pi_mem hd _, ?_⟩
      rw [mkY_eq_conj, map_mul, map_mul, map_inv, hd.lam_eq]

end CFSG.OddStandard.SmallF3.FritzII
