module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPList

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)
open Certificates.T84P (IsInvE InvM)

theorem sec8t84FPrank_wit (F : Facts) (G : Certificates.T84P.Facts) :
    ∀ s : Sec8T84FPM0 F, orderOf s = 2 → ∃ A : Subgroup (Sec8T84FPM0 F),
      A ≤ centralizer ({s} : Set (Sec8T84FPM0 F)) ∧ CFSG.Open.IsElemAbelian 2 A ∧
        16 ≤ Nat.card A := by
  intro s hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs, pow_two] at h
  have hsInv : sec8t84FPRaw F s ∈ InvM :=
    List.mem_filter.mpr ⟨sec8t84FPRaw_mem F s, decide_eq_true
      ⟨fun h => hs1 ((sec8t84FPRaw_eq_oneE_iff F s).mp h), (sec8t84FPRaw_mul_self_iff F s).mpr hss⟩⟩
  have hlift : ∀ z ∈ InvM, ∃ x : Sec8T84FPM0 F, sec8t84FPRaw F x = z ∧ x * x = 1 := by
    intro z hz
    obtain ⟨hzM, hzI⟩ := List.mem_filter.mp hz
    have hzI' : IsInvE z := of_decide_eq_true hzI
    obtain ⟨x, rfl⟩ := sec8t84FPRaw_surj F hzM
    exact ⟨x, rfl, (sec8t84FPRaw_mul_self_iff F x).mp hzI'.2⟩
  obtain ⟨a, ha, hsa, b, hb, hsb, hab, c, hc, hsc, hac, hbc, hnd⟩ := G.rank _ hsInv
  obtain ⟨a₀, rfl, haa⟩ := hlift a ha
  obtain ⟨b₀, rfl, hbb⟩ := hlift b hb
  obtain ⟨c₀, rfl, hcc⟩ := hlift c hc
  rw [sec8t84FPRaw_commE_iff] at hsa hsb hab hsc hac hbc
  rw [← sec8t84FPRaw_prod4] at hnd
  exact sec8t84_elemAb_of_prod4 hss haa hbb hcc hsa hsb hsc hab hac hbc (List.Nodup.of_map _ hnd)

end CFSG.OddStandard.SmallF3.Omega
