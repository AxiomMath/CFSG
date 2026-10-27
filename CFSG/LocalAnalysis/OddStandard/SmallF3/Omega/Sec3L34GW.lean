module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_w_exists [Finite G] (hP : L34GPocketComm G) {v x u : G} {D K : Subgroup G}
    (hdat : Sec3PocketData v D u K) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({u} : Set G))) (hIF : InFStar I) :
    ∃ w : G, w * w = x⁻¹ * u * x ∧ (∀ l ∈ CFSG.conjugate I x, w * l = l * w) ∧
      (∀ l ∈ CFSG.conjugate (CFSG.conjugate I v) x, w * l = l * w) := by
  have huv : u * v = v * u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hdat.component.1 hdat.mem)
  obtain ⟨f, -, hfu, hfK⟩ :=
    exists_quaternion_of_pocketData_q8 asc82NoQ8InL2_holds asc82OddCoreCentralizerQ8_holds hdat
  have hw0 : f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1) = u := by
    rw [← map_mul, QuaternionGroup.a_mul_a, show (1 : ZMod (2 * 2)) + 1 = 2 by decide, hfu]
  have hw0K : f (QuaternionGroup.a 1) ∈ K := by
    have h := hfK ⟨QuaternionGroup.a 1, rfl⟩
    rw [CFSG.inSubgroup] at h
    rcases Subgroup.mem_map.mp h with ⟨z, -, hz⟩
    rw [← hz]
    exact z.2
  have hKe : K ≤ Subgroup.centralizer (fstarLayer u : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hP v D u K hdat)
  have hKcomm : ∀ k ∈ K, ∀ e ∈ fstarLayer u, k * e = e * k := fun k hk e he =>
    (Subgroup.mem_centralizer_iff.mp (hKe hk) e he).symm
  have hv_mem : v ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huv.symm
  have hI_le : I ≤ fstarLayer u := le_fstarLayer hI hIF
  have hIv_le : CFSG.conjugate I v ≤ fstarLayer u :=
    le_fstarLayer (hI.conjugate hv_mem) (hIF.conjugate v)
  have key : ∀ (J : Subgroup G), J ≤ fstarLayer u →
      ∀ l ∈ CFSG.conjugate J x,
        (x⁻¹ * f (QuaternionGroup.a 1) * x) * l = l * (x⁻¹ * f (QuaternionGroup.a 1) * x) := by
    intro J hJ l hl
    have hl' : x * l * x⁻¹ ∈ fstarLayer u := hJ (sec63P_mem_conjugate_iff.mp hl)
    have hcomm : f (QuaternionGroup.a 1) * (x * l * x⁻¹) =
        (x * l * x⁻¹) * f (QuaternionGroup.a 1) := hKcomm _ hw0K _ hl'
    calc (x⁻¹ * f (QuaternionGroup.a 1) * x) * l
        = x⁻¹ * (f (QuaternionGroup.a 1) * (x * l * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * l * x⁻¹) * f (QuaternionGroup.a 1)) * x := by rw [hcomm]
      _ = l * (x⁻¹ * f (QuaternionGroup.a 1) * x) := by group
  refine ⟨x⁻¹ * f (QuaternionGroup.a 1) * x, ?_, key I hI_le, key (CFSG.conjugate I v) hIv_le⟩
  rw [show x⁻¹ * f (QuaternionGroup.a 1) * x * (x⁻¹ * f (QuaternionGroup.a 1) * x)
      = x⁻¹ * (f (QuaternionGroup.a 1) * f (QuaternionGroup.a 1)) * x by group, hw0]

end CFSG.OddStandard.SmallF3.Omega
