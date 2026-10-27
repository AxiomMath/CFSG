module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OHeartAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OHeartFin
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5o_frame_data [Finite G] (f59 : Asc82Fact59) {t : G} {L : Subgroup G} {z r : G}
    {A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) :
    ∃ (g : G) (a b : Fin 6) (c : G), a ≠ b ∧ g⁻¹ * t * g = t * z ∧
      φ (Pi.single a 1) ∈ CFSG.conjugate L g ∧ c ∈ CFSG.conjugate L g ∧ c * t * c⁻¹ = t ∧
      ∀ i : Fin 6, c * φ (Pi.single i 1) * c⁻¹ = t * φ (Pi.single (Equiv.swap a b i) 1) := by
  obtain ⟨v, hv4, hvz⟩ := hm.z_mem
  obtain ⟨e, f, a, b, hef, hab, hae, haf, hbe, hbf, hv⟩ := sec5o_exists_efab hv4
  obtain ⟨m, _hmN, hmact⟩ := sec5o_acts_alt8 f59 hm ht (sec5o_gamma_mem_alt hef)
  obtain ⟨mτ, hmτ, hτact⟩ := sec5o_acts_extPerm hm (sec5o_tau_mem_alt hab hef)
  have hphi1 : φ (1 : Fin 6 → ZMod 2) = t := by
    change φ (fun _ => 1) = t
    exact hm.map_one
  have hact_c : sec5oActs φ (m⁻¹ * mτ * m) (sec5oSigma a b e f) := by
    unfold sec5oSigma
    exact sec5o_acts_mul (sec5o_acts_mul (sec5o_acts_inv hmact) hτact) hmact
  refine ⟨m, a, b, m⁻¹ * mτ * m, hab, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : m⁻¹ * t * m = φ (Pi.single e 1 + Pi.single f 1) := by
      have h := sec5o_acts_inv hmact (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)
        sec5o_isEvenVec_pair
      rw [sec5o_t_eq hm, inv_inv, sec5o_gamma_inv hef, sec5o_gamma_pair hef] at h
      exact h
    calc m⁻¹ * t * m = φ (Pi.single e 1 + Pi.single f 1) := h1
      _ = φ (1 + v) := by rw [hv]
      _ = φ (1 : Fin 6 → ZMod 2) * φ v := hm.perm.map_add 1 v
      _ = t * z := by rw [hphi1, hvz]
  ·
    rw [mem_conjugate_iff L m]
    rw [← sec5o_heartCoord_unit a]
    rw [hmact (Pi.single (sec5oPt a) 1 + Pi.single 6 1) (sec5o_isEvenVec_unit a)]
    exact (hm.mem_L _).mpr (sec5o_gamma_ra hef hae haf)
  ·
    rw [mem_conjugate_iff L m]
    have hc : m * (m⁻¹ * mτ * m) * m⁻¹ = mτ := by group
    rw [hc]
    exact hmτ.1
  ·
    have h := hact_c _ sec5o_isEvenVec_pair
    rw [sec5o_t_eq hm] at h
    rw [sec5o_sigma_t hab hef hae haf hbe hbf] at h
    rwa [sec5o_t_eq hm] at h
  ·
    intro i
    have h := hact_c _ (sec5o_isEvenVec_unit i)
    rw [sec5o_heartCoord_unit i] at h
    rw [sec5o_sigma_frame hab hef hae haf hbe hbf i] at h
    rw [hm.perm.map_add (1 : Fin 6 → ZMod 2) (Pi.single (Equiv.swap a b i) 1), hphi1] at h
    exact h

end CFSG.OddStandard.SmallF3.Omega
