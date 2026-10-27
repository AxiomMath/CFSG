module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEImg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEQuat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEType
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZIff
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fx_qe_isI4PlusIn (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {Q₁ Q₂ : Subgroup G} {z : G}
    (hQ₁ : Q₁ ≤ L) (hQ₂ : Q₂ ≤ L) (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (hc : ⁅Q₁, Q₂⁆ = ⊥) (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂) (he₁ : e₁ ⟨z, hz₁⟩ = QuaternionGroup.a 2)
    (he₂ : e₂ ⟨z, hz₂⟩ = QuaternionGroup.a 2) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hzc : z ∉ centerIn L) : IsI4PlusIn L z := by
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  letI := i1
  letI := i2
  letI := i3
  have hoc : OddCentralCover φ := hφ.oddCentralCover hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  rw [fg_isI4PlusIn_iff_of_cover hoc (hQ₁ hz₁) hz2]
  rw [m6z_isI4PlusIn_omega_iff hQ (by rw [hφ.finrank_eq]; norm_num)
    (fun h => absurd h (by rw [hφ.finrank_eq]; norm_num)) (φ ⟨z, hQ₁ hz₁⟩)]
  have hww : (⟨z, hQ₁ hz₁⟩ : ↥L) * ⟨z, hQ₁ hz₁⟩ = 1 := Subtype.ext hzz
  have h1 : φ ⟨z, hQ₁ hz₁⟩ * φ ⟨z, hQ₁ hz₁⟩ = 1 := by
    rw [← map_mul, hww, map_one]
  obtain ⟨q, r, s, hqq, hrr, hss, hrq, hsq, hsr⟩ :=
    fx_qe_q8_images hQ₁ hQ₂ e₁ e₂ hc hz₁ hz₂ he₁ he₂ φ
  obtain ⟨hne1, hneπ⟩ := fx_qe_image_ne hφ hL (hQ₁ hz₁) hzz hz1 hzc
  refine ⟨?_, ?_⟩
  · exact congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h1
  · have hqq' : (q : OGroup Q) * (q : OGroup Q) = (φ ⟨z, hQ₁ hz₁⟩ : OGroup Q) :=
      congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hqq
    have hyy : ((q : OGroup Q) * (q : OGroup Q)) * ((q : OGroup Q) * (q : OGroup Q)) = 1 := by
      have h2 : ((q * q) * (q * q) : omegaGroup hQ) = 1 := by rw [hqq, h1]
      exact congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h2
    have hy1 : (q : OGroup Q) * (q : OGroup Q) ≠ 1 := by
      rw [hqq']; intro h; exact hne1 (Subtype.ext h)
    have hyπ : (q : OGroup Q) * (q : OGroup Q) ≠ piOrth Q := by
      rw [hqq']; exact hneπ
    have hrr' : (r : OGroup Q) * (r : OGroup Q) = (q : OGroup Q) * (q : OGroup Q) := by
      rw [hqq']
      exact congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hrr
    have hss' : (s : OGroup Q) * (s : OGroup Q) = (q : OGroup Q) * (q : OGroup Q) := by
      rw [hqq']
      exact congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hss
    have htype := fx_qe_invType_q8 (hQ := hQ) hφ.finrank_eq hφ.quadSign_eq
      (q := (q : OGroup Q)) (r := (r : OGroup Q)) (s := (s : OGroup Q))
      q.2 r.2 hyy hy1 hyπ hrr'
      (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hrq)
      hss'
      (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hsq)
      (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) hsr)
    rw [← hqq']; exact htype

end CFSG.OddStandard.SmallF3.Omega
