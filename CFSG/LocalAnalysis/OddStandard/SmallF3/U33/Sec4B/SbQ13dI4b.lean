module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dS

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_caseI_false (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    False := by
  obtain ⟨𝒮, h𝒮, hU𝒮, _hnormU𝒮, hcard𝒮⟩ := q13d_exists_cover h
  let R : Subgroup G := 𝒮 ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)
  have hRcard : Nat.card ↥R = 2 ^ 8 := by
    simpa only [R] using q13d_I_R2_card h hB h𝒮 hU𝒮 hcard𝒮
  have hcent_le : R ⊓ centralizer ({t * lam} : Set G) ≤
      q13E0 t tau x₁ x₂ rho om ⊓ centralizer ({t * lam} : Set G) := by
    intro r hr
    obtain ⟨hrR, hrf⟩ := Subgroup.mem_inf.mp hr
    obtain ⟨hrS, hrCN⟩ := Subgroup.mem_inf.mp hrR
    have hrU : r ∈ ctxU t tau x₁ x₂ lam := by
      have h1 : r ∈ 𝒮 ⊓ centralizer ({t * lam} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hrS, hrf⟩
      rw [hC.C_eq 𝒮 h𝒮 hU𝒮] at h1
      exact (Subgroup.mem_inf.mp h1).1
    have hrE0 : r ∈ q13E0 t tau x₁ x₂ rho om := by
      rw [← q13d_E0_eq h]
      exact Subgroup.mem_inf.mpr ⟨hrU, hrCN⟩
    exact Subgroup.mem_inf.mpr ⟨hrE0, hrf⟩
  have hCcard_le : Nat.card ↥(R ⊓ centralizer ({t * lam} : Set G)) ≤ 16 :=
    (Subgroup.card_le_of_le hcent_le).trans (q13d_I_card_E0_cent_f_le h hI hC.lam_om)
  have hprod : (conjIn R (t * lam)).ncard *
      Nat.card ↥(R ⊓ centralizer ({t * lam} : Set G)) = 2 ^ 8 := by
    rw [← card_eq_ncard_conjIn_mul R (t * lam), hRcard]
  have hCpos : 0 < Nat.card ↥(R ⊓ centralizer ({t * lam} : Set G)) :=
    Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have h16 : 16 ≤ (conjIn R (t * lam)).ncard := by
    apply le_of_mul_le_mul_right _ hCpos
    rw [hprod]
    calc 16 * Nat.card ↥(R ⊓ centralizer ({t * lam} : Set G)) ≤ 16 * 16 :=
          Nat.mul_le_mul_left 16 hCcard_le
      _ = 2 ^ 8 := by norm_num
  have hsubset : conjIn R (t * lam) ⊆
      {x : G | x ∈ (t * lam) • ((q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) :
        Subgroup G) : Set G) ∧ x * x = 1} := by
    rintro x ⟨r, hr, rfl⟩
    have hx2 : (r * (t * lam) * r⁻¹) * (r * (t * lam) * r⁻¹) = 1 := by
      have hf2 := q13c_tlam_sq h
      calc (r * (t * lam) * r⁻¹) * (r * (t * lam) * r⁻¹)
          = r * ((t * lam) * (t * lam)) * r⁻¹ := by group
        _ = r * 1 * r⁻¹ := by rw [hf2]
        _ = 1 := by group
    have he : (t * lam)⁻¹ * (r * (t * lam) * r⁻¹) ∈ q13E0 t tau x₁ x₂ rho om :=
      q13d_I_R2_comm h hB h𝒮 hU𝒮 hcard𝒮 r hr
    rcases (q13d_I_mem_E0 h hI).mp he with heP1 | ⟨p, hp, hep⟩
    · refine ⟨⟨(t * lam)⁻¹ * (r * (t * lam) * r⁻¹), heP1, ?_⟩, hx2⟩
      simp only [smul_eq_mul]
      group
    · exfalso
      have hxlam : r * (t * lam) * r⁻¹ = lam * p := by
        calc r * (t * lam) * r⁻¹
            = (t * lam) * ((t * lam)⁻¹ * (r * (t * lam) * r⁻¹)) := by group
          _ = (t * lam) * (t * p) := by rw [hep]
          _ = lam * p := by
                have hcomm := (q13a_t_comm h).1
                calc (t * lam) * (t * p) = ((t * lam) * t) * p := by group
                  _ = (t * (lam * t)) * p := by group
                  _ = (t * (t * lam)) * p := by rw [← hcomm]
                  _ = lam * p := by rw [← mul_assoc t t lam, q13a_t_mul_self h, one_mul]
      obtain ⟨g, hg⟩ := q13c_exists_conj h
      have hconj : (r * g) * t * (r * g)⁻¹ = lam * p := by
        calc (r * g) * t * (r * g)⁻¹ = r * (g * t * g⁻¹) * r⁻¹ := by group
          _ = r * (t * lam) * r⁻¹ := by rw [hg]
          _ = lam * p := hxlam
      have hxlamsq : (lam * p) * (lam * p) = 1 := by rw [← hxlam]; exact hx2
      exact (q13d_I_lamP1_not_tG h hI hC.lam_om p hp hxlamsq (r * g)) hconj
  have hle8 : (conjIn R (t * lam)).ncard ≤ 8 :=
    (Set.ncard_le_ncard hsubset).trans (q13d_I_card_invol_fP1_le h hI hC.lam_om)
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
