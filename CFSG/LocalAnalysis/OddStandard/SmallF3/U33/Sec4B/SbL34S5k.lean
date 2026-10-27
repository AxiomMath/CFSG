module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5j
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem cent_decomp (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) :
    ∀ o ∈ ctxO t tau x₁ x₂, (∀ b ∈ B, o * b = b * o) → ∃ b ∈ B, o = b ∨ o = b * ω := by
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  have hcardV : Nat.card (fourGrp x₁ x₂) = 4 := card_fourGrp hc
  have hcentQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, (∀ b ∈ B, q * b = b * q) → q ∈ B := by
    intro q hq hqb
    have hZ : ∀ b ∈ B, (∀ q ∈ ctxQ t tau x₁ x₂ rho, q * b = b * q) →
        b ∈ fourGrp x₁ x₂ := by
      intro b hb hbq
      have hmem : b ∈ ctxQ t tau x₁ x₂ rho ⊓
          centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
        ⟨hB.le_Q hb, Subgroup.mem_centralizer_iff.mpr hbq⟩
      rwa [hl.Z_Q] at hmem
    exact cent_eq_of_fpf (ctxQ t tau x₁ x₂ rho) B (fourGrp x₁ x₂) rho
      (rho_cubed hc) hc.card_Q hB.le_Q hB.card hcardV hB.comm
      (rho_conj_Q hc) hB.rho_mem (rho_fix_Q hc) hZ q hq hqb
  intro o ho hoB
  obtain ⟨q, hq, d, hd, rfl⟩ := O_decomp hc ho
  let C : Subgroup G := ctxO t tau x₁ x₂ ⊓ centralizer (B : Set G)
  have hVC : fourGrp x₁ x₂ ≤ C := by
    intro v hv
    exact Subgroup.mem_inf.mpr ⟨V_le_O hc hv,
      Subgroup.mem_centralizer_iff.mpr
        (fun b hb => V_comm_O hc (hc.Q_le_O (hB.le_Q hb)) hv)⟩
  have hCρ : ∀ z ∈ C, rho * z * rho⁻¹ ∈ C := by
    intro z hz
    obtain ⟨hzO, hzcent⟩ := Subgroup.mem_inf.mp hz
    have hzB : ∀ b ∈ B, b * z = z * b := Subgroup.mem_centralizer_iff.mp hzcent
    refine Subgroup.mem_inf.mpr ⟨rho_conj_O hc z hzO, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun b hb => ?_)
    have hb' : rho⁻¹ * b * rho ∈ B := by
      have h1 : rho * b * rho⁻¹ ∈ B := hB.rho_mem b hb
      have h2 : rho * (rho * b * rho⁻¹) * rho⁻¹ ∈ B := hB.rho_mem _ h1
      have hρ2 : rho * rho = rho⁻¹ :=
        (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact rho_cubed hc)).symm
      have hρinv2 : rho⁻¹ * rho⁻¹ = rho := by rw [← mul_inv_rev, hρ2, inv_inv]
      have key : rho * (rho * b * rho⁻¹) * rho⁻¹ = rho⁻¹ * b * rho := by
        rw [show rho * (rho * b * rho⁻¹) * rho⁻¹
              = (rho * rho) * b * (rho⁻¹ * rho⁻¹) by group, hρ2, hρinv2]
      rwa [key] at h2
    have hcomm' : z * (rho⁻¹ * b * rho) = (rho⁻¹ * b * rho) * z := (hzB _ hb').symm
    calc b * (rho * z * rho⁻¹)
        = rho * ((rho⁻¹ * b * rho) * z) * rho⁻¹ := by group
      _ = rho * (z * (rho⁻¹ * b * rho)) * rho⁻¹ := by rw [hcomm']
      _ = (rho * z * rho⁻¹) * b := by group
  have hoC : q * d ∈ C :=
    Subgroup.mem_inf.mpr ⟨ho,
      Subgroup.mem_centralizer_iff.mpr (fun b hb => (hoB b hb).symm)⟩
  have hdC : d ∈ C :=
    norm_trick_mem (ctxO t tau x₁ x₂) (ctxQ t tau x₁ x₂ rho)
      (closure ({t, tau} : Set G)) (fourGrp x₁ x₂) C rho
      (rho_cubed hc) hc.Q_le_O (T_le_O hc) hc.V_le_Q hVC
      (fun a ha' b hb' => O_comm_le hc ha' hb')
      (fun a ha' => O_sq_mem_V hc ha')
      (fun v hv a ha' => (V_comm_O hc ha' hv).symm)
      (rho_conj_Q hc) (rho_comm_T hc) hCρ (fix_mod_V hc) hq hd hoC
  have hdcent : d ∈ centralizer (B : Set G) := (Subgroup.mem_inf.mp hdC).2
  have hdc : ∀ b ∈ B, d * b = b * d :=
    fun b hb => (Subgroup.mem_centralizer_iff.mp hdcent b hb).symm
  rcases T_cent_cases ha hB hd hdc with hd1 | hdω
  ·
    refine ⟨q, ?_, Or.inl ?_⟩
    · apply hcentQ q hq
      intro b hb
      have hqd_comm : b * (q * d) = (q * d) * b :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hoC).2 b hb
      have hd_inv_comm : d⁻¹ * b = b * d⁻¹ := by
        have h : d * b = b * d := hdc b hb
        calc d⁻¹ * b = d⁻¹ * (b * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * b) * d⁻¹ := by rw [h]
          _ = b * d⁻¹ := by group
      calc q * b = (q * d) * d⁻¹ * b := by group
        _ = (q * d) * (d⁻¹ * b) := by group
        _ = (q * d) * (b * d⁻¹) := by rw [hd_inv_comm]
        _ = ((q * d) * b) * d⁻¹ := by group
        _ = (b * (q * d)) * d⁻¹ := by rw [hqd_comm]
        _ = b * ((q * d) * d⁻¹) := by group
        _ = b * q := by group
    · rw [hd1, mul_one]
  ·
    refine ⟨q, ?_, Or.inr ?_⟩
    · apply hcentQ q hq
      intro b hb
      have hqd_comm : b * (q * d) = (q * d) * b :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hoC).2 b hb
      have hd_inv_comm : d⁻¹ * b = b * d⁻¹ := by
        have h : d * b = b * d := hdc b hb
        calc d⁻¹ * b = d⁻¹ * (b * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * b) * d⁻¹ := by rw [h]
          _ = b * d⁻¹ := by group
      calc q * b = (q * d) * d⁻¹ * b := by group
        _ = (q * d) * (d⁻¹ * b) := by group
        _ = (q * d) * (b * d⁻¹) := by rw [hd_inv_comm]
        _ = ((q * d) * b) * d⁻¹ := by group
        _ = (b * (q * d)) * d⁻¹ := by rw [hqd_comm]
        _ = b * ((q * d) * d⁻¹) := by group
        _ = b * q := by group
    · rw [hdω]

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
