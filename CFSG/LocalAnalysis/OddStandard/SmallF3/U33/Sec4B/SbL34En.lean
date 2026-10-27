module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3Sig

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_u_cent' (hc : Ctx4L t L S x₁ x₂ lam rho tau) {n : G}
    (hnO : n ∈ normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G))
    (hnU : n * (t * lam) * n⁻¹ ∈ ctxU t tau x₁ x₂ lam) :
    ∃ u ∈ ctxU t tau x₁ x₂ lam, (u * n) * (t * lam) * (u * n)⁻¹ = t * lam := by
  set q' : G := n * (t * lam) * n⁻¹ with hq'_def
  have hq'U : q' ∈ ctxU t tau x₁ x₂ lam := by
    rw [hq'_def]
    exact hnU
  have hq'O : q' ∉ ctxO t tau x₁ x₂ := by
    intro h
    apply q_not_mem_O hc
    rw [hq'_def] at h
    exact (Subgroup.mem_normalizer_iff.mp hnO (t * lam)).mpr h
  set w : G := (t * lam)⁻¹ * q' with hw_def
  have hw : w ∈ ctxO t tau x₁ x₂ := by
    rw [hw_def]
    exact inv_mul_mem_O hc (q_mem_U hc) hq'U (q_not_mem_O hc) hq'O
  have hq'w : (t * lam) * w = q' := by
    rw [hw_def]; group
  have hq'2 : q' * q' = 1 := by
    rw [hq'_def]
    calc (n * (t * lam) * n⁻¹) * (n * (t * lam) * n⁻¹)
        = n * ((t * lam) * (t * lam)) * n⁻¹ := by group
      _ = 1 := by rw [q_mul_self hc.toCtx4Q]; group
  have hqw : (t * lam * w) * (t * lam * w) = 1 := by
    have h : t * lam * w = q' := hq'w
    rw [h]; exact hq'2
  obtain ⟨b, hb, hxX⟩ := claim1 hc hw hqw
  set x : G := (t * lam)⁻¹ * (b⁻¹ * (t * lam * w) * b) with hx_def
  have hbx : b⁻¹ * q' * b = (t * lam) * x := by
    rw [hx_def, hq'w]
    group
  have hinv : (t * lam * x) * (t * lam * x) = 1 := by
    rw [hbx.symm]
    calc (b⁻¹ * q' * b) * (b⁻¹ * q' * b) = b⁻¹ * (q' * q') * b := by group
      _ = 1 := by rw [hq'2]; group
  have hcl : ∃ g : G, g * t * g⁻¹ = t * lam * x := by
    obtain ⟨g₀, hg₀⟩ := hc.inv_tl 1 (one_mem _) (by simpa using q_mul_self hc.toCtx4Q)
    have hg₀' : g₀ * t * g₀⁻¹ = t * lam := by
      simpa using hg₀
    refine ⟨b⁻¹ * n * g₀, ?_⟩
    calc (b⁻¹ * n * g₀) * t * (b⁻¹ * n * g₀)⁻¹
        = b⁻¹ * (n * (g₀ * t * g₀⁻¹) * n⁻¹) * b := by group
      _ = b⁻¹ * (n * (t * lam) * n⁻¹) * b := by rw [hg₀']
      _ = b⁻¹ * q' * b := by rw [hq'_def]
      _ = (t * lam) * x := hbx
  rcases x_one_or_z hc hxX hinv hcl with hx1 | hxz
  · refine ⟨b⁻¹, O_le_U hc (inv_mem hb), ?_⟩
    calc (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹
        = b⁻¹ * q' * b := by rw [hq'_def]; group
      _ = (t * lam) * x := hbx
      _ = t * lam := by rw [hx1, mul_one]
  · refine ⟨(x₁ ^ 2)⁻¹ * b⁻¹, ?_, ?_⟩
    · exact mul_mem
        (inv_mem (O_le_U hc (hc.toCtx4Q.Q_le_O
          (hc.toCtx4Q.V_le_Q (subset_closure (by simp))))))
        (inv_mem (O_le_U hc hb))
    · have hgt : (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹ = (t * lam) * (x₁ * x₂) ^ 2 := by
        calc (b⁻¹ * n) * (t * lam) * (b⁻¹ * n)⁻¹
            = b⁻¹ * q' * b := by rw [hq'_def]; group
          _ = (t * lam) * x := hbx
          _ = (t * lam) * (x₁ * x₂) ^ 2 := by rw [hxz]
      have hcent := cent_of_conj_qz hc hgt
      rw [show (x₁ ^ 2)⁻¹ * (b⁻¹ * n) = ((x₁ ^ 2)⁻¹ * b⁻¹) * n from
        (mul_assoc (x₁ ^ 2)⁻¹ b⁻¹ n).symm] at hcent
      exact hcent

theorem exists_cent_of_comm_mem (ha : Ctx4A t L S x₁ x₂ lam rho tau) {W : Subgroup G} {v : G}
    (hv : Ctx4V t x₁ x₂ lam tau W v) {w : G} (hw : w ∈ W)
    (hcomm : (t * lam) * w * (t * lam)⁻¹ * w⁻¹ ∈ ctxO t tau x₁ x₂) :
    ∃ k ∈ ctxO t tau x₁ x₂, ∃ d ∈ centralizer ({t * lam} : Set G) ⊓ W, w = k * d := by
  have hc : Ctx4L t L S x₁ x₂ lam rho tau := ha.toCtx4L
  have hwN : w ∈ normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := hv.sylow.1 hw
  have hwU : w * (t * lam) * w⁻¹ ∈ ctxU t tau x₁ x₂ lam := by
    have hwq : w * (t * lam) * w⁻¹ =
        ((t * lam) * w * (t * lam)⁻¹ * w⁻¹)⁻¹ * (t * lam) := by group
    rw [hwq]
    exact mul_mem (O_le_U hc (inv_mem hcomm)) (q_mem_U hc)
  obtain ⟨u, hu, huq⟩ := exists_u_cent' hc hwN hwU
  have hdW : u * w ∈ W := mul_mem (hv.U_le hu) hw
  have hdC : u * w ∈ centralizer ({t * lam} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (u * w) * (t * lam)
        = ((u * w) * (t * lam) * (u * w)⁻¹) * (u * w) := by group
      _ = (t * lam) * (u * w) := by rw [huq]
  by_cases huO : u⁻¹ ∈ ctxO t tau x₁ x₂
  ·
    refine ⟨u⁻¹, huO, u * w, Subgroup.mem_inf.mpr ⟨hdC, hdW⟩, ?_⟩
    group
  ·
    have hk0 : (t * lam)⁻¹ * u⁻¹ ∈ ctxO t tau x₁ x₂ :=
      inv_mul_mem_O hc (q_mem_U hc) (inv_mem hu) (q_not_mem_O hc) huO
    have hkO : (t * lam) * ((t * lam)⁻¹ * u⁻¹) * (t * lam)⁻¹ ∈ ctxO t tau x₁ x₂ :=
      q_conj_O hc hk0
    have hd'W : (t * lam) * (u * w) ∈ W := mul_mem (hv.U_le (q_mem_U hc)) hdW
    have hd'C : (t * lam) * (u * w) ∈ centralizer ({t * lam} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hd := Subgroup.mem_centralizer_singleton_iff.mp hdC
      rw [mul_assoc (t * lam) (u * w) (t * lam), hd]
    refine ⟨(t * lam) * ((t * lam)⁻¹ * u⁻¹) * (t * lam)⁻¹,
      hkO, (t * lam) * (u * w), Subgroup.mem_inf.mpr ⟨hd'C, hd'W⟩, ?_⟩
    group

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
