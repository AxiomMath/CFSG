module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5h1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_B (ha : Ctx4P t L S x₁ x₂ lam rho tau)
    (hQn : ¬ NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂)) :
    ∃ B : Subgroup G, fourGrp x₁ x₂ ≤ B ∧ B ≤ ctxQ t tau x₁ x₂ rho ∧ Nat.card B = 16 ∧
      (∀ b ∈ B, ∀ p ∈ ctxPL t tau x₁ x₂, b * p * b⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂) ∧
      (∀ b ∈ B, rho * b * rho⁻¹ ∈ B) ∧ (∀ b ∈ B, (lam * t) * b * (lam * t)⁻¹ ∈ B) := by
  have hl : Ctx4L t L S x₁ x₂ lam rho tau := ha.toCtx4L
  have hc : Ctx4Q t L S x₁ x₂ lam rho tau := hl.toCtx4Q
  obtain ⟨Z, hVZ, hZO, hZ16, hZP, hZL⟩ := exists_Z ha
  let B : Subgroup G := Z ⊓ ctxQ t tau x₁ x₂ rho
  have hVB : fourGrp x₁ x₂ ≤ B := le_inf hVZ hc.V_le_Q
  have hBQ : B ≤ ctxQ t tau x₁ x₂ rho := inf_le_right
  have hBP : ∀ b ∈ B, ∀ p ∈ ctxPL t tau x₁ x₂, b * p * b⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂ := by
    intro b hb p hp
    exact hZP b (Subgroup.mem_inf.mp hb).1 p hp
  have hρB : ∀ b ∈ B, rho * b * rho⁻¹ ∈ B := by
    intro b hb
    exact ⟨hZL rho (rho_mem_LO ha.toCtx4A) b (Subgroup.mem_inf.mp hb).1,
      rho_conj_Q hc b (Subgroup.mem_inf.mp hb).2⟩
  have hσB : ∀ b ∈ B, (lam * t) * b * (lam * t)⁻¹ ∈ B := by
    intro b hb
    exact ⟨hZL (lam * t) (lamt_mem_LO ha.toCtx4A) b (Subgroup.mem_inf.mp hb).1,
      sig_conj_Q ha b (Subgroup.mem_inf.mp hb).2⟩
  have hdec : ∀ z ∈ Z, ∃ q ∈ Z ⊓ ctxQ t tau x₁ x₂ rho,
      ∃ d ∈ Z ⊓ closure ({t, tau} : Set G), z = q * d := by
    intro z hz
    obtain ⟨b, hbQ, s, hsT, hzbs⟩ := O_decomp hc (hZO hz)
    have hsZ : s ∈ Z :=
      norm_trick_mem (ctxO t tau x₁ x₂) (ctxQ t tau x₁ x₂ rho)
        (closure ({t, tau} : Set G)) (fourGrp x₁ x₂) Z rho (rho_cubed hc)
        hc.Q_le_O (T_le_O hc) hc.V_le_Q hVZ
        (fun a ha' b hb' => O_comm_le hc ha' hb')
        (fun a ha' => O_sq_mem_V hc ha')
        (fun v hv a ha' => (V_comm_O hc ha' hv).symm)
        (rho_conj_Q hc) (rho_comm_T hc)
        (fun z hz => hZL rho (rho_mem_LO ha.toCtx4A) z hz)
        (fix_mod_V hc) hbQ hsT (by rw [← hzbs]; exact hz)
    have hbZ : b ∈ Z := by
      have hbz : b = z * s⁻¹ := by rw [hzbs]; group
      rw [hbz]
      exact Z.mul_mem hz (Z.inv_mem hsZ)
    exact ⟨b, ⟨hbZ, hbQ⟩, s, ⟨hsZ, hsT⟩, hzbs⟩
  have hB8 : 8 ≤ Nat.card B := by
    have h1 : Nat.card Z ≤ Nat.card B * Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) := by
      have hh := card_le_mul_of_decomp Z (ctxQ t tau x₁ x₂ rho)
        (closure ({t, tau} : Set G)) hdec
      simpa [B] using hh
    have h2 : Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ≤ 2 :=
      card_Z_inf_T_le ha Z hZP
    by_contra h
    have hlt : Nat.card B < 8 := Nat.not_le.mp h
    have hle7 : Nat.card B ≤ 7 := Nat.le_of_lt_succ hlt
    have h3 : Nat.card B * Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ≤ 7 * 2 :=
      Nat.mul_le_mul hle7 h2
    have h14 : Nat.card B * Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ≤ 14 := by
      calc Nat.card B * Nat.card ↥(Z ⊓ closure ({t, tau} : Set G)) ≤ 7 * 2 := h3
        _ = 14 := rfl
    exact absurd (le_trans hZ16 (le_trans h1 h14)) (by decide)
  have hdvd : Nat.card B ∣ 2 ^ 6 := by
    have h := Subgroup.card_dvd_of_le hBQ
    rwa [hc.card_Q] at h
  have hfixB : ∀ b ∈ B, rho * b = b * rho → b = 1 :=
    fun b hb hcomm => rho_fix_Q hc b (hBQ hb) hcomm
  have hcases := card_cases_of_conj_fpf B rho (rho_cubed hc) hρB hfixB hdvd
  have h16or64 : Nat.card B = 16 ∨ Nat.card B = 64 := by
    rcases hcases with h | h | h | h
    · exact absurd (h ▸ hB8) (by decide)
    · exact absurd (h ▸ hB8) (by decide)
    · exact Or.inl h
    · exact Or.inr h
  rcases h16or64 with h16 | h64
  · exact ⟨B, hVB, hBQ, h16, hBP, hρB, hσB⟩
  ·
    exfalso
    have hBQeq : B = ctxQ t tau x₁ x₂ rho := by
      apply Subgroup.eq_of_le_of_card_ge hBQ
      rw [hc.card_Q, h64]
      decide
    have hQZ : ctxQ t tau x₁ x₂ rho ≤ Z := by
      intro q hq
      have hqB : q ∈ B := by rw [hBQeq]; exact hq
      exact (Subgroup.mem_inf.mp hqB).1
    have hPnorm : ∀ p ∈ ctxPL t tau x₁ x₂, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
        p * q * p⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro p hp q hq
      have hv : q * p * q⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂ := hZP q (hQZ hq) p hp
      have hvinv : (q * p * q⁻¹ * p⁻¹)⁻¹ ∈ fourGrp x₁ x₂ := (fourGrp x₁ x₂).inv_mem hv
      have heq : p * q * p⁻¹ = (q * p * q⁻¹ * p⁻¹)⁻¹ * q := by group
      rw [heq]
      exact (ctxQ t tau x₁ x₂ rho).mul_mem (hc.V_le_Q hvinv) hq
    refine hQn ⟨hc.Q_le_O.trans (O_le_LO t tau x₁ x₂), ?_⟩
    intro g hg q hq
    rw [ha.L_eq] at hg
    exact normalizes_of_sup (ctxQ t tau x₁ x₂ rho) (ctxPL t tau x₁ x₂) rho (lam * t)
      hPnorm (rho_conj_Q hc) (sig_conj_Q ha) g hg q hq

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
