module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem fixSub_conj_le_centralizer {H : Type*} [Group H] (g : H) :
    Outside.fixSub (MulAut.conj g) ≤ Subgroup.centralizer ({g} : Set H) := by
  intro x hx
  rw [Outside.mem_fixSub, MulAut.conj_apply] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h : g * x = x * g := by
    have h' := congrArg (· * g) hx
    simpa [mul_assoc] using h'
  exact h

theorem k18_Xi_cap_cent_rho (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxXi, hxCent⟩ := Subgroup.mem_inf.mp hx
    have hxComm : x * rho = rho * x :=
      ((Subgroup.mem_centralizer_iff.mp hxCent) rho rfl).symm
    have hρ3 : rho ^ 3 = 1 := by
      rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
    have hQC : ctxQ t tau x₁ x₂ rho ≤ ctxXi t tau x₁ x₂ rho :=
      l18_Q_le_Xi hc.toCtx13
    have hQn : ∀ c ∈ ctxXi t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
        c * q * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro c hcC q hq
      exact hc.normal_Q_K.2 c ((l18_Xi_normal hc.toCtx13).1 hcC) q hq
    have hρQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro q hq
      exact hc.normal_Q_K.2 rho (l17_mem_K hc.toCtx13).2.2.2.2 q hq
    have hρC : ∀ c ∈ ctxXi t tau x₁ x₂ rho, rho * c * rho⁻¹ ∈ ctxXi t tau x₁ x₂ rho := by
      intro c hcC
      exact (l18_Xi_normal hc.toCtx13).2 rho (l17_mem_K hc.toCtx13).2.2.2.2 c hcC
    have hab : ∀ c ∈ ctxXi t tau x₁ x₂ rho, ∀ c' ∈ ctxXi t tau x₁ x₂ rho,
        c * c' * c⁻¹ * c'⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      (k18_Xi_quot_elem hc).1
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho :=
      comm_zpowers_inf_cent_le (C := ctxXi t tau x₁ x₂ rho)
        (Q := ctxQ t tau x₁ x₂ rho) (ρ := rho) hρ3
        (l18_Xi_pgroup hc.toCtx13) hQC hQn hρQ hρC hab x
        (by rw [k18_Xi_idem hc.toCtx13]; exact hxXi) hxComm
    exact Subgroup.mem_bot.mpr
      (l17_CP_rho hc.toCtx13 x (l17_Q_le_P hc.toCtx13 hxQ) hxComm)
  · exact bot_le

theorem k18_Xi_cap_tom (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ⊓ closure ({t, om} : Set G) = ⊥ := by
  have hle : closure ({t, om} : Set G) ≤ Subgroup.centralizer ({rho} : Set G) := by
    rw [← l18_OK_cap_cent_rho hc.toCtx13]
    exact inf_le_right
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← k18_Xi_cap_cent_rho hc]
    exact ⟨hx.1, hle hx.2⟩
  exact Subgroup.mem_bot.mp hxbot

theorem k18_card_Xi (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card (ctxXi t tau x₁ x₂ rho) = 2 ^ 8 := by
  have htomK : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({t, om} : Set G))
    rcases ha with rfl | rfl
    · exact (l17_mem_K hc.toCtx13).1
    · exact (l17_mem_K hc.toCtx13).2.2.1
  have hnorm : ∀ k ∈ closure ({t, om} : Set G), ∀ h ∈ ctxXi t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxXi t tau x₁ x₂ rho := fun k hk h hh =>
    (l18_Xi_normal hc.toCtx13).2 k (htomK hk) h hh
  have hcardtom : Nat.card ↥(closure ({t, om} : Set G)) = 8 :=
    (ctx13_T_facts hc.toCtx13).2.2
  have hcardmul := card_sup_eq_mul (H := ctxXi t tau x₁ x₂ rho)
    (K := closure ({t, om} : Set G)) hnorm (k18_Xi_cap_tom hc)
  rw [hcardtom, ← k18_OK_eq_Xi_tom hc.toCtx13, k18_card_OK hc.toCtx18S] at hcardmul
  have h2048 : Nat.card (ctxXi t tau x₁ x₂ rho) * 8 = 2048 := by
    rw [← hcardmul]; norm_num
  have h256 : Nat.card (ctxXi t tau x₁ x₂ rho) = 2 ^ 8 := by omega
  exact h256

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
