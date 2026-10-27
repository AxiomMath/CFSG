module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BNs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BPar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}

theorem fzl59b_of_linear [IsSimpleGroup G] (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hz : ¬ IsConj t ((x₁ * x₂) ^ 2))
    (hcent : 2 ^ 8 ≤ Nat.card ↥(T₃ ⊓ centralizer ({s} : Set G))) (hlin : Fz59Linear T₃) :
    False := by
  have hs : ¬ IsConj t s := fzl59b_not_conj_s h hcent
  have hnab : ∃ a b : G, a * b ≠ b * a := fzr_nonabelian_of_wreath h.ctx.wreath
  have htT : t ∈ T₃ := fzl59b_t_mem h
  have htt : t * t = 1 := fzl59b_t_mul_self h
  have ht1 : t ≠ 1 := fzl59b_t_ne_one h
  obtain ⟨M, hMT, hM, hMv⟩ := hlin (fun g => IsConj t g)
    (fun g _ a _ => fzl59b_isConj_conj g)
    (fun a _ c _ ha hc hac ha1 hc1 hne => fzl59b_parity h hz hs ha hc hac ha1 hc1 hne)
  have htM : t ∉ M := (hMv t htT htt ht1).mp (IsConj.refl t)
  have hM2 : M.relIndex T₃ = 2 := by
    rcases hM with hMeq | h2
    · exfalso
      apply htM
      rw [hMeq]
      exact htT
    · exact h2
  obtain ⟨m, hmM, x, hx⟩ := fzr_exists_conj_mem_maximal hnab h.sylow hMT hM2 htT htt
  have hm2 : m * m = 1 := by
    calc m * m = (x * t * x⁻¹) * (x * t * x⁻¹) := by rw [hx]
      _ = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hm1 : m ≠ 1 := by
    intro h1
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [hx, h1]; group
  exact ((hMv m (hMT hmM) hm2 hm1).mp (isConj_iff.mpr ⟨x, hx⟩)) hmM

theorem fzl59b_of_facts
    [IsSimpleGroup G]
    (h : Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃)
    (hcent : 2 ^ 8 ≤ Nat.card ↥(T₃ ⊓ centralizer ({s} : Set G))) (hlin : Fz59Linear T₃) :
    False :=
  fzl59b_of_linear h (fun hc => S4A.not_conj_z_of_ctx h.ctx (isConj_iff.mp hc)) hcent hlin

end CFSG.OddStandard.SmallF3.FritzII
