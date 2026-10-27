module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18AH1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Thm4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18A_Xi_class_eq (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {d w : G} (hw : w = lam * d)
    (hd : d ∈ closure ({t, om} : Set G)) (hd2 : d * d = 1) {ξ : G}
    (hξ : ξ ∈ ctxXi t tau x₁ x₂ rho) (hsq : (ξ * w) * (ξ * w) = 1) :
    ∃ η ∈ ctxXi t tau x₁ x₂ rho, ξ * w = η * w * η⁻¹ := by
  subst hw
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  obtain ⟨hlam2pow, hlam_comm⟩ := ctx13_lam_facts hc13
  have hlam2 : lam * lam = 1 := by rw [pow_two] at hlam2pow; exact hlam2pow
  have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hdl : d * lam = lam * d := hlam_comm d hd
  have hw2 : (lam * d) * (lam * d) = 1 := by
    calc (lam * d) * (lam * d) = lam * (d * lam) * d := by group
      _ = lam * (lam * d) * d := by rw [hdl]
      _ = (lam * lam) * (d * d) := by group
      _ = 1 := by rw [hlam2, hd2, one_mul]
  have hdρ : d * rho = rho * d :=
    Subgroup.mem_centralizer_singleton_iff.mp ((ctx13_T_facts hc13).1 hd)
  have hwρ : (lam * d) * rho * (lam * d)⁻¹ = rho⁻¹ := by
    have hdρ' : d * rho * d⁻¹ = rho := by rw [hdρ]; group
    calc (lam * d) * rho * (lam * d)⁻¹ = lam * (d * rho * d⁻¹) * lam⁻¹ := by group
      _ = lam * rho * lam⁻¹ := by rw [hdρ']
      _ = rho⁻¹ := hc.lam_rho
  have hQΞ : ctxQ t tau x₁ x₂ rho ≤ ctxXi t tau x₁ x₂ rho := l18_Q_le_Xi hc13
  have hQ3 : ¬ 3 ∣ Nat.card (ctxQ t tau x₁ x₂ rho) := by
    rw [IsZ4Z4E4.card hc.q_iso]; norm_num
  have hQn : ∀ x ∈ ctxXi t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      x * q * x⁻¹ ∈ ctxQ t tau x₁ x₂ rho := fun x hx q hq =>
    hc.normal_Q_K.2 x ((l18_Xi_normal hc13).1 hx) q hq
  have hρΞ : ∀ x ∈ ctxXi t tau x₁ x₂ rho, rho * x * rho⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
    fun x hx => (l18_Xi_normal hc13).2 rho (l17_mem_K hc13).2.2.2.2 x hx
  have hρQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun q hq => hc.normal_Q_K.2 rho (l17_mem_K hc13).2.2.2.2 q hq
  have hfix : ∀ x ∈ ctxXi t tau x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1 := by
    intro x hx hxfix
    have hxc : x ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * rho = (rho * x * rho⁻¹) * rho := by rw [hxfix]
        _ = rho * x := by group
    have hxbot : x ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hx, hxc⟩
    rw [k18_Xi_cap_cent_rho hc] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  exact k18A_cocycle_exact hρ3 hw2 hwρ hQΞ hQ3 hQn
    (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) (k18_Xi_quot_elem hc).1
    (k18_Xi_quot_elem hc).2 hρΞ hρQ hfix hξ hsq

end S4B

theorem lemma418CaseAH1_holds : Lemma418CaseAH1Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc ξ w hw hξ hsq
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  rcases hw with hw | hw | hw
  · exact S4B.k18A_Xi_class_eq hc.toCtx18 (d := 1) (by rw [hw, mul_one])
      (Subgroup.one_mem _) (mul_one 1) hξ hsq
  · obtain ⟨ht2, -, hom2, htau2, -, htτ, hom_t⟩ := S4B.ctx13_relations hc13
    have htau2' : tau * tau = 1 := by rw [pow_two] at htau2; exact htau2
    exact S4B.k18A_Xi_class_eq hc.toCtx18 hw (S4B.tau_mem_closure ht2 hom2 htau2 htτ hom_t)
      htau2' hξ hsq
  · have hom2 : om * om = 1 := by
      have h := hc13.om_sq
      rw [pow_two] at h; exact h
    exact S4B.k18A_Xi_class_eq hc.toCtx18 hw (Subgroup.subset_closure (by simp)) hom2 hξ hsq

theorem lemma418CaseAFuC_holds : Lemma418CaseAFuCStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc g ξ hξ hg
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have ht2 : t * t = 1 := by
    have h := (S4B.ctx13_relations hc13).1
    rw [pow_two] at h; exact h
  have hsq : (ξ * (lam * t)) * (ξ * (lam * t)) = 1 := by
    rw [← hg]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  exact S4B.k18A_Xi_class_eq hc.toCtx18 rfl (Subgroup.subset_closure (by simp)) ht2 hξ hsq


theorem harris1981_bound_reduced13F (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hK : Ctx13KStmt) (hI : Sec4Inputs)
    (hB : Sec4BInputs) : FritzII.Harris1981Bound :=
  harris1981_bound_reduced13E h41 h41c h411 h413 hK lemma418CaseAH1_holds
    lemma418CaseAFuC_holds hI hB

end CFSG.OddStandard.SmallF3.HarrisU33
