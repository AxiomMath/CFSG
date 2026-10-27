module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarKappaCrd
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarKappaModel
public import CFSG.LocalAnalysis.EvenBN.Tits.N.PZThmA
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Syl
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Star

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem starV_false_of_kappa (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) (hS : PZ.StarV d z₀) : False := by
  classical
  letI : CommGroup d.s56V :=
    { (inferInstance : Group d.s56V) with
      mul_comm := fun a c => Subtype.ext (hS.abelian _ a.2 _ c.2) }
  have hvD : ∀ k, 7 ≤ k → k ≤ 12 → Model.parrottV k ∈ titsD := fun k h7 h12 =>
    (Model.parrottV_mem_titsD_iff h12).2 (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)
  have hU8D : Model.parrottU 8 ≤ titsD := by
    rw [Model.parrottU, closure_le]
    rintro _ ⟨k, ⟨hk8, hk12⟩, rfl⟩
    exact hvD k (by omega) hk12
  have hvE : ∀ k, 8 ≤ k → k ≤ 12 → d.pv k ∈ d.E := fun k h8 h12 =>
    mem_liftSub.2 ⟨Model.parrottV k, by
      rw [Model.hatE_eq_parrottU_eight]
      exact subset_closure ⟨k, ⟨h8, h12⟩, rfl⟩, hvD k (by omega) h12, rfl⟩
  have hEV := hd.s56_E_le_V h49
  have hgD := kapG_mem_titsD
  have hgM : d.lift kapG ∈ d.M := by
    refine p09_sylT_le_M hd (p09_mem_sylT_iff.2 ⟨hd.L_le (d.lift_mem _), ?_⟩)
    rw [hd.ρ_lift hgD]
    exact kapG_mem_parrottU
  have hgV := hd.s56_M_le_normalizer_V h49 hgM
  have hfV := hd.s56_M_le_normalizer_V h49 hd.s56_pv7_mem_M
  have hff : d.pv 7 * d.pv 7 = 1 := s56_pv7_mul_self d
  have hgg : d.lift kapG * d.lift kapG = d.pv 7 * (d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12) := by
    have h8 := hvD 8 (by norm_num) (by norm_num)
    have h10 := hvD 10 (by norm_num) (by norm_num)
    have h11 := hvD 11 (by norm_num) (by norm_num)
    have h12 := hvD 12 (by norm_num) (by norm_num)
    rw [← d.lift_mul hgD hgD, kapG_mul_self,
      d.lift_mul (hvD 7 le_rfl (by norm_num)) (mul_mem (mul_mem (mul_mem h8 h10) h11) h12),
      d.lift_mul (mul_mem (mul_mem h8 h10) h11) h12, d.lift_mul (mul_mem h8 h10) h11,
      d.lift_mul h8 h10]
    rfl
  have he0V : d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12 ∈ d.s56V :=
    hEV (mul_mem (mul_mem (mul_mem (hvE 8 le_rfl (by norm_num)) (hvE 10 (by norm_num)
      (by norm_num))) (hvE 11 (by norm_num) (by norm_num))) (hvE 12 (by norm_num) le_rfl))
  have hconj : ∀ k, 7 ≤ k → k ≤ 12 → d.lift kapG * d.pv k * (d.lift kapG)⁻¹ =
      d.lift (kapG * Model.parrottV k * kapG⁻¹) := fun k h7 h12 =>
    (d.lift_conj hgD (hvD k h7 h12)).symm
  obtain ⟨k12, k11, k10, k9, k8⟩ := kapG_conj
  have hroot : ∀ i : Fin 5, ∃ v ∈ d.s56V, v * v = d.pv (12 - (i : ℕ)) := fun i => by
    obtain ⟨v, hv, hε⟩ := hd.s56_V_eps_surj h49 hz _ (hvE (12 - (i : ℕ)) (by omega) (by omega))
    exact ⟨v, hv, (hS.sq_eq_eps v hv).trans hε⟩
  choose bG hbV hbsq using hroot
  let b : Fin 5 → d.s56V := fun i => ⟨bG i, hbV i⟩
  have hb2 : ∀ i, ((b i ^ 2 : d.s56V) : G) = d.pv (12 - (i : ℕ)) := fun i => by
    rw [Subgroup.coe_pow, sq]
    exact hbsq i
  have hb4 : ∀ i, b i ^ 4 = 1 := fun i => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hS.exp_four _ (hbV i))
  have hP : ∀ v : d.s56V, (v : G) ∈ d.E → v ∈ closure (Set.range fun i => b i ^ 2) := by
    intro v hv
    apply mem_closure_of_coe_mem
    have himg : ((↑) : d.s56V → G) '' (Set.range fun i => b i ^ 2) =
        Set.range fun i : Fin 5 => d.pv (12 - (i : ℕ)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hb2)
    rw [himg]
    obtain ⟨x, hx, -, hxv⟩ := mem_liftSub.1 hv
    rw [← hxv]
    clear hxv
    rw [Model.hatE_eq_parrottU_eight, Model.parrottU] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, ⟨hk8, hk12⟩, rfl⟩ := hx
      refine subset_closure ⟨⟨12 - k, by omega⟩, ?_⟩
      show d.pv (12 - (12 - k)) = d.pv k
      rw [Nat.sub_sub_self hk12]
    | one => rw [d.lift_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      rw [d.lift_mul (hU8D hx) (hU8D hy)]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      rw [d.lift_inv (hU8D hx)]
      exact inv_mem ihx
  have hsurj : Function.Surjective (crd b) :=
    crd_surjective hb4 (P := fun v : d.s56V => (v : G) ∈ d.E)
      (fun v => by
        show ((v ^ 2 : d.s56V) : G) ∈ d.E
        rw [Subgroup.coe_pow, sq, hS.sq_eq_eps _ v.2]
        exact hd.s56_V_eps_mem_E v.2)
      (fun w hw => by
        have h1 : (w : G) * w = 1 := by
          rw [← sq, ← Subgroup.coe_pow, hw, Subgroup.coe_one]
        exact (hS.sq_eq_one_iff _ w.2).1 h1) hP
  have hbij := crd_bijective hS.card hsurj
  let σ := conjEnd d.s56V hgV
  let τ := conjEnd d.s56V hfV
  have hτ : ∀ x, τ x = σ (σ x) := fun x => Subtype.ext (by
    simp only [τ, σ, conjEnd_apply]
    have hc := hS.abelian _ he0V _ x.2
    calc d.pv 7 * x * (d.pv 7)⁻¹
        = d.pv 7 * ((d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12) * x *
            (d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12)⁻¹) * (d.pv 7)⁻¹ := by
          rw [hc, mul_inv_cancel_right]
      _ = (d.pv 7 * (d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12)) * x *
            (d.pv 7 * (d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12))⁻¹ := by group
      _ = (d.lift kapG * d.lift kapG) * x * (d.lift kapG * d.lift kapG)⁻¹ := by rw [hgg]
      _ = d.lift kapG * (d.lift kapG * x * (d.lift kapG)⁻¹) * (d.lift kapG)⁻¹ := by group)
  have hττ : ∀ x, τ (τ x) = x := fun x => Subtype.ext (by
    simp only [τ, conjEnd_apply]
    calc d.pv 7 * (d.pv 7 * x * (d.pv 7)⁻¹) * (d.pv 7)⁻¹
        = (d.pv 7 * d.pv 7) * x * (d.pv 7 * d.pv 7)⁻¹ := by group
      _ = x := by rw [hff]; group)
  have hσe : ∀ i, ((σ (b i ^ 2) : d.s56V) : G) =
      d.lift kapG * d.pv (12 - (i : ℕ)) * (d.lift kapG)⁻¹ := fun i => by
    simp only [σ, conjEnd_apply, hb2]
  have h8 := hvD 8 (by norm_num) (by norm_num)
  have h9 := hvD 9 (by norm_num) (by norm_num)
  have h10 := hvD 10 (by norm_num) (by norm_num)
  have h11 := hvD 11 (by norm_num) (by norm_num)
  have h12 := hvD 12 (by norm_num) (by norm_num)
  have hσ0 : σ (b 0 ^ 2) = b 0 ^ 2 := Subtype.ext (by
    rw [hσe, hb2]
    show d.lift kapG * d.pv 12 * (d.lift kapG)⁻¹ = d.pv 12
    rw [hconj 12 (by norm_num) le_rfl, k12]
    rfl)
  have hσ1 : σ (b 1 ^ 2) = b 1 ^ 2 := Subtype.ext (by
    rw [hσe, hb2]
    show d.lift kapG * d.pv 11 * (d.lift kapG)⁻¹ = d.pv 11
    rw [hconj 11 (by norm_num) (by norm_num), k11]
    rfl)
  have hσ2 : σ (b 2 ^ 2) = b 0 ^ 2 * b 2 ^ 2 := by
    rw [mul_comm]
    refine Subtype.ext ?_
    rw [hσe, Subgroup.coe_mul, hb2, hb2]
    show d.lift kapG * d.pv 10 * (d.lift kapG)⁻¹ = d.pv 10 * d.pv 12
    rw [hconj 10 (by norm_num) (by norm_num), k10, d.lift_mul h10 h12]
    rfl
  have hσ3 : σ (b 3 ^ 2) = b 0 ^ 2 * b 1 ^ 2 * b 3 ^ 2 := by
    rw [show b 0 ^ 2 * b 1 ^ 2 * b 3 ^ 2 = b 3 ^ 2 * b 1 ^ 2 * b 0 ^ 2 by
      rw [mul_comm (b 0 ^ 2), mul_comm _ (b 3 ^ 2), mul_assoc]]
    refine Subtype.ext ?_
    rw [hσe, Subgroup.coe_mul, Subgroup.coe_mul, hb2, hb2, hb2]
    show d.lift kapG * d.pv 9 * (d.lift kapG)⁻¹ = d.pv 9 * d.pv 11 * d.pv 12
    rw [hconj 9 (by norm_num) (by norm_num), k9, d.lift_mul (mul_mem h9 h11) h12,
      d.lift_mul h9 h11]
    rfl
  have hσ4 : σ (b 4 ^ 2) = b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 2 * b 4 ^ 2 := by
    rw [show b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 2 * b 4 ^ 2 = b 4 ^ 2 * b 2 ^ 2 * b 1 ^ 2 * b 0 ^ 2 by
      rw [mul_comm _ (b 4 ^ 2), mul_comm (b 0 ^ 2 * b 1 ^ 2), mul_comm (b 0 ^ 2), ← mul_assoc,
        ← mul_assoc]]
    refine Subtype.ext ?_
    rw [hσe, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hb2, hb2, hb2, hb2]
    show d.lift kapG * d.pv 8 * (d.lift kapG)⁻¹ = d.pv 8 * d.pv 10 * d.pv 11 * d.pv 12
    rw [hconj 8 (by norm_num) (by norm_num), k8, d.lift_mul (mul_mem (mul_mem h8 h10) h11) h12,
      d.lift_mul (mul_mem h8 h10) h11, d.lift_mul h8 h10]
    rfl
  have hU : ∀ i : Fin 5, d.pv (12 - (i : ℕ)) ∈ d.F →
      b i * (τ (b i))⁻¹ ∈ closure ({b 0 ^ 2, b 1 ^ 2} : Set d.s56V) := by
    intro i hiF
    apply mem_closure_of_coe_mem
    have himg : ((↑) : d.s56V → G) '' {b 0 ^ 2, b 1 ^ 2} = {d.pv 11, d.pv 12} := by
      rw [Set.image_insert_eq, Set.image_singleton, hb2, hb2, Set.pair_comm]
      rfl
    rw [himg, ← s56U11_def]
    have hx : (bG i : G) ∈ d.s56V ⊓ d.N :=
      ⟨hbV i, (hd.s56_mem_N_iff_eps h49 (hd.s56_Q_le_Q0 (hbV i).1)).2 (by
        rw [← hS.sq_eq_eps _ (hbV i), hbsq i]
        exact hiF)⟩
    have h := hκ _ hx _ hd.s56_pv7_mem_F
    have e : ((b i * (τ (b i))⁻¹ : d.s56V) : G) = bG i * d.pv 7 * (bG i)⁻¹ * (d.pv 7)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, τ, conjEnd_apply, b]
      group
    rw [e]
    exact h
  exact false_of_crd hb4 hbij σ τ hτ hττ hσ0 hσ1 hσ2 hσ3 hσ4 (hU 1 (s56_pv11_mem_F d))
    (hU 2 (s56_pv10_mem_F d))

theorem stepZ0Inv_of_kappa (hK : StepKappa) : StepZ0Inv := by
  intro G _ _ d h49 hd z₀ hz
  have hκ : d.S56Kappa := hK h49 hd
  rcases (PZ.stepA_holds h49 hd hz hκ : PZ.InvV d z₀ ∨ PZ.StarV d z₀) with hI | hS
  · exact hI.sq_z₀
  · exact (starV_false_of_kappa h49 hd hz hκ hS).elim

end CFSG.LocalAnalysis.EvenBN.Tits.N.Star
