module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AOuter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G}


private theorem baseGrp_isMulCommutative (h : Ctx t L S x₁ x₂ lam rho tau) :
    IsMulCommutative ↥(baseGrp x₁ x₂) := by
  have hpair : ({x₁, x₂} : Set G).Pairwise Commute := by
    intro a ha b hb hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hne
    · exact h.wreath.comm
    · exact h.wreath.comm.symm
    · exact absurd rfl hne
  rw [baseGrp]
  exact Subgroup.isMulCommutative_closure hpair

private theorem baseGrp_comm (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : a * b = b * a := by
  haveI := baseGrp_isMulCommutative h
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(baseGrp x₁ x₂))
    (⟨b, hb⟩ : ↥(baseGrp x₁ x₂)))

private theorem baseGrp_le_L (h : Ctx t L S x₁ x₂ lam rho tau) : baseGrp x₁ x₂ ≤ L := by
  refine le_trans ?_ (S4A.wreathGrp_le_L_ctx0 h.toCtx0)
  rw [baseGrp, wreathGrp, Subgroup.closure_le]
  intro g hg
  exact Subgroup.subset_closure (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl <;> simp)

private theorem tau_conj_eq_inv (h : Ctx t L S x₁ x₂ lam rho tau) {e : G}
    (he : e ∈ baseGrp x₁ x₂) : tau * e * tau⁻¹ = e⁻¹ := by
  have hcomm : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => baseGrp_comm h ha hb
  refine (Subgroup.closure_induction (k := ({x₁, x₂} : Set G))
    (p := fun e _ => e ∈ baseGrp x₁ x₂ ∧ tau * e * tau⁻¹ = e⁻¹) ?_ ?_ ?_ ?_ he).2
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨Subgroup.subset_closure (by simp), h.tau_x₁⟩
    · exact ⟨Subgroup.subset_closure (by simp), h.tau_x₂⟩
  · exact ⟨(baseGrp x₁ x₂).one_mem, by simp⟩
  · intro a b ha hb hpa hpb
    obtain ⟨haH, hA⟩ := hpa
    obtain ⟨hbH, hB⟩ := hpb
    refine ⟨(baseGrp x₁ x₂).mul_mem haH hbH, ?_⟩
    calc tau * (a * b) * tau⁻¹ = (tau * a * tau⁻¹) * (tau * b * tau⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hA, hB]
      _ = b⁻¹ * a⁻¹ := hcomm a⁻¹ ((baseGrp x₁ x₂).inv_mem haH)
          b⁻¹ ((baseGrp x₁ x₂).inv_mem hbH)
      _ = (a * b)⁻¹ := (mul_inv_rev a b).symm
  · intro a ha hpa
    obtain ⟨haH, hA⟩ := hpa
    refine ⟨(baseGrp x₁ x₂).inv_mem haH, ?_⟩
    calc tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [hA]

private theorem t_comm (h : Ctx t L S x₁ x₂ lam rho tau) :
    (∀ l ∈ L, t * l = l * t) ∧ t * tau = tau * t := by
  constructor
  · intro l hl
    exact (Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer l hl).symm
  · have hZ : t ∈ Subgroup.centralizer (S : Set G) :=
      (h.center_ge (Subgroup.subset_closure
        (by simp : t ∈ ({t, (x₁ * x₂) ^ 2} : Set G)))).2
    exact (Subgroup.mem_centralizer_iff.mp hZ tau h.tau_mem).symm

private theorem tau_mul_tau (h44 : tau ^ 2 = 1) : tau * tau = 1 := by
  simpa [pow_two] using h44

theorem fz59Fus_holds :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
      (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
      Nat.card (twoCore t) = 2 → tau ^ 2 = 1 → ∀ e ∈ baseGrp x₁ x₂,
        IsConj tau (e * tau) ∧ IsConj (t * tau) (e * (t * tau)) := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau hr4 hctx hK h44 e he
  have hτ2 : tau * tau = 1 := tau_mul_tau h44
  have hτH : tau ∈ invCent t := hctx.toCtx0.le_invCent hctx.tau_mem
  have heL : e ∈ L := baseGrp_le_L hctx he
  have heH : e ∈ invCent t := by
    rw [invCent, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hctx.hyp.mem_centralizer e heL
  have hsq : (e * tau) * (e * tau) = 1 := by
    have hinv : tau * e * tau⁻¹ = e⁻¹ := tau_conj_eq_inv hctx he
    have h1 : tau * e = e⁻¹ * tau := by
      calc tau * e = (tau * e * tau⁻¹) * tau := by group
        _ = e⁻¹ * tau := by rw [hinv]
    calc (e * tau) * (e * tau) = e * (tau * e) * tau := by group
      _ = e * (e⁻¹ * tau) * tau := by rw [h1]
      _ = tau * tau := by group
      _ = 1 := hτ2
  have heτH : e * tau ∈ invCent t := (invCent t).mul_mem heH hτH
  have hquot : (e * tau) * tau⁻¹ ∈ L := by
    have : (e * tau) * tau⁻¹ = e := by rw [mul_assoc, mul_inv_cancel tau, mul_one]
    rw [this]; exact heL
  obtain ⟨l, hlL, hconj⟩ := S4A.outer_coset_conj hctx.hyp hτH hτ2 hctx.tau_not_mem
    heτH hsq hquot
  constructor
  · exact isConj_iff.mpr ⟨l, hconj.symm⟩
  ·
    obtain ⟨htL, htτ⟩ := t_comm hctx
    refine isConj_iff.mpr ⟨l, ?_⟩
    have he_tr : e * (t * tau) = t * (e * tau) := by
      calc e * (t * tau) = e * t * tau := by group
        _ = t * e * tau := by rw [(htL e heL).symm]
        _ = t * (e * tau) := by group
    have ht_conj : t * (e * tau) = l * (t * tau) * l⁻¹ := by
      rw [hconj]
      calc t * (l * tau * l⁻¹) = (t * l) * tau * l⁻¹ := by group
        _ = (l * t) * tau * l⁻¹ := by rw [htL l hlL]
        _ = l * (t * tau) * l⁻¹ := by group
    exact (he_tr.trans ht_conj).symm

end CFSG.OddStandard.SmallF3.FritzII
