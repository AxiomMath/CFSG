module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem CY_t (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
  apply le_antisymm
  · intro a ha
    have haY : a ∈ ctxYq t tau x₁ x₂ rho := ha.1
    have haQ : a ∈ ctxQ t tau x₁ x₂ rho := hz.Y_le_Q haY
    have hcomm : t * a = a * t := mem_centralizer_iff.mp ha.2 t rfl
    have hbase : a ∈ baseGrp x₁ x₂ := by
      have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        ⟨haQ, mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact hcomm⟩
      rwa [hz.CQ_t] at hmem
    have ha2 : a ^ 2 = 1 := (hz.mem_Y_iff a).mp haY |>.2
    have hcl : a ∈ closure {b : G | b ∈ baseGrp x₁ x₂ ∧ b ^ 2 = 1} :=
      subset_closure ⟨hbase, ha2⟩
    rwa [← (hz.wreath.fourGrp_eq_omega).1] at hcl
  · intro v hv
    have ht : t ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      have h := hz.t_mem_O
      rw [hz.O_eq_CV] at h
      exact h.2
    exact ⟨hz.V_le_Y hv, mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact (mem_centralizer_iff.mp ht v hv).symm⟩

theorem comm_Y_t_mem (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, t * a * t⁻¹ * a⁻¹ ∈ fourGrp x₁ x₂ := by
  intro a ha
  have haO : a ∈ ctxO t tau x₁ x₂ := hz.Q_le_O (hz.Y_le_Q ha)
  have haR : a ∈ ctxR t tau x₁ x₂ := by rwa [hz.O_eq_R] at haO
  have hx : t ∈ ctxX t tau x₁ x₂ := subset_closure (by simp)
  have h := haR.2.1 t hx
  have : (a * t * a⁻¹ * t⁻¹)⁻¹ = t * a * t⁻¹ * a⁻¹ := by group
  rw [← this]
  exact inv_mem h

private theorem comm_Y_t_mul (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxYq t tau x₁ x₂ rho) (hb : b ∈ ctxYq t tau x₁ x₂ rho) :
    t * (a * b) * t⁻¹ * (a * b)⁻¹ =
      (t * a * t⁻¹ * a⁻¹) * (t * b * t⁻¹ * b⁻¹) := by
  haveI : IsMulCommutative (ctxYq t tau x₁ x₂ rho) :=
    IsMulCommutative.of_comm fun x y =>
      Subtype.ext (hz.Q_comm x.1 (hz.Y_le_Q x.2) y.1 (hz.Y_le_Q y.2))
  have hb' : t * b * t⁻¹ * b⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    hz.V_le_Y (hz.comm_Y_t_mem b hb)
  have hcomm : a * (t * b * t⁻¹ * b⁻¹) = (t * b * t⁻¹ * b⁻¹) * a :=
    setLike_mul_comm ha hb'
  calc t * (a * b) * t⁻¹ * (a * b)⁻¹
      = (t * a * t⁻¹) * (t * b * t⁻¹) * (b⁻¹ * a⁻¹) := by group
    _ = (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹)) * (b * b⁻¹) * a⁻¹ := by group
    _ = (t * a * t⁻¹ * a⁻¹) * ((t * b * t⁻¹ * b⁻¹) * a) * (b * b⁻¹) * a⁻¹ := by rw [hcomm]
    _ = (t * a * t⁻¹ * a⁻¹) * (t * b * t⁻¹ * b⁻¹) := by group

private theorem comm_Y_t_inv (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ ctxYq t tau x₁ x₂ rho) :
    t * a⁻¹ * t⁻¹ * (a⁻¹)⁻¹ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by
  have hmul := comm_Y_t_mul hz ha (inv_mem ha)
  have h1 : t * (a * a⁻¹) * t⁻¹ * (a * a⁻¹)⁻¹ = 1 := by group
  rw [h1] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem comm_Y_t_surj (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ v ∈ fourGrp x₁ x₂, ∃ a ∈ ctxYq t tau x₁ x₂ rho, t * a * t⁻¹ * a⁻¹ = v := by
  haveI : IsMulCommutative (ctxYq t tau x₁ x₂ rho) :=
    IsMulCommutative.of_comm fun x y =>
      Subtype.ext (hz.Q_comm x.1 (hz.Y_le_Q x.2) y.1 (hz.Y_le_Q y.2))
  obtain ⟨V', v₁, v₂, hV'⟩ := hz.data_V
  obtain ⟨_, _, _, _, hY, _, hv1V, hv2V, _, _, _, ht1, ht2, _, _⟩ := hV'
  have hv1Y : v₁ ∈ ctxYq t tau x₁ x₂ rho := by rw [hY]; exact mem_sup_right hv1V
  have hv2Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := by rw [hY]; exact mem_sup_right hv2V
  have hyY : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y (subset_closure (by simp))
  have hx2sqY : x₂ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := by
    refine hz.V_le_Y ?_
    rw [hz.x₂_sq]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hc1 : t * v₁ * t⁻¹ * v₁⁻¹ = x₁ ^ 2 := by
    rw [ht1, setLike_mul_comm hv1Y hyY]
    group
  have hc2 : t * v₂ * t⁻¹ * v₂⁻¹ = x₂ ^ 2 := by
    rw [ht2, setLike_mul_comm hv2Y hx2sqY]
    group
  intro v hv
  change v ∈ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) at hv
  induction hv using Subgroup.closure_induction with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]
        exact ⟨v₁, hv1Y, hc1⟩
      · rw [hg]
        refine ⟨v₁ * v₂, mul_mem hv1Y hv2Y, ?_⟩
        rw [hz.comm_Y_t_mul hv1Y hv2Y, hc1, hc2]
        have hysq : x₁ ^ 2 * x₁ ^ 2 = 1 := by simpa [pow_two] using hz.y_sq
        rw [hz.x₂_sq, ← mul_assoc, hysq, one_mul]
  | one => exact ⟨1, one_mem _, by group⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨a', ha'Y, ha'eq⟩ := iha
      obtain ⟨b', hb'Y, hb'eq⟩ := ihb
      exact ⟨a' * b', mul_mem ha'Y hb'Y, by rw [hz.comm_Y_t_mul ha'Y hb'Y, ha'eq, hb'eq]⟩
  | inv a _ iha =>
      obtain ⟨a', ha'Y, ha'eq⟩ := iha
      exact ⟨a'⁻¹, inv_mem ha'Y, by rw [hz.comm_Y_t_inv ha'Y, ha'eq]⟩

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
