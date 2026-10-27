module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

structure Z4VBase (t tau x₁ x₂ lam rho : G) (V' : Subgroup G) (v₁ v₂ : G) : Prop where
  elem : CFSG.Open.IsElemAbelian 2 V'
  card : Nat.card V' = 4
  Q_eq : ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V'
  B_inf : baseGrp x₁ x₂ ⊓ V' = ⊥
  Y_eq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V'
  V_inf : fourGrp x₁ x₂ ⊓ V' = ⊥
  rho_mem : rho ∈ normalizer (V' : Set G)
  v₁_mem : v₁ ∈ V'
  v₂_mem : v₂ ∈ V'
  v₁_ne : v₁ ≠ 1
  v₂_nmem : v₂ ∉ zpowers v₁
  gen : V' = closure {v₁, v₂}
  t_v₁ : t * v₁ * t⁻¹ = v₁ * x₁ ^ 2
  t_v₂ : t * v₂ * t⁻¹ = v₂ * x₂ ^ 2
  sigma_v₁ : (lam * t) * v₁ * (lam * t)⁻¹ = v₂

namespace Z4VBase

variable {V' : Subgroup G} {v₁ v₂ : G}

theorem toCtx4ZV (h : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂)
    (hlast : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) =
      closure {x₁ * v₁, x₂ * v₂}) : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂ :=
  ⟨h.elem, h.card, h.Q_eq, h.B_inf, h.Y_eq, h.rho_mem, h.v₁_mem, h.v₂_mem, h.v₁_ne, h.v₂_nmem,
    h.gen, h.t_v₁, h.t_v₂, h.sigma_v₁, hlast⟩

variable (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂)
include hV

theorem sq_eq_one {a : G} (ha : a ∈ V') : a * a = 1 := by
  simpa [pow_two] using hV.elem.2 a ha

theorem V'_le_Y : V' ≤ ctxYq t tau x₁ x₂ rho := by
  rw [hV.Y_eq]; exact le_sup_right

theorem V'_le_Q (hp : Z4Pre t L S x₁ x₂ lam rho tau) : V' ≤ ctxQ t tau x₁ x₂ rho :=
  (hV.V'_le_Y).trans hp.Y_le_Q

theorem mem_Q_decomp (hp : Z4Pre t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ ctxQ t tau x₁ x₂ rho) : ∃ b ∈ baseGrp x₁ x₂, ∃ v ∈ V', a = b * v := by
  rw [hV.Q_eq] at ha
  refine mem_sup_of_normalizes (fun c hc b hb => ?_) ha
  have h : b * c = c * b :=
    hp.Q_comm _ (hp.base_le_Q hb) _ (hV.V'_le_Q hp hc)
  rw [← h]
  simpa using hb

theorem comm_v₁ (hp : Z4Pre t L S x₁ x₂ lam rho tau) : z4Comm t v₁ = x₁ ^ 2 := by
  have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hp.V_le_Y hp.y_mem_V
  have hc : v₁ * x₁ ^ 2 = x₁ ^ 2 * v₁ :=
    hp.Y_comm _ (hV.V'_le_Y hV.v₁_mem) _ hy
  unfold z4Comm
  rw [hV.t_v₁, hc]
  group

theorem comm_v₂ (hp : Z4Pre t L S x₁ x₂ lam rho tau) : z4Comm t v₂ = x₂ ^ 2 := by
  have hw : x₂ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hp.V_le_Y hp.w_mem_V
  have hc : v₂ * x₂ ^ 2 = x₂ ^ 2 * v₂ :=
    hp.Y_comm _ (hV.V'_le_Y hV.v₂_mem) _ hw
  unfold z4Comm
  rw [hV.t_v₂, hc]
  group

theorem eq_one_of_comm (hp : Z4Pre t L S x₁ x₂ lam rho tau) {v : G} (hv : v ∈ V')
    (h : z4Comm t v = 1) : v = 1 := by
  have h1 : v ∈ fourGrp x₁ x₂ := (hp.comm_t_eq_one_iff (hV.V'_le_Y hv)).mp h
  have h2 : v ∈ fourGrp x₁ x₂ ⊓ V' := ⟨h1, hv⟩
  rw [hV.V_inf] at h2
  exact mem_bot.mp h2

end Z4VBase

end CFSG.OddStandard.SmallF3.HarrisU33
