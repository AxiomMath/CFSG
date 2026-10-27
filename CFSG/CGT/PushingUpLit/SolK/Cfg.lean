module

public import CFSG.CGT.PushingUpLit.SolK.MAction

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

structure SolCfg (G : Type) [Group G] [Finite G] (M X : Subgroup G) (n : ℕ) where
  hyp : SolHyp G M X n
  D : ModData G X n

namespace SolCfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)
include S

theorem xnorm : XNorm M X where
  le := S.hyp.le
  normal := fun m hm x hx => by
    have h1 := S.hyp.normal.conj_mem ⟨x, S.hyp.le hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.1 h1

theorem res : oResidualTwo ↥X = ⊤ := S.hyp.short.residual_eq

@[expose] noncomputable def θ : ↥M →* Perm (Fin (2 * n + 1)) :=
  theta S.D S.xnorm S.hyp.two_le


theorem q_eq (q : G) (hq : q ∈ pCoreOf 2 M) : ∃ w ∈ S.D.W, ∃ r ∈ rOf M X, q = w * r :=
  S.xnorm.q_eq_W_mul_R S.D S.hyp.two_le S.res hq

theorem q_comm_W {q w : G} (hq : q ∈ pCoreOf 2 M) (hw : w ∈ S.D.W) : q * w = w * q :=
  comm_of_conj_eq (S.xnorm.q_centralizes_W S.hyp.two_le hq w hw)

theorem W_normalized {m w : G} (hm : m ∈ M) (hw : w ∈ S.D.W) : m * w * m⁻¹ ∈ S.D.W :=
  S.xnorm.W_normalized hm hw

theorem W_le_Q : S.D.W ≤ pCoreOf 2 M := S.xnorm.W_le_Q S.D

theorem W_inf_R {w : G} (hw : w ∈ S.D.W) (hr : w ∈ rOf M X) : w = 1 := by
  refine S.D.fix S.hyp.two_le hw (fun x hx => ?_)
  have := Subgroup.mem_centralizer_iff.1 hr.2 x hx
  rw [this, mul_inv_cancel_right]

theorem W_comm_R {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) : w * r = r * w :=
  Subgroup.mem_centralizer_iff.1 hr.2 w (ModData.W_le_X S.D hw)

theorem R_normalized {m r : G} (hm : m ∈ M) (hr : r ∈ rOf M X) : m * r * m⁻¹ ∈ rOf M X := by
  refine Subgroup.mem_inf.2 ⟨pCoreOf_normalized M hm hr.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : m⁻¹ * x * m ∈ X := by
    have := S.xnorm.normal m⁻¹ (M.inv_mem hm) x hx
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hr.2 _ h1
  calc x * (m * r * m⁻¹) = m * ((m⁻¹ * x * m) * r) * m⁻¹ := by group
    _ = m * (r * (m⁻¹ * x * m)) * m⁻¹ := by rw [h2]
    _ = m * r * m⁻¹ * x := by group

end SolCfg

theorem exists_solCfg {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (h : SolHyp G M X n) : Nonempty (SolCfg G M X n) := by
  obtain ⟨D⟩ := exists_modData (G := G) (X := X) h.short h.two_le h.nat
  exact ⟨⟨h, D⟩⟩

end CFSG.CGT.PushingUpLit.SolK
