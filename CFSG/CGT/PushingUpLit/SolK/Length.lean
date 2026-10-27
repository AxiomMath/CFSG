module

public import CFSG.CGT.PushingUpLit.SolK.Vec
public import CFSG.CGT.PushingUpLit.SolK.Cfg

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem decomp_unique {w₁ w₂ r₁ r₂ : G} (hw₁ : w₁ ∈ S.D.W) (hw₂ : w₂ ∈ S.D.W)
    (hr₁ : r₁ ∈ rOf M X) (hr₂ : r₂ ∈ rOf M X) (h : w₁ * r₁ = w₂ * r₂) : w₁ = w₂ ∧ r₁ = r₂ := by
  have h1 : w₂⁻¹ * w₁ = r₂ * r₁⁻¹ := by
    calc w₂⁻¹ * w₁ = w₂⁻¹ * (w₁ * r₁) * r₁⁻¹ := by group
      _ = w₂⁻¹ * (w₂ * r₂) * r₁⁻¹ := by rw [h]
      _ = r₂ * r₁⁻¹ := by group
  have hW : w₂⁻¹ * w₁ ∈ S.D.W := S.D.W.mul_mem (S.D.W.inv_mem hw₂) hw₁
  have hR : w₂⁻¹ * w₁ ∈ rOf M X := h1 ▸ (rOf M X).mul_mem hr₂ ((rOf M X).inv_mem hr₁)
  have h2 : w₂⁻¹ * w₁ = 1 := S.W_inf_R hW hR
  have hw : w₁ = w₂ := by
    calc w₁ = w₂ * (w₂⁻¹ * w₁) := by group
      _ = w₂ := by rw [h2, mul_one]
  refine ⟨hw, ?_⟩
  rw [hw] at h
  exact mul_left_cancel h

@[expose] def HasLen (x : G) (l : ℕ) : Prop :=
  ∃ (w : G) (hw : w ∈ S.D.W) (r : G), r ∈ rOf M X ∧ x = w * r ∧
    (vsupp (S.D.β ⟨w, hw⟩)).card = l

theorem exists_hasLen {x : G} (hx : x ∈ pCoreOf 2 M) : ∃ l, S.HasLen x l := by
  obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq x hx
  exact ⟨_, w, hw, r, hr, rfl, rfl⟩

theorem HasLen.unique {x : G} {l l' : ℕ} (h : S.HasLen x l) (h' : S.HasLen x l') : l = l' := by
  obtain ⟨w, hw, r, hr, rfl, rfl⟩ := h
  obtain ⟨w', hw', r', hr', he, rfl⟩ := h'
  obtain ⟨rfl, -⟩ := S.decomp_unique hw hw' hr hr' he
  rfl

theorem HasLen.even {x : G} {l : ℕ} (h : S.HasLen x l) : Even l := by
  obtain ⟨w, hw, r, hr, rfl, rfl⟩ := h
  exact even_card_vsupp _

theorem HasLen.le {x : G} {l : ℕ} (h : S.HasLen x l) : l ≤ 2 * n + 1 := by
  obtain ⟨w, hw, r, hr, rfl, rfl⟩ := h
  exact (Finset.card_le_univ _).trans (by simp)

theorem θ_X (x : ↥X) : S.θ ⟨(x : G), S.hyp.le x.2⟩ = S.D.ρ x :=
  theta_X S.D S.xnorm S.hyp.two_le x

theorem θ_spec (m : ↥M) (w : ↥S.D.W) (hw' : (m : G) * (w : G) * (m : G)⁻¹ ∈ S.D.W) :
    S.D.β ⟨(m : G) * (w : G) * (m : G)⁻¹, hw'⟩ =
      coreAct (2 * n + 1) (S.θ m) (S.D.β w) :=
  theta_spec S.D S.xnorm S.hyp.two_le m w hw'

theorem fix_of_comm {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (m : ↥M)
    (h : (m : G) * (w * r) * (m : G)⁻¹ = w * r) :
    coreAct (2 * n + 1) (S.θ m) (S.D.β ⟨w, hw⟩) = S.D.β ⟨w, hw⟩ := by
  have hw' : (m : G) * w * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 hw
  have hr' : (m : G) * r * (m : G)⁻¹ ∈ rOf M X := S.R_normalized m.2 hr
  have e : (m : G) * (w * r) * (m : G)⁻¹ =
      ((m : G) * w * (m : G)⁻¹) * ((m : G) * r * (m : G)⁻¹) := by
    group
  rw [e] at h
  obtain ⟨h1, -⟩ := S.decomp_unique hw' hw hr' hr h
  rw [← S.θ_spec m ⟨w, hw⟩ hw']
  congr 1
  exact Subtype.ext h1

theorem comm_of_fix_X {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (c : ↥X)
    (h : coreAct (2 * n + 1) (S.D.ρ c) (S.D.β ⟨w, hw⟩) = S.D.β ⟨w, hw⟩) :
    (c : G) * (w * r) * (c : G)⁻¹ = w * r := by
  have hw' : (c : G) * w * (c : G)⁻¹ ∈ S.D.W := S.W_normalized (S.hyp.le c.2) hw
  have h1 : (c : G) * w * (c : G)⁻¹ = w := by
    have := S.D.equivar c ⟨w, hw⟩ hw'
    rw [h] at this
    exact congrArg Subtype.val (S.D.β.injective this)
  have h2 : (c : G) * r * (c : G)⁻¹ = r := by
    have := Subgroup.mem_centralizer_iff.1 hr.2 (c : G) c.2
    rw [this, mul_inv_cancel_right]
  have e : (c : G) * (w * r) * (c : G)⁻¹ =
      ((c : G) * w * (c : G)⁻¹) * ((c : G) * r * (c : G)⁻¹) := by
    group
  rw [e, h1, h2]

end SolCfg

structure TightData (S : SolCfg G M X n) : Prop where
  abelian : ∀ q ∈ pCoreOf 2 M, ∀ q' ∈ pCoreOf 2 M, q * q' = q' * q
  ker_two : ∀ m : ↥M, S.θ m = 1 → (∃ j : ℕ, (m : G) ^ (2 ^ j) = 1) → (m : G) ∈ pCoreOf 2 M

omit [Finite G] in
theorem mem_centralizer_zpowers_iff {x m : G} :
    m ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ↔ m * x * m⁻¹ = x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have := h x (Subgroup.mem_zpowers x)
    calc m * x * m⁻¹ = x * m * m⁻¹ := by rw [← this]
      _ = x := by group
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute x m := by
      have : x * m = m * x := by
        calc x * m = (m * x * m⁻¹) * m := by rw [h]
          _ = m * x := by group
      exact this
    exact (hc.zpow_left k)

end CFSG.CGT.PushingUpLit.SolK
