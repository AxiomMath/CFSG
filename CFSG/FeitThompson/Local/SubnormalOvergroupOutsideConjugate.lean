module

public import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem forall_inf_conj_inv_smul_eq_bot_iff {K L : Subgroup G} :
    (∀ g ∉ L, K ⊓ MulAut.conj g⁻¹ • L = ⊥) ↔ ∀ g ∉ L, K ⊓ MulAut.conj g • L = ⊥ := by
  constructor <;> intro h g hg <;> simpa using h g⁻¹ (by simpa using hg)

private theorem step_le {K L M N : Subgroup G} (hK : K ≠ ⊥)
    (hdisj : ∀ g ∉ L, K ⊓ MulAut.conj g⁻¹ • L = ⊥)
    (hKM : K ≤ M) (hML : M ≤ L) (hMN : M ≤ N)
    (hnormal : (M.subgroupOf N).Normal) : N ≤ L := by
  intro b hb
  by_contra hbL
  have hKconj : K ≤ MulAut.conj b • L := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hmem : b⁻¹ * x * b ∈ M := by
      have := (Subgroup.normal_subgroupOf_iff hMN).1 hnormal x b⁻¹ (hKM hx) (inv_mem hb)
      simpa using this
    have hx' : (MulAut.conj b)⁻¹ • x = b⁻¹ * x * b := by simp [mul_assoc]
    rw [hx']
    exact hML hmem
  have h := hdisj b⁻¹ (by simpa using hbL)
  rw [inv_inv, inf_eq_left.2 hKconj] at h
  exact hK h

private theorem normal_subgroupOf_map_subtype {B : Subgroup G} {H₁ H₂ : Subgroup B}
    (hle : H₁ ≤ H₂) (h : (H₁.subgroupOf H₂).Normal) :
    ((H₁.map B.subtype).subgroupOf (H₂.map B.subtype)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hle)]
  intro _ _ hh hk
  simp only [Subgroup.mem_map, Subgroup.coe_subtype] at hh hk ⊢
  obtain ⟨a, ha, rfl⟩ := hh
  obtain ⟨b, hb, rfl⟩ := hk
  exact ⟨b * a * b⁻¹, (Subgroup.normal_subgroupOf_iff hle).1 h a b ha hb, by push_cast; ring_nf⟩

theorem le_of_subnormal_chain_of_inf_conj_eq_bot {K L B : Subgroup G} (hK : K ≠ ⊥) (hKL : K ≤ L)
    (hdisj : ∀ g ∉ L, K ⊓ MulAut.conj g⁻¹ • L = ⊥)
    {n : ℕ} {C : ℕ → Subgroup G} (hC0 : C 0 = K) (hCn : C n = B)
    (hle : ∀ i < n, C i ≤ C (i + 1))
    (hnormal : ∀ i < n, ((C i).subgroupOf (C (i + 1))).Normal) : B ≤ L := by
  have key : ∀ i ≤ n, K ≤ C i ∧ C i ≤ L := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hC0.ge, hC0.le.trans hKL⟩
    | succ i ih =>
      intro hi
      have hin : i < n := lt_of_lt_of_le (Nat.lt_succ_self i) hi
      obtain ⟨hKi, hiL⟩ := ih hin.le
      exact ⟨hKi.trans (hle i hin), step_le hK hdisj hKi hiL (hle i hin) (hnormal i hin)⟩
  exact hCn ▸ (key n le_rfl).2

theorem le_of_isSubnormal_of_inf_conj_eq_bot {K L B : Subgroup G} (hK : K ≠ ⊥) (hKL : K ≤ L)
    (hdisj : ∀ g ∉ L, K ⊓ MulAut.conj g⁻¹ • L = ⊥) (hKB : K ≤ B)
    (hsub : (K.subgroupOf B).IsSubnormal) : B ≤ L := by
  have key : ∀ {H : Subgroup B}, H.IsSubnormal →
      K ≤ H.map B.subtype → H.map B.subtype ≤ L → B ≤ L := by
    intro H hH
    induction hH with
    | top =>
      intro _ h2
      rwa [← Subgroup.subgroupOf_self B, Subgroup.map_subgroupOf_eq_of_le le_rfl] at h2
    | step H₁ H₂ hle _ hn ih =>
      intro h1 h2
      have hmaple : H₁.map B.subtype ≤ H₂.map B.subtype := Subgroup.map_mono hle
      exact ih (h1.trans hmaple)
        (step_le hK hdisj h1 h2 hmaple (normal_subgroupOf_map_subtype hle hn))
  refine key hsub ?_ ?_
  · rw [Subgroup.map_subgroupOf_eq_of_le hKB]
  · rw [Subgroup.map_subgroupOf_eq_of_le hKB]; exact hKL

end CFSG.FeitThompson
