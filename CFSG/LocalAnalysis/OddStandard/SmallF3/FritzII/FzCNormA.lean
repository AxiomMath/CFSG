module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCStepsDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_pCoreOf_two_isPGroup (N : Subgroup G) :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 N) := by
  rw [CFSG.Open.pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem fzc_pCoreOf_two_conj_mem {N : Subgroup G} {g : G} (hg : g ∈ N) {q : G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 N) : g * q * g⁻¹ ∈ CFSG.Open.pCoreOf 2 N := by
  rw [CFSG.Open.pCoreOf] at hq ⊢
  obtain ⟨o', ho', rfl⟩ := hq
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem fzc_le_pCoreOf_two {N Q : Subgroup G} (hQN : Q ≤ N)
    (hnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) (hQ : IsPGroup 2 Q) :
    Q ≤ CFSG.Open.pCoreOf 2 N := by
  have hnormal : (Q.subgroupOf N).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hnorm g g.2 x hx
  have hp : IsPGroup 2 (Q.subgroupOf N) := hQ.comap_subtype
  have hcore : Q.subgroupOf N ≤ CFSG.pCore 2 ↥N := le_sSup ⟨hnormal, hp⟩
  rw [CFSG.Open.pCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hQN]
  exact Subgroup.map_mono hcore

theorem fzc_comm_W (hs : FzCSteps t L S x₁ x₂ lam rho) :
    ∀ a ∈ ctxW t x₁ x₂, ∀ b ∈ ctxW t x₁ x₂, a * b = b * a := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := hs.ctx.abelian_W
  intro a ha b hb
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) ⟨b, hb⟩)

def fzcOmegaOne (W : Subgroup G)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : Subgroup G where
  carrier := {w | w ∈ W ∧ w * w = 1}
  mul_mem' := by
    rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
    refine ⟨W.mul_mem haW hbW, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hW b hbW a haW]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := ⟨W.one_mem, mul_one 1⟩
  inv_mem' := by
    rintro a ⟨haW, ha⟩
    refine ⟨W.inv_mem haW, ?_⟩
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [ha, inv_one]

theorem fzc_mem_omegaOne {W : Subgroup G}
    {hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a} {w : G} :
    w ∈ fzcOmegaOne W hW ↔ w ∈ W ∧ w * w = 1 := Iff.rfl

theorem fzc_ctxE_le_ctxW (hs : FzCSteps t L S x₁ x₂ lam rho) :
    ctxE t x₁ x₂ ≤ ctxW t x₁ x₂ := by
  have hy : x₁ ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hz : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := by
    rw [baseGrp]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2
  rw [ctxE]
  refine (Subgroup.closure_le (K := ctxW t x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left hs.ctx.hyp.mem_twoCore
  · exact Subgroup.mem_sup_right hy
  · exact Subgroup.mem_sup_right hz

theorem fzc_omega_ctxW_le (hs : FzCSteps t L S x₁ x₂ lam rho) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) (hw2 : w * w = 1) : w ∈ ctxE t x₁ x₂ := by
  have hcommW := fzc_comm_W hs
  have hnorm : NormalIn (fzcOmegaOne (ctxW t x₁ x₂) hcommW) S := by
    refine ⟨fun e he => hs.basic.normal_W.1 (fzc_mem_omegaOne.mp he).1, ?_⟩
    intro s hs' e he
    obtain ⟨heW, he2⟩ := fzc_mem_omegaOne.mp he
    refine fzc_mem_omegaOne.mpr ⟨hs.basic.normal_W.2 s hs' e heW, ?_⟩
    calc s * e * s⁻¹ * (s * e * s⁻¹) = s * (e * e) * s⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have helem : CFSG.Open.IsElemAbelian 2 (fzcOmegaOne (ctxW t x₁ x₂) hcommW) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (hcommW a (fzc_mem_omegaOne.mp a.2).1 b (fzc_mem_omegaOne.mp b.2).1)
    · rw [pow_two]
      exact (fzc_mem_omegaOne.mp hx).2
  exact hs.basic.normal_elem_le (fzcOmegaOne (ctxW t x₁ x₂) hcommW) hnorm helem
    (fzc_mem_omegaOne.mpr ⟨hw, hw2⟩)

theorem fzc_conj_W (hs : FzCSteps t L S x₁ x₂ lam rho) {n : G}
    (hn : n ∈ l41N t x₁ x₂) {w : G} (hw : w ∈ ctxW t x₁ x₂) :
    n * w * n⁻¹ ∈ ctxW t x₁ x₂ := by
  rw [← hs.basic.cent_A] at hw ⊢
  rw [Subgroup.mem_centralizer_iff] at hw ⊢
  intro a ha
  have ha' : n⁻¹ * a * n ∈ ctxE t x₁ x₂ :=
    (Subgroup.mem_normalizer_iff''.mp hn a).mp ha
  have h1 := hw _ ha'
  calc a * (n * w * n⁻¹) = n * ((n⁻¹ * a * n) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * a * n)) * n⁻¹ := by rw [h1]
    _ = (n * w * n⁻¹) * a := by group

theorem fzc_normalizer_O2 (hs : FzCSteps t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ l41N t x₁ x₂) :
    g ∈ normalizer ((l41O2 t x₁ x₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  exact ⟨fun hq => fzc_pCoreOf_two_conj_mem hg hq, fun hq => by
    have h2 := fzc_pCoreOf_two_conj_mem (Subgroup.inv_mem _ hg) hq
    have e : g⁻¹ * (g * q * g⁻¹) * (g⁻¹)⁻¹ = q := by group
    rwa [e] at h2⟩

end CFSG.OddStandard.SmallF3.FritzII
