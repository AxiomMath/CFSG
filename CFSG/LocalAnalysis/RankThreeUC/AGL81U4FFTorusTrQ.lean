module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSecAct

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V]

@[expose] noncomputable def qv (M₀ M₁ : Subgroup V) (x : V) : Sec M₁ M₀ := by
  classical
  exact if h : x ∈ M₁ then QuotientGroup.mk ⟨x, h⟩ else 1

theorem qv_of_mem {M₀ M₁ : Subgroup V} {x : V} (hx : x ∈ M₁) :
    qv M₀ M₁ x = QuotientGroup.mk ⟨x, hx⟩ := by
  unfold qv
  exact dif_pos hx

theorem qv_mul {M₀ M₁ : Subgroup V} {x y : V} (hx : x ∈ M₁) (hy : y ∈ M₁) :
    qv M₀ M₁ (x * y) = qv M₀ M₁ x * qv M₀ M₁ y := by
  rw [qv_of_mem (M₁.mul_mem hx hy), qv_of_mem hx, qv_of_mem hy]
  rfl

theorem qv_inv {M₀ M₁ : Subgroup V} {x : V} (hx : x ∈ M₁) :
    qv M₀ M₁ x⁻¹ = (qv M₀ M₁ x)⁻¹ := by
  rw [qv_of_mem (M₁.inv_mem hx), qv_of_mem hx]
  rfl

theorem qv_eq_one_iff {M₀ M₁ : Subgroup V} {x : V} (hx : x ∈ M₁) :
    qv M₀ M₁ x = 1 ↔ x ∈ M₀ := by
  rw [qv_of_mem hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem qv_eq_iff {M₀ M₁ : Subgroup V} {x y : V} (hx : x ∈ M₁) (hy : y ∈ M₁) :
    qv M₀ M₁ x = qv M₀ M₁ y ↔ x⁻¹ * y ∈ M₀ := by
  rw [qv_of_mem hx, qv_of_mem hy, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact Iff.rfl

theorem qv_act {L : Subgroup (MulAut V)} {M₀ M₁ : Subgroup V} (hL1 : L ≤ stabSub M₁)
    (hL0 : L ≤ stabSub M₀) {g : MulAut V} (hg : g ∈ L) {x : V} (hx : x ∈ M₁) :
    secAct L hL1 hL0 ⟨g, hg⟩ (qv M₀ M₁ x) = qv M₀ M₁ (g x) := by
  have hgx : g x ∈ M₁ := (hL1 hg x).2 hx
  rw [qv_of_mem hx, qv_of_mem hgx]
  exact secAct_mk L hL1 hL0 ⟨g, hg⟩ ⟨x, hx⟩

private theorem qv_one {M₀ M₁ : Subgroup V} : qv M₀ M₁ 1 = 1 := by
  rw [qv_of_mem M₁.one_mem]
  rfl

theorem qv_prod {M₀ M₁ : Subgroup V} {ι : Type} (s : Finset ι) (f : ι → V)
    (hf : ∀ i ∈ s, f i ∈ M₁) :
    qv M₀ M₁ (∏ i ∈ s, f i) = ∏ i ∈ s, qv M₀ M₁ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact qv_one
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ∈ M₁ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, f i) ∈ M₁ := M₁.prod_mem hs
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      qv_mul (hf a (Finset.mem_insert_self a s)) hprod, ih hs]

end CFSG.LocalAnalysis.RankThreeUC
