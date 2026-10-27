module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem fzc_mem_invCent_iff {u g : G} : g ∈ invCent u ↔ g * u = u * g := by
  rw [invCent]
  exact Subgroup.mem_centralizer_singleton_iff

private theorem fzc_W_comm (hs : FzCSteps t L S x₁ x₂ lam rho) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := hs.ctx.abelian_W
  exact setLike_mul_comm ha hb

theorem fzc_four_sq (hs : FzCSteps t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ fourGrp x₁ x₂) :
    f * f = 1 := by
  have hE : CFSG.Open.IsElemAbelian 2 (fourGrp x₁ x₂) :=
    hs.ctx.wreath.fourGrp_eq_omega.2.1
  simpa [pow_two] using hE.2 f hf

theorem fzc_four_comm (hs : FzCSteps t L S x₁ x₂ lam rho) {f g : G} (hf : f ∈ fourGrp x₁ x₂)
    (hg : g ∈ fourGrp x₁ x₂) : f * g = g * f := by
  have hE : CFSG.Open.IsElemAbelian 2 (fourGrp x₁ x₂) :=
    hs.ctx.wreath.fourGrp_eq_omega.2.1
  haveI : IsMulCommutative (fourGrp x₁ x₂) := hE.1
  exact setLike_mul_comm hf hg

theorem fzc_t_mem_W (hs : FzCSteps t L S x₁ x₂ lam rho) : t ∈ ctxW t x₁ x₂ :=
  Subgroup.mem_sup_left hs.ctx.hyp.mem_twoCore

theorem fzc_R_cent_four (hs : FzCSteps t L S x₁ x₂ lam rho) {r : G}
    (hr : r ∈ fzR t x₁ x₂) {f : G} (hf : f ∈ fourGrp x₁ x₂) : r * f = f * r := by
  have hR : r ∈ l41O2 t x₁ x₂ := by rwa [fzc_R_eq hs] at hr
  have hcent : r ∈ l41N t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [← hs.O2_eq]
    exact hR
  exact (Subgroup.mem_centralizer_iff.mp hcent.2 f hf).symm

theorem fzc_R_act_t (hs : FzCSteps t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ fzR t x₁ x₂) :
    ∃ f ∈ fourGrp x₁ x₂, r * t * r⁻¹ = t * f := by
  have hN : r ∈ l41N t x₁ x₂ := by
    rw [fzc_R_eq hs] at hr
    exact Subgroup.map_subtype_le (CFSG.pCore 2 (l41N t x₁ x₂)) hr
  have hmem : r * t * r⁻¹ ∈ conjIn (l41N t x₁ x₂) t := ⟨r, hN, rfl⟩
  rw [hs.orbit_t] at hmem
  rw [Set.mem_smul_set] at hmem
  obtain ⟨f, hf, hft⟩ := hmem
  exact ⟨f, hf, by simpa using hft.symm⟩

theorem fzc_R_orbit_t (hs : FzCSteps t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ fourGrp x₁ x₂) :
    ∃ r ∈ fzR t x₁ x₂, r * t * r⁻¹ = t * f := by
  have hmem : t * f ∈ conjIn (l41N t x₁ x₂) t := by
    rw [hs.orbit_t, Set.mem_smul_set]
    exact ⟨f, hf, rfl⟩
  rw [conjIn] at hmem
  obtain ⟨n, hn, hn_eq⟩ := hmem
  obtain ⟨o, ho, c, hc, hc_eq⟩ := fzc_decomp hs hn
  rw [hc_eq] at hn_eq
  have hct : c * t * c⁻¹ = t := fzc_closure_cent_t hs hc
  refine ⟨o, ho, ?_⟩
  calc o * t * o⁻¹ = o * (c * t * c⁻¹) * o⁻¹ := by rw [hct]
    _ = (o * c) * t * (o * c)⁻¹ := by group
    _ = t * f := hn_eq

theorem fzc_cent_R_t (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzR t x₁ x₂ ⊓ invCent t = ctxW t x₁ x₂ := by
  apply le_antisymm
  · intro r hr
    have hle : ctxE t x₁ x₂ ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [ctxE]
      refine (Subgroup.closure_le _).mpr ?_
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (fzc_mem_invCent_iff.mp hr.2).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (fzc_R_cent_four hs hr.1 (Subgroup.subset_closure (by simp))).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (fzc_R_cent_four hs hr.1 (Subgroup.subset_closure (by simp))).symm
    rw [← hs.basic.cent_A, Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  · intro w hw
    refine ⟨fzc_W_le_R hs hw, ?_⟩
    exact fzc_mem_invCent_iff.mpr (fzc_W_comm hs hw (fzc_t_mem_W hs))

theorem fzc_R_sq_mem_W (hs : FzCSteps t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ fzR t x₁ x₂) :
    r * r ∈ ctxW t x₁ x₂ := by
  obtain ⟨f, hf, hfeq⟩ := fzc_R_act_t hs hr
  have hfr : r * f = f * r := fzc_R_cent_four hs hr hf
  have hff : f * f = 1 := fzc_four_sq hs hf
  have hc : r * f * r⁻¹ = f := by rw [hfr]; group
  have hconj : (r * r) * t * (r * r)⁻¹ = t := by
    calc (r * r) * t * (r * r)⁻¹ = r * (r * t * r⁻¹) * r⁻¹ := by group
      _ = r * (t * f) * r⁻¹ := by rw [hfeq]
      _ = (r * t * r⁻¹) * (r * f * r⁻¹) := by group
      _ = (t * f) * f := by rw [hfeq, hc]
      _ = t := by rw [mul_assoc, hff, mul_one]
  rw [← fzc_cent_R_t hs]
  refine ⟨mul_mem hr hr, ?_⟩
  exact fzc_mem_invCent_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj)

private theorem fzc_comm_conj_mem_W (hs : FzCSteps t L S x₁ x₂ lam rho) {a b : G}
    (ha : a ∈ fzR t x₁ x₂) (hb : b ∈ fzR t x₁ x₂) :
    (b * a)⁻¹ * (a * b) ∈ ctxW t x₁ x₂ := by
  obtain ⟨f, hf, hfeq⟩ := fzc_R_act_t hs ha
  obtain ⟨f', hf', hf'eq⟩ := fzc_R_act_t hs hb
  have haf' : a * f' = f' * a := fzc_R_cent_four hs ha hf'
  have hbf : b * f = f * b := fzc_R_cent_four hs hb hf
  have hff' : f * f' = f' * f := fzc_four_comm hs hf hf'
  have hab : (a * b) * t * (a * b)⁻¹ = t * (f * f') := by
    have hac : a * f' * a⁻¹ = f' := by rw [haf']; group
    calc (a * b) * t * (a * b)⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by group
      _ = a * (t * f') * a⁻¹ := by rw [hf'eq]
      _ = (a * t * a⁻¹) * (a * f' * a⁻¹) := by group
      _ = (t * f) * f' := by rw [hfeq, hac]
      _ = t * (f * f') := by rw [mul_assoc]
  have hba : (b * a) * t * (b * a)⁻¹ = t * (f * f') := by
    have hbc : b * f * b⁻¹ = f := by rw [hbf]; group
    calc (b * a) * t * (b * a)⁻¹ = b * (a * t * a⁻¹) * b⁻¹ := by group
      _ = b * (t * f) * b⁻¹ := by rw [hfeq]
      _ = (b * t * b⁻¹) * (b * f * b⁻¹) := by group
      _ = (t * f') * f := by rw [hf'eq, hbc]
      _ = t * (f' * f) := by rw [mul_assoc]
      _ = t * (f * f') := by rw [hff']
  have hconj : ((b * a)⁻¹ * (a * b)) * t * ((b * a)⁻¹ * (a * b))⁻¹ = t := by
    calc ((b * a)⁻¹ * (a * b)) * t * ((b * a)⁻¹ * (a * b))⁻¹
        = (b * a)⁻¹ * ((a * b) * t * (a * b)⁻¹) * (b * a) := by group
      _ = (b * a)⁻¹ * (t * (f * f')) * (b * a) := by rw [hab]
      _ = (b * a)⁻¹ * ((b * a) * t * (b * a)⁻¹) * (b * a) := by rw [← hba]
      _ = t := by group
  rw [← fzc_cent_R_t hs]
  refine ⟨(fzR t x₁ x₂).mul_mem ((fzR t x₁ x₂).inv_mem ((fzR t x₁ x₂).mul_mem hb ha))
    ((fzR t x₁ x₂).mul_mem ha hb), ?_⟩
  exact fzc_mem_invCent_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj)

theorem fzc_R_comm_le_W (hs : FzCSteps t L S x₁ x₂ lam rho) :
    ⁅fzR t x₁ x₂, fzR t x₁ x₂⁆ ≤ ctxW t x₁ x₂ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := fzc_comm_conj_mem_W hs ((fzR t x₁ x₂).inv_mem ha) ((fzR t x₁ x₂).inv_mem hb)
  have h' : ⁅a, b⁆ = (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]; group
  rw [h']
  exact h

end CFSG.OddStandard.SmallF3.FritzII
