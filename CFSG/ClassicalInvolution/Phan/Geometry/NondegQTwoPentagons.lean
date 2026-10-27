module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoTriangles

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph Module CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ}
    {W : Submodule K (Fin d → K)}

theorem exists_collGraph_pentApex (hσ : IsUnitaryInvolution σ) (hW : Nondeg σ W)
    (h5 : 5 ≤ finrank K W) {a c t : ↥(nsPts σ W)} (hct : (collGraph σ W).Adj c t) :
    ∃ f : ↥(nsPts σ W), (collGraph σ W).Adj a f ∧
      (collGraph σ W).Adj f c ∧ (collGraph σ W).Adj f t := by
  let P := c.1 ⊔ t.1
  have hPW : P ≤ W := sup_le c.2.1 t.2.1
  have hPnd : Nondeg σ P := hct.2
  have hPdim : finrank K P = 2 := finrank_sup_of_ne_pts c.2.2.1 t.2.2.1 hct.1
  let Z := W ⊓ perp σ P
  have hZnd : Nondeg σ Z := Nondeg.inf_perp hσ hW hPnd hPW
  have hZdim : 3 ≤ finrank K Z := by
    change 3 ≤ finrank K ↥(W ⊓ perp σ P)
    have he := finrank_eq_add_finrank_inf_perp hσ hPnd hPW
    rw [hPdim] at he
    omega
  obtain ⟨a₀, -, haW, haeq⟩ := mem_nsPts_iff.mp a.2
  have haSup : a₀ ∈ P ⊔ Z := by
    rw [sup_inf_perp_of_nondeg hσ _ rfl hPnd hPW]
    exact haW
  obtain ⟨x, hxP, z, hzZ, rfl⟩ := Submodule.mem_sup.mp haSup
  obtain ⟨u, huZ, huu, hzu⟩ := Q3G.exists_aniso_orth hσ hZnd hZdim hzZ
  have hxu : herm σ x u = 0 :=
    (herm_eq_zero_iff hσ u x).mp ((mem_perp.mp huZ.2) x hxP)
  have hau : herm σ (x + z) u = 0 := by rw [herm_add_left, hxu, hzu, add_zero]
  have hfu : K ∙ u ∈ nsPts σ W := span_singleton_mem_nsPts huu huZ.1
  have haf : Orth σ a.1 (K ∙ u) := by
    rw [haeq]
    exact orth_span_singleton_iff.mpr hau
  have hfP : Orth σ (K ∙ u) P := by
    intro v hv y hy
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [herm_smul_left, (mem_perp.mp huZ.2) y hy, mul_zero]
  have hfc : Orth σ (K ∙ u) c.1 := hfP.mono le_rfl le_sup_left
  have hft : Orth σ (K ∙ u) t.1 := hfP.mono le_rfl le_sup_right
  exact ⟨⟨K ∙ u, hfu⟩, IsCollinear.of_orth hσ a.2 hfu haf,
    IsCollinear.of_orth hσ hfu c.2 hfc, IsCollinear.of_orth hσ hfu t.2 hft⟩

theorem ndNullLen5 [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hW : Nondeg σ W) (h5 : 5 ≤ finrank K W)
    (h4 : NullLen (ndNull (σ := σ) (W := W) (by omega)) 4) :
    NullLen (ndNull (σ := σ) (W := W) (by omega)) 5 := by
  intro u p hp
  match u, p, hp with
  | a, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil)))), _ =>
    obtain ⟨f, haf, hfc, hfd⟩ := exists_collGraph_pentApex hσ hW h5 (a := a) h₃
    exact cycleHomotopic_pent_nil_of_apex (ndNull (σ := σ) (W := W) (by omega))
      (ndNullLen3 hσ hK (by omega)) h4 h₁ h₂ h₃ h₄ h₅ hfc hfd haf

end CFSG.ClassicalInvolution.Phan
