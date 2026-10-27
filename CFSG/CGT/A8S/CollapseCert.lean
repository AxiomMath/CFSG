module

public import CFSG.CGT.A8S.Collapse
public import CFSG.CGT.A8S.Interfaces
public import Certificates.Certificate21199

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable CFSG.CGT.Timmesfeld75

theorem collapseCheckA8_eq_true : ∀ k : Fin 7, CollapseA8 k :=
  Certificates.certificate21199.2

theorem collapse_index_one (k : Fin 7) {H : Type*} [Group H]
    (e : Fin 6 → H) (hN0 : ∀ r ∈ relsN0A8, evalA8 e (liftW5 r) = 1)
    (hθ : ∀ r ∈ thetaRelsA8, evalA8 e r = 1)
    (hw : e 5 * e 1 * e 5 * (e 1)⁻¹ * e 5 = evalA8 e (wrongWordA8 k)) :
    e 5 ∈ Subgroup.closure (Set.range fun i : Fin 5 => e (Fin.castSucc i)) :=
  mem_closure_of_collapseCheckA8' (collapseCheckA8_eq_true k) e hN0 hθ hw

section Config

variable {G : Type} [Group G] {T T₁ : Subgroup G}

private theorem gens_five (c : T1ConfigA8 T T₁) : c.gens 5 = c.g := by
  simp [T1ConfigA8.gens, genTupleA8]

private theorem gens_castSucc (c : T1ConfigA8 T T₁) (i : Fin 5) :
    c.gens (Fin.castSucc i) = ((c.ψ (PresentedGroup.of i) :
      ↥(Subgroup.normalizer (T : Set G))) : G) := by
  simp [T1ConfigA8.gens, genTupleA8]

private theorem gens_relsN0A8 (c : T1ConfigA8 T T₁) {r : List (Fin 5 × Bool)}
    (hr : r ∈ relsN0A8) : evalA8 c.gens (liftW5 r) = 1 := by
  set f : PG 5 relsN0A8 →* G :=
    (Subgroup.normalizer (T : Set G)).subtype.comp c.ψ.toMonoidHom
  have hlift : FreeGroup.lift (fun i : Fin 5 => c.gens (Fin.castSucc i)) =
      f.comp (PresentedGroup.mk _) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [FreeGroup.lift_apply_of, gens_castSucc]
    rfl
  rw [evalA8_liftW5, hlift, MonoidHom.comp_apply,
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr), map_one]

private theorem closure_gens_le (c : T1ConfigA8 T T₁) :
    Subgroup.closure (Set.range fun i : Fin 5 => c.gens (Fin.castSucc i)) ≤
      Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  show c.gens (Fin.castSucc i) ∈ Subgroup.normalizer (T : Set G)
  rw [gens_castSucc]
  exact (c.ψ _).2

theorem T1ConfigA8.collapse_g_mem_normalizer
    (c : T1ConfigA8 T T₁) (k : Fin 7)
    (hw : c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g = evalA8 c.gens (wrongWordA8 k)) :
    c.g ∈ Subgroup.normalizer (T : Set G) := by
  have hθ : ∀ r ∈ thetaRelsA8, evalA8 c.gens r = 1 := c.rel
  rw [← gens_five c] at hw ⊢
  exact closure_gens_le c (collapse_index_one k c.gens (fun _ hr => gens_relsN0A8 c hr) hθ hw)

private theorem g_not_mem_normalizer (hyp : A8CtxHyp T T₁) (c : T1ConfigA8 T T₁) :
    c.g ∉ Subgroup.normalizer (T : Set G) := by
  intro hg
  have hT : conjSubgroup c.g T = T := by
    ext x
    rw [mem_conjSubgroup, Subgroup.mem_normalizer_iff.1 hg]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hbot : T = ⊥ := by
    have h := hyp.inf_bot
    rw [← c.conj_g, hT, inf_idem] at h
    exact h
  have h8 := hyp.card8
  rw [hbot, Subgroup.card_bot] at h8
  omega

theorem T1ConfigA8.collapse_ne_wrong (hyp : A8CtxHyp T T₁)
    (c : T1ConfigA8 T T₁) (k : Fin 7) :
    c.g * c.gens 1 * c.g * (c.gens 1)⁻¹ * c.g ≠ evalA8 c.gens (wrongWordA8 k) := fun hw =>
  g_not_mem_normalizer hyp c (c.collapse_g_mem_normalizer k hw)

end Config

end CFSG.CGT.A8S
