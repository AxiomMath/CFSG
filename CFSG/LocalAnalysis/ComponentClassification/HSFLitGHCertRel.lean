module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDSkeleton

public section

namespace CFSG.ComponentClassification.HSFLit.GHCert

variable {G H : Type*} [Group G] [Group H] {z l α₁ α₂ α₃ α₄ x y a : G}

theorem ghRel_of_lift_eq_one
    (h : ∀ r ∈ ghWords, FreeGroup.lift (ghFam z l α₁ α₂ α₃ α₄ x y a) (FreeGroup.mk r) = 1) :
    GHRel z l α₁ α₂ α₃ α₄ x y a := by
  simp only [ghWords, List.forall_mem_cons, FreeGroup.lift_mk, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Bool.cond_true, Bool.cond_false, ghFam, mul_one] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44, h45, -⟩ := h
  constructor
  all_goals (rw [← mul_inv_eq_one]; simp only [mul_assoc, pow_two, mul_inv_rev, inv_one, mul_one])
  exacts [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44, h45]

theorem ghRel_map {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (h : GHRel z l α₁ α₂ α₃ α₄ x y a) :
    GHRel (f z) (f l) (f α₁) (f α₂) (f α₃) (f α₄) (f x) (f y) (f a) := by
  refine ghRel_of_lift_eq_one fun r hr => ?_
  have e : ghFam (f z) (f l) (f α₁) (f α₂) (f α₃) (f α₄) (f x) (f y) (f a) =
      (f : G →* H) ∘ ghFam z l α₁ α₂ α₃ α₄ x y a := by
    funext i
    fin_cases i <;> simp [ghFam]
  have hc : FreeGroup.lift ((f : G →* H) ∘ ghFam z l α₁ α₂ α₃ α₄ x y a) =
      (f : G →* H).comp (FreeGroup.lift (ghFam z l α₁ α₂ α₃ α₄ x y a)) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  rw [e, hc, MonoidHom.comp_apply, h.lift_eq_one _ (List.mem_map_of_mem hr), map_one]

theorem ghRel_card_closure_le (hB : GHPresentationBound) (h : GHRel z l α₁ α₂ α₃ α₄ x y a) :
    Nat.card (Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set G)) ≤ 512 := by
  obtain ⟨hfin, hle⟩ := hB
  rw [← h.range_hom]
  exact (Nat.card_le_card_of_surjective _ h.hom.rangeRestrict_surjective).trans hle

theorem card_closure_image (e : G ≃* H) (s : Set G) :
    Nat.card (Subgroup.closure (e '' s)) = Nat.card (Subgroup.closure s) := by
  have h := MonoidHom.map_closure e.toMonoidHom s
  rw [MulEquiv.coe_toMonoidHom] at h
  rw [← h, Subgroup.card_map_of_injective e.injective]

end CFSG.ComponentClassification.HSFLit.GHCert
