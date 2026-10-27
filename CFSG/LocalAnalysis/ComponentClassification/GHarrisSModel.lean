module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSylow

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup HSFLit SCert

namespace SCert.SE

theorem ghRel_gen : GHRel (gen 0) (gen 1) (gen 2) (gen 3) (gen 4) (gen 5) (gen 6) (gen 7)
    (gen 8) := by
  constructor <;> decide

@[expose] def tr (u0 u1 u2 : ZMod 4) : SE := ⟨0, u0, u1, u2⟩

@[expose] def rep : Fin 8 → SE :=
  ![1, gen 6, gen 4, gen 5, gen 8, gen 6 * gen 8, gen 4 * gen 8, gen 5 * gen 8]

theorem eq_tr_mul_rep : ∀ (d : Fin 8) (v0 v1 v2 : ZMod 4),
    (⟨d, v0, v1, v2⟩ : SE) = tr (v0 - (rep d).v0) (v1 - (rep d).v1) (v2 - (rep d).v2) * rep d := by
  decide

theorem tr_eq : ∀ u0 u1 u2 : ZMod 4,
    tr u0 u1 u2 = gen 1 ^ u0.val * (gen 6 * gen 4 * gen 5) ^ u1.val * (gen 7 * gen 5) ^ u2.val := by
  decide

theorem closure_range_gen : closure (Set.range gen) = ⊤ := by
  have hg : ∀ i, gen i ∈ closure (Set.range gen) := fun i => subset_closure ⟨i, rfl⟩
  have htr : ∀ u0 u1 u2 : ZMod 4, tr u0 u1 u2 ∈ closure (Set.range gen) := fun u0 u1 u2 => by
    rw [tr_eq]
    exact mul_mem (mul_mem (pow_mem (hg 1) _) (pow_mem (mul_mem (mul_mem (hg 6) (hg 4)) (hg 5)) _))
      (pow_mem (mul_mem (hg 7) (hg 5)) _)
  have hrep : ∀ d, rep d ∈ closure (Set.range gen) := by
    intro d
    fin_cases d
    · exact one_mem _
    · exact hg 6
    · exact hg 4
    · exact hg 5
    · exact hg 8
    · exact mul_mem (hg 6) (hg 8)
    · exact mul_mem (hg 4) (hg 8)
    · exact mul_mem (hg 5) (hg 8)
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨d, v0, v1, v2⟩ := s
  rw [eq_tr_mul_rep]
  exact mul_mem (htr _ _ _) (hrep d)

theorem card_SE : Nat.card SE = 512 := by
  rw [Nat.card_congr equivProd]
  simp [ZMod.card]

end SCert.SE

theorem range_ghFam_gen : Set.range (ghFam (SE.gen 0) (SE.gen 1) (SE.gen 2) (SE.gen 3)
    (SE.gen 4) (SE.gen 5) (SE.gen 6) (SE.gen 7) (SE.gen 8)) = Set.range SE.gen := by
  congr 1
  funext i
  fin_cases i <;> rfl

theorem range_hom_gen : SE.ghRel_gen.hom.range = ⊤ := by
  rw [GHRel.range_hom, ← range_ghFam, range_ghFam_gen, SE.closure_range_gen]

theorem bijective_hom_gen : Function.Bijective SE.ghRel_gen.hom := by
  obtain ⟨hfin, hle⟩ := ghPresentationBound
  have hsurj : Function.Surjective SE.ghRel_gen.hom :=
    MonoidHom.range_eq_top.mp range_hom_gen
  exact hsurj.bijective_of_nat_card_le (by rw [SE.card_SE]; exact hle)

noncomputable def equivSE : GHGroup ≃* SE :=
  MulEquiv.ofBijective SE.ghRel_gen.hom bijective_hom_gen

theorem equivSE_ghGen (i : Fin 9) :
    equivSE (ghGen i) = SE.gen i := by
  change SE.ghRel_gen.hom (PresentedGroup.of i) = SE.gen i
  rw [GHRel.hom, PresentedGroup.toGroup.of]
  fin_cases i <;> rfl

theorem equivSE_symm_gen (i : Fin 9) :
    equivSE.symm (SE.gen i) = ghGen i := by
  rw [MulEquiv.symm_apply_eq, equivSE_ghGen]

namespace GHSylow

variable {G : Type} [Group G] (D : GHSylow G)

@[expose] noncomputable def toG : SE →* G :=
  D.emb.comp equivSE.symm.toMonoidHom

theorem toG_injective : Function.Injective D.toG :=
  D.emb_injective.comp equivSE.symm.injective

theorem range_toG : D.toG.range = D.S := by
  rw [toG, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr equivSE.symm.surjective,
    ← MonoidHom.range_eq_map, range_emb]

theorem toG_mem (s : SE) : D.toG s ∈ (D.S : Subgroup G) := by
  rw [← D.range_toG]
  exact ⟨s, rfl⟩

theorem exists_toG {g : G} (hg : g ∈ (D.S : Subgroup G)) :
    ∃ s : SE, D.toG s = g := by
  rw [← D.range_toG] at hg
  exact hg

end GHSylow

end CFSG.ComponentClassification.GHarris
