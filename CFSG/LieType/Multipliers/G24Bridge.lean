module

public import CFSG.LieType.Multipliers.G24Check
public import CFSG.Quasithin.Background.G2UAdjoint
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import Certificates.Certificate9130

public section

namespace CFSG.LieType.Multipliers.G24

open Subgroup CFSG.CosetTable CFSG.Fischer CFSG.Quasithin.G2U CFSG.Blueprint.Chevalley

theorem finite_card_PG_congr {m k : ℕ} (h : m = k) {ws : List (List (Fin m × Bool))}
    {ws' : List (List (Fin k × Bool))}
    (hw : ws.map (List.map fun l => (l.1.val, l.2)) = ws'.map (List.map fun l => (l.1.val, l.2)))
    (hf : Finite (PG m ws)) : Finite (PG k ws') ∧ Nat.card (PG k ws') = Nat.card (PG m ws) := by
  subst h
  have hinj : Function.Injective fun l : Fin m × Bool => (l.1.val, l.2) := by
    rintro ⟨a, s⟩ ⟨a', s'⟩ e
    simp only [Prod.mk.injEq] at e
    rw [Fin.ext e.1, e.2]
  obtain rfl : ws = ws' := List.map_injective_iff.2 (List.map_injective_iff.2 hinj) hw
  exact ⟨hf, rfl⟩

theorem card_PG_R1_le :
    Finite (PG _ CFSG.Sporadic.Presentation.Suz.R1) ∧
      Nat.card (PG _ CFSG.Sporadic.Presentation.Suz.R1) ≤ 251596800 :=
  Certificates.certificate9130.2

@[expose] def genMat (i : Fin 6) : Matrix (Fin 14) (Fin 14) F4 := toMat 14 (genArr i)

theorem toMat_one14 : toMat 14 one14 = 1 :=
  toMat_ofMat 1

section Model

theorem genMat_mul_self (i : Fin 6) : genMat i * genMat i = 1 := by
  have h := inv_check
  rw [invCheck, List.all_eq_true] at h
  rw [genMat, ← toMat_mulArr, of_decide_eq_true (h i (List.mem_finRange i)), toMat_one14]

@[expose] def genGL (i : Fin 6) : GL (Fin 14) F4 :=
  ⟨genMat i, genMat i, genMat_mul_self i, genMat_mul_self i⟩

theorem val_lift_genGL (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift genGL (FreeGroup.mk w) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) =
      toMat 14 (wordArr w) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => exact toMat_one14.symm
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih]
    change _ = toMat 14 (mulArr 14 (genArr l.1) (wordArr w))
    rw [toMat_mulArr]
    congr 1
    obtain ⟨i, s⟩ := l
    cases s <;> rfl

@[expose] def grp : Subgroup (GL (Fin 14) F4) :=
  closure (Set.range genGL)

@[expose] def gen (i : Fin 6) : grp :=
  ⟨genGL i, subset_closure ⟨i, rfl⟩⟩

theorem coe_lift_gen (x : FreeGroup (Fin 6)) :
    ((FreeGroup.lift gen x : grp) : GL (Fin 14) F4) = FreeGroup.lift genGL x := by
  have h : grp.subtype.comp (FreeGroup.lift gen) = FreeGroup.lift genGL :=
    FreeGroup.ext_hom _ _ fun i => by simp [gen]
  exact DFunLike.congr_fun h x

theorem lift_gen_eq_one {w : List (Fin 6 × Bool)} (h : wordArr w = one14) :
    FreeGroup.lift gen (FreeGroup.mk w) = 1 := by
  apply Subtype.ext
  rw [coe_lift_gen, OneMemClass.coe_one]
  exact Units.ext (by rw [val_lift_genGL, h, toMat_one14]; rfl)

theorem lift_gen_rels : ∀ r ∈ wordSet rels, FreeGroup.lift gen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have h := rel_check
  rw [relCheck, List.all_eq_true] at h
  exact lift_gen_eq_one (of_decide_eq_true (h w hw))

theorem closure_range_gen : closure (Set.range gen) = ⊤ := by
  have h : Set.range gen = ((↑) : grp → GL (Fin 14) F4) ⁻¹' Set.range genGL := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  rw [h]
  exact closure_closure_coe_preimage

theorem map_adjointGroup_le {K : Type} [Field K] (σ : K ≃+* F4) :
    (adjointGroup .G2 K).map (glHom σ) ≤ grp := by
  have hmem : ∀ w : List (Fin 6 × Bool), FreeGroup.lift genGL (FreeGroup.mk w) ∈ grp := by
    intro w
    rw [grp, ← FreeGroup.range_lift_eq_closure]
    exact ⟨_, rfl⟩
  have hr := root_check
  rw [rootCheck, List.all_eq_true] at hr
  rw [adjointGroup, MonoidHom.map_closure, closure_le]
  rintro _ ⟨g, ⟨i, c, h⟩, rfl⟩
  have hic := List.all_eq_true.mp (hr i (List.mem_finRange i)) (σ c) (mem_allF4 _)
  rw [Bool.and_eq_true] at hic
  rw [SetLike.mem_coe]
  rcases h with h | h
  · have e : glHom σ g = FreeGroup.lift genGL (FreeGroup.mk (genWordX i (σ c))) := by
      refine Units.ext ?_
      rw [glHom_apply, coe_glEquiv, h, endEquiv_xOp, val_lift_genGL, ← of_decide_eq_true hic.1,
        toMat_ofMat]
    rw [e]
    exact hmem _
  · have e : glHom σ g = FreeGroup.lift genGL (FreeGroup.mk (genWordY i (σ c))) := by
      refine Units.ext ?_
      rw [glHom_apply, coe_glEquiv, h, endEquiv_yOp, val_lift_genGL, ← of_decide_eq_true hic.2,
        toMat_ofMat]
    rw [e]
    exact hmem _

end Model

section Order

theorem card_PG_rels_le : Finite (PG 6 rels) ∧ Nat.card (PG 6 rels) ≤ 251596800 := by
  obtain ⟨hf, hc⟩ := card_PG_R1_le
  have hw := suz_check
  rw [suzCheck, Bool.and_eq_true] at hw
  obtain ⟨hf', hc'⟩ :=
    finite_card_PG_congr (of_decide_eq_true hw.1) (of_decide_eq_true hw.2) hf
  exact ⟨hf', hc'.trans_le hc⟩

theorem card_grp_le : Nat.card grp ≤ 251596800 := by
  obtain ⟨hf, hc⟩ := card_PG_rels_le
  have hs : Function.Surjective (PresentedGroup.toGroup lift_gen_rels) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_gen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  exact (Nat.card_le_card_of_surjective _ hs).trans hc

end Order

section Adjoint

variable {K : Type} [Field K]

theorem card_adjointGroup (hK : Nat.card K = 4) : Nat.card (adjointGroup .G2 K) = 251596800 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  rfl

theorem map_adjointGroup_eq (σ : K ≃+* F4) (hK : Nat.card K = 4) :
    (adjointGroup .G2 K).map (glHom σ) = grp := by
  refine eq_of_le_of_card_ge (map_adjointGroup_le σ) ?_
  rw [← Nat.card_congr ((adjointGroup .G2 K).equivMapOfInjective _ (glHom_injective σ)).toEquiv,
    card_adjointGroup hK]
  exact card_grp_le

noncomputable def adjointEquiv (σ : K ≃+* F4) (hK : Nat.card K = 4) :
    ↥(adjointGroup .G2 K) ≃* grp :=
  ((adjointGroup .G2 K).equivMapOfInjective _ (glHom_injective σ)).trans
    (MulEquiv.subgroupCongr (map_adjointGroup_eq σ hK))

theorem card_grp : Nat.card grp = 251596800 := by
  have hF : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  rw [← Nat.card_congr (adjointEquiv (RingEquiv.refl F4) hF).toEquiv, card_adjointGroup hF]

theorem isPresentation : IsPresentation gen (wordSet rels) := by
  obtain ⟨hf, hc⟩ := card_PG_rels_le
  exact IsPresentation.of_card_le lift_gen_rels closure_range_gen (hc.trans card_grp.ge)

end Adjoint

end CFSG.LieType.Multipliers.G24
