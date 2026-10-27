module

public import CFSG.CGT.A8S.L2Sub

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] def evS (pos neg : Fin 5 → ℕ) : List (Fin 5 × Bool) → ℕ
  | [] => 2184
  | l :: w => cmul (if l.2 then pos l.1 else neg l.1) (evS pos neg w)

theorem avc_lift (f : Fin 5 → PG 5 relsN0A8)
    {pos neg : Fin 5 → ℕ} (hp : ∀ i, avc (f i) = pos i) (hn : ∀ i, avc (f i)⁻¹ = neg i)
    (w : List (Fin 5 × Bool)) : avc (FreeGroup.lift f (FreeGroup.mk w)) = evS pos neg w := by
  induction w with
  | nil => exact avc_one
  | cons l w ih =>
    rw [lift_mk_cons, avc_mul, ih]
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [Bool.cond_false, evS, Bool.false_eq_true, ↓reduceIte, hn]
    · simp only [Bool.cond_true, evS, ↓reduceIte, hp]

@[expose] def alphaW (i : Fin 5) : List (Fin 5 × Bool) :=
  if i = 0 then [(0, true), (3, true)] else [(i, true)]

@[expose] def alphaInvW (i : Fin 5) : List (Fin 5 × Bool) :=
  if i = 0 then [(3, false), (0, false)] else [(i, false)]

abbrev alphaImg (i : Fin 5) : PG 5 relsN0A8 := mkW (alphaW i)

theorem alphaImg_inv (i : Fin 5) : (alphaImg i)⁻¹ = mkW (alphaInvW i) := by
  rw [alphaImg, mkW, ← map_inv, FreeGroup.inv_mk]
  congr 2
  fin_cases i <;> rfl

theorem alpha_rels_check : ∀ r ∈ relsN0A8,
    evS (fun i => affCode (affEval (alphaW i))) (fun i => affCode (affEval (alphaInvW i))) r =
      2184 := by
  decide +kernel

theorem alphaImg_rels :
    ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ relsN0A8.map FreeGroup.mk},
      FreeGroup.lift alphaImg r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  apply avc_inj
  rw [avc_lift alphaImg (fun i => avc_mk (alphaW i))
    (fun i => by rw [alphaImg_inv, avc_mk]), avc_one]
  exact alpha_rels_check w hw

@[expose] noncomputable def alphaHom :
    PG 5 relsN0A8 →* PG 5 relsN0A8 :=
  PresentedGroup.toGroup alphaImg_rels

theorem alphaHom_of (i : Fin 5) :
    alphaHom (PresentedGroup.of i) = alphaImg i :=
  PresentedGroup.toGroup.of _

theorem alphaHom_alphaImg (i : Fin 5) :
    alphaHom (alphaImg i) = PresentedGroup.of i := by
  by_cases h : i = 0
  · subst h
    have e : alphaImg 0 = PresentedGroup.of 0 * PresentedGroup.of 3 := rfl
    rw [e, map_mul, alphaHom_of, alphaHom_of]
    apply avc_inj
    rw [avc_mul, avc_mk, avc_mk, ← mkW_single, avc_mk]
    decide +kernel
  · have e : alphaImg i = PresentedGroup.of i := by
      simp only [alphaImg, alphaW, h, ↓reduceIte]
      rfl
    rw [e, alphaHom_of, e]

theorem alphaHom_alphaHom (x : PG 5 relsN0A8) :
    alphaHom (alphaHom x) = x := by
  have h : alphaHom.comp alphaHom = MonoidHom.id (PG 5 relsN0A8) :=
    PresentedGroup.ext fun i => by
      rw [MonoidHom.comp_apply, alphaHom_of, alphaHom_alphaImg, MonoidHom.id_apply]
  exact DFunLike.congr_fun h x

@[expose] noncomputable def alphaA8 :
    PG 5 relsN0A8 ≃* PG 5 relsN0A8 where
  toFun := alphaHom
  invFun := alphaHom
  left_inv := alphaHom_alphaHom
  right_inv := alphaHom_alphaHom
  map_mul' := map_mul alphaHom

theorem alphaA8_apply (x : PG 5 relsN0A8) :
    alphaA8 x = alphaHom x :=
  rfl

theorem alphaA8_alphaA8 (x : PG 5 relsN0A8) :
    alphaA8 (alphaA8 x) = x :=
  alphaHom_alphaHom x

theorem alphaA8_tGen (j : Fin 3) :
    alphaA8 (tGenA8 j) = tGenA8 j := by
  rw [alphaA8_apply, tGenA8, alphaHom_of]
  fin_cases j <;> rfl

theorem alphaA8_mem_T0 {x : PG 5 relsN0A8} (hx : x ∈ T0) :
    alphaA8 x ∈ T0 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [alphaA8_tGen]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  | one => rw [map_one]; exact T0.one_mem
  | mul y z _ _ hy hz => rw [map_mul]; exact T0.mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact T0.inv_mem hy

theorem mem_T0_iff_alpha (x : PG 5 relsN0A8) :
    x ∈ T0 ↔ alphaA8 x ∈ T0 :=
  ⟨alphaA8_mem_T0, fun h => by simpa [alphaA8_alphaA8] using alphaA8_mem_T0 h⟩

theorem alphaA8_b0 :
    alphaA8 b0 = PresentedGroup.of 0 := by
  rw [alphaA8_apply]
  exact alphaHom_alphaImg 0

end CFSG.CGT.A8S.L2
