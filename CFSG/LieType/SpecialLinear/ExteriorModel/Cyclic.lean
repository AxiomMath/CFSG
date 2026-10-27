module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Basic.Sign.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix
open scoped Matrix

variable {k : Type*} [Field k] {I : Type*} [Fintype I] {β : Type*}

@[expose] def cyclicSub (D : β → Matrix I I k) (v : I → k) : Submodule k (I → k) :=
  sInf {N | v ∈ N ∧ ∀ b, ∀ w ∈ N, D b *ᵥ w ∈ N}

theorem mem_cyclicSub_self (D : β → Matrix I I k) (v : I → k) : v ∈ cyclicSub D v := by
  exact Submodule.mem_sInf.2 fun N hN => hN.1

theorem mulVec_mem_cyclicSub {D : β → Matrix I I k} {v w : I → k} (b : β)
    (hw : w ∈ cyclicSub D v) : D b *ᵥ w ∈ cyclicSub D v := by
  exact Submodule.mem_sInf.2 fun N hN => hN.2 b w (Submodule.mem_sInf.1 hw N hN)

theorem cyclicSub_le {D : β → Matrix I I k} {v : I → k} {N : Submodule k (I → k)} (hv : v ∈ N)
    (hN : ∀ b, ∀ w ∈ N, D b *ᵥ w ∈ N) : cyclicSub D v ≤ N :=
  sInf_le ⟨hv, hN⟩

theorem mulVec_mem_cyclicSub_of_mem_span {D : β → Matrix I I k} {v w : I → k} {X : Matrix I I k}
    (hX : X ∈ Submodule.span k (Set.range D)) (hw : w ∈ cyclicSub D v) : X *ᵥ w ∈ cyclicSub D v := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨b, rfl⟩ := hX
      exact mulVec_mem_cyclicSub b hw
  | zero => simp
  | add X Y _ _ hX hY => rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hX hY
  | smul a X _ hX => rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ a hX

theorem mulVec_mem_cyclicSub_of_conj {D : β → Matrix I I k} {v : I → k} {g : Matrix I I k}
    (hgv : g *ᵥ v ∈ cyclicSub D v)
    (hg : ∀ b, ∃ X ∈ Submodule.span k (Set.range D), g * D b = X * g) {w : I → k}
    (hw : w ∈ cyclicSub D v) : g *ᵥ w ∈ cyclicSub D v := by
  let N : Submodule k (I → k) := (cyclicSub D v).comap g.mulVecLin
  have hN : v ∈ N := hgv
  have hstab : ∀ b, ∀ w ∈ N, D b *ᵥ w ∈ N := by
    intro b w hw
    obtain ⟨X, hX, hgX⟩ := hg b
    change g *ᵥ (D b *ᵥ w) ∈ cyclicSub D v
    rw [Matrix.mulVec_mulVec, hgX, ← Matrix.mulVec_mulVec]
    exact mulVec_mem_cyclicSub_of_mem_span hX hw
  exact cyclicSub_le hN hstab hw

@[expose] def dotRad (C : Submodule k (I → k)) : Submodule k (I → k) where
  carrier := {x | x ∈ C ∧ ∀ y ∈ C, x ⬝ᵥ y = 0}
  add_mem' := by
    rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
    refine ⟨Submodule.add_mem _ hxC hyC, fun z hz => ?_⟩
    rw [add_dotProduct, hx z hz, hy z hz, add_zero]
  zero_mem' := ⟨Submodule.zero_mem _, fun y _ => by simp⟩
  smul_mem' := by
    rintro a x ⟨hxC, hx⟩
    refine ⟨Submodule.smul_mem _ a hxC, fun z hz => ?_⟩
    rw [smul_dotProduct, hx z hz, smul_zero]

theorem mem_dotRad {C : Submodule k (I → k)} {x : I → k} :
    x ∈ dotRad C ↔ x ∈ C ∧ ∀ y ∈ C, x ⬝ᵥ y = 0 :=
  Iff.rfl

theorem mulVec_mem_dotRad {C : Submodule k (I → k)} {g : Matrix I I k}
    (hg : ∀ y ∈ C, g *ᵥ y ∈ C) (hgT : ∀ y ∈ C, gᵀ *ᵥ y ∈ C) {x : I → k}
    (hx : x ∈ dotRad C) : g *ᵥ x ∈ dotRad C := by
  refine mem_dotRad.mpr ⟨hg x hx.1, fun y hy => ?_⟩
  calc (g *ᵥ x) ⬝ᵥ y = y ⬝ᵥ (g *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (gᵀ *ᵥ y) := (Matrix.dotProduct_transpose_mulVec g x y).symm
    _ = 0 := hx.2 _ (hgT y hy)

@[expose] def cyclicFiltration (D : β → Matrix I I k) (v : I → k) : ℕ → Submodule k (I → k)
  | 0 => k ∙ v
  | m + 1 => cyclicFiltration D v m ⊔ ⨆ b : β, (cyclicFiltration D v m).map (D b).mulVecLin

@[simp] theorem cyclicFiltration_zero (D : β → Matrix I I k) (v : I → k) :
    cyclicFiltration D v 0 = k ∙ v := rfl

@[simp] theorem cyclicFiltration_succ (D : β → Matrix I I k) (v : I → k) (m : ℕ) :
    cyclicFiltration D v (m + 1) =
      cyclicFiltration D v m ⊔ ⨆ b : β, (cyclicFiltration D v m).map (D b).mulVecLin := rfl

theorem cyclicFiltration_mono (D : β → Matrix I I k) (v : I → k) :
    Monotone (cyclicFiltration D v) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem cyclicFiltration_le_cyclicSub (D : β → Matrix I I k) (v : I → k) (m : ℕ) :
    cyclicFiltration D v m ≤ cyclicSub D v := by
  induction m with
  | zero =>
      rw [cyclicFiltration_zero]
      exact Submodule.span_le.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact mem_cyclicSub_self D v
  | succ m ih =>
      rw [cyclicFiltration_succ]
      refine sup_le ih ?_
      refine iSup_le fun b => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      exact mulVec_mem_cyclicSub b (ih hx)

theorem cyclicSub_le_iSup_cyclicFiltration (D : β → Matrix I I k) (v : I → k) :
    cyclicSub D v ≤ ⨆ m, cyclicFiltration D v m := by
  refine cyclicSub_le ?_ ?_
  · exact Submodule.mem_iSup_of_mem 0 (by
      rw [cyclicFiltration_zero]
      exact Submodule.mem_span_singleton_self v)
  · intro b w hw
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed (cyclicFiltration D v)
      (cyclicFiltration_mono D v).directed_le).1 hw
    exact Submodule.mem_iSup_of_mem (m + 1) (by
      rw [cyclicFiltration_succ]
      exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem b (Submodule.mem_map_of_mem hm)))

theorem cyclicSub_eq_sup_neg {D : β → Matrix I I k} {v : I → k} (sgn : β → SignType)
    (hlie : ∀ a b, D a * D b - D b * D a ∈ Submodule.span k (Set.range D))
    (hpos : ∀ b, sgn b = 1 → D b *ᵥ v = 0)
    (hzero : ∀ b, sgn b = 0 → ∃ c : k, D b *ᵥ v = c • v) :
    cyclicSub D v = (k ∙ v) ⊔ ⨆ (b : β) (_ : sgn b = -1), (cyclicSub D v).map (D b).mulVecLin := by
  let P : ℕ → Submodule k (I → k) := fun m =>
    (k ∙ v) ⊔ ⨆ (b : β) (_ : sgn b = -1),
      (cyclicFiltration D v m).map (D b).mulVecLin
  let Pfin : Submodule k (I → k) :=
    (k ∙ v) ⊔ ⨆ (b : β) (_ : sgn b = -1), (cyclicSub D v).map (D b).mulVecLin
  have hPmono : Monotone P := by
    intro m n hmn
    refine sup_le le_sup_left ?_
    refine iSup_le fun b => iSup_le fun hb => ?_
    exact (le_iSup_of_le b (le_iSup_of_le hb
      (Submodule.map_mono (cyclicFiltration_mono D v hmn)))).trans le_sup_right
  have hDv : ∀ b, D b *ᵥ v ∈ P 0 := by
    intro b
    cases hb : sgn b with
    | zero =>
        obtain ⟨c, hc⟩ := hzero b hb
        rw [hc]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    | neg =>
        refine Submodule.mem_sup_right ?_
        refine Submodule.mem_iSup_of_mem b ?_
        refine Submodule.mem_iSup_of_mem hb ?_
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
    | pos =>
        rw [hpos b hb]
        exact Submodule.zero_mem _
  have hstep : ∀ m, cyclicFiltration D v (m + 1) ≤ P m := by
    intro m
    induction m with
    | zero =>
        rw [cyclicFiltration_succ, cyclicFiltration_zero]
        refine sup_le le_sup_left ?_
        refine iSup_le fun b => ?_
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact hDv b
    | succ m ih =>
        rw [cyclicFiltration_succ]
        refine sup_le ?_ ?_
        · exact ih.trans (hPmono (Nat.le_succ m))
        · refine iSup_le fun b => ?_
          rw [Submodule.map_le_iff_le_comap]
          refine ih.trans ?_
          refine sup_le ?_ ?_
          · rw [Submodule.span_le]
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            subst x
            exact hPmono (Nat.zero_le (m + 1)) (hDv b)
          · refine iSup_le fun b' => iSup_le fun hb' => ?_
            rw [Submodule.map_le_iff_le_comap]
            intro y hy
            have hDy : D b *ᵥ y ∈ cyclicFiltration D v (m + 1) := by
              rw [cyclicFiltration_succ]
              exact Submodule.mem_sup_right
                (Submodule.mem_iSup_of_mem b (Submodule.mem_map_of_mem hy))
            have hfirst : D b' *ᵥ (D b *ᵥ y) ∈ P (m + 1) := by
              refine Submodule.mem_sup_right ?_
              refine Submodule.mem_iSup_of_mem b' ?_
              refine Submodule.mem_iSup_of_mem hb' ?_
              exact Submodule.mem_map_of_mem hDy
            have hspan : ∀ X ∈ Submodule.span k (Set.range D),
                X *ᵥ y ∈ cyclicFiltration D v (m + 1) := by
              intro X hX
              refine Submodule.span_induction (p := fun X _ =>
                X *ᵥ y ∈ cyclicFiltration D v (m + 1)) ?_ ?_ ?_ ?_ hX
              · rintro X ⟨c, rfl⟩
                rw [cyclicFiltration_succ]
                exact Submodule.mem_sup_right
                  (Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem hy))
              · rw [Matrix.zero_mulVec]
                exact Submodule.zero_mem _
              · intro X Y _ _ hX hY
                rw [Matrix.add_mulVec]
                exact Submodule.add_mem _ hX hY
              · intro a X _ hX
                rw [Matrix.smul_mulVec]
                exact Submodule.smul_mem _ a hX
            have hbr : (D b * D b' - D b' * D b) *ᵥ y ∈ P (m + 1) :=
              hPmono (Nat.le_succ m) (ih (hspan _ (hlie b b')))
            have hcomm : D b *ᵥ (D b' *ᵥ y) =
                D b' *ᵥ (D b *ᵥ y) + (D b * D b' - D b' * D b) *ᵥ y := by
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.sub_mulVec]
              abel
            change D b *ᵥ (D b' *ᵥ y) ∈ P (m + 1)
            rw [hcomm]
            exact Submodule.add_mem _ hfirst hbr
  have hWle : ∀ m, cyclicFiltration D v m ≤ Pfin := by
    intro m
    cases m with
    | zero =>
        rw [cyclicFiltration_zero]
        exact le_sup_left
    | succ m =>
        refine (hstep m).trans ?_
        refine sup_le le_sup_left ?_
        refine iSup_le fun b => iSup_le fun hb => ?_
        exact (le_iSup_of_le b (le_iSup_of_le hb
          (Submodule.map_mono (cyclicFiltration_le_cyclicSub D v m)))).trans le_sup_right
  refine le_antisymm ?_ ?_
  · exact (cyclicSub_le_iSup_cyclicFiltration D v).trans (iSup_le hWle)
  · refine sup_le ?_ ?_
    · exact Submodule.span_le.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact mem_cyclicSub_self D v
    · refine iSup_le fun b => iSup_le fun hb => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      exact mulVec_mem_cyclicSub b hx

theorem sub_smul_mem_dotRad {D : β → Matrix I I k} {v w : I → k} (sgn : β → SignType)
    (op : β → β) (hsgn : ∀ b, sgn (op b) = -sgn b) (htr : ∀ b, (D b)ᵀ = D (op b))
    (hlie : ∀ a b, D a * D b - D b * D a ∈ Submodule.span k (Set.range D))
    (hpos : ∀ b, sgn b = 1 → D b *ᵥ v = 0)
    (hzero : ∀ b, sgn b = 0 → ∃ c : k, D b *ᵥ v = c • v) (hv : v ⬝ᵥ v = 1)
    (hw : w ∈ cyclicSub D v) (hwpos : ∀ b, sgn b = 1 → D b *ᵥ w ∈ dotRad (cyclicSub D v)) :
    w - (w ⬝ᵥ v) • v ∈ dotRad (cyclicSub D v) := by
  let C : Submodule k (I → k) := cyclicSub D v
  let x : I → k := w - (w ⬝ᵥ v) • v
  have hx_mem : x ∈ C :=
    Submodule.sub_mem C hw (Submodule.smul_mem C (w ⬝ᵥ v) (mem_cyclicSub_self D v))
  have hx_v : x ⬝ᵥ v = 0 := by
    rw [sub_dotProduct, smul_dotProduct, hv, smul_eq_mul, mul_one, sub_self]
  let K : Submodule k (I → k) :=
    { carrier := {y | x ⬝ᵥ y = 0}
      add_mem' := by
        rintro y z hy hz
        change x ⬝ᵥ (y + z) = 0
        rw [dotProduct_add, hy, hz, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        rintro a y hy
        change x ⬝ᵥ (a • y) = 0
        rw [dotProduct_smul, hy, smul_zero] }
  have hK : (k ∙ v) ⊔ ⨆ (b : β) (_ : sgn b = -1),
      C.map (D b).mulVecLin ≤ K := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx_v
    · refine iSup_le fun b => iSup_le fun hb => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro y hy
      have hop : sgn (op b) = 1 := by
        rw [hsgn b, hb]
        rfl
      have hDv : D (op b) *ᵥ v = 0 := hpos (op b) hop
      have hDw : D (op b) *ᵥ w ∈ dotRad C := hwpos (op b) hop
      have hDx : D (op b) *ᵥ x = D (op b) *ᵥ w := by
        change D (op b) *ᵥ (w - (w ⬝ᵥ v) • v) = D (op b) *ᵥ w
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hDv, smul_zero, sub_zero]
      have hdot : x ⬝ᵥ (D b *ᵥ y) = (D (op b) *ᵥ x) ⬝ᵥ y := by
        rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, htr b]
      change x ⬝ᵥ (D b *ᵥ y) = 0
      rw [hdot, hDx]
      exact (mem_dotRad.mp hDw).2 y hy
  refine mem_dotRad.mpr ⟨hx_mem, fun y hy => ?_⟩
  have hyP : y ∈ (k ∙ v) ⊔ ⨆ (b : β) (_ : sgn b = -1), C.map (D b).mulVecLin := by
    rw [← cyclicSub_eq_sup_neg sgn hlie hpos hzero]
    exact hy
  exact hK hyP

@[expose] def homComp {Γ : Type*} [DecidableEq Γ] (deg : I → Γ) (e : Γ) (w : I → k) : I → k :=
  fun i => if deg i = e then w i else 0

@[expose] def homCompLin {Γ : Type*} [DecidableEq Γ] (deg : I → Γ) (e : Γ) : (I → k) →ₗ[k] (I → k) where
  toFun := homComp deg e
  map_add' := by
    intro x y
    funext i
    simp only [homComp, Pi.add_apply]
    split <;> simp
  map_smul' := by
    intro a x
    funext i
    simp only [homComp, Pi.smul_apply]
    split <;> simp

omit [Fintype I] in
@[simp] theorem homCompLin_apply {Γ : Type*} [DecidableEq Γ] (deg : I → Γ) (e : Γ) (w : I → k) :
    homCompLin deg e w = homComp deg e w :=
  rfl

theorem dotProduct_homComp {Γ : Type*} [DecidableEq Γ] (deg : I → Γ) (e : Γ) (x y : I → k) :
    homComp deg e x ⬝ᵥ y = x ⬝ᵥ homComp deg e y := by
  simp only [dotProduct, homComp]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : deg i = e <;> simp [h]

theorem mulVec_homComp {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] (deg : I → Γ)
    {A : Matrix I I k} {δ : Γ} (hA : ∀ i j, A i j ≠ 0 → deg i = deg j + δ) (e : Γ)
    (w : I → k) : A *ᵥ homComp deg e w = homComp deg (e + δ) (A *ᵥ w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, homComp]
  by_cases hi : deg i = e + δ
  · rw [if_pos hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : A i j = 0
    · simp [hij]
    · have hd := hA i j hij
      have hje : deg j = e := add_right_cancel (hd.symm.trans hi)
      simp [hje]
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hje : deg j = e
    · have hzero : A i j = 0 := by
        by_contra hne
        exact hi ((hA i j hne).trans (by rw [hje]))
      simp [hje, hzero]
    · simp [hje]

theorem homComp_mem_cyclicSub {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ] (deg : I → Γ)
    {D : β → Matrix I I k} {v : I → k} (δ : β → Γ)
    (hD : ∀ b i j, D b i j ≠ 0 → deg i = deg j + δ b)
    {e₀ : Γ} (hv : ∀ i, v i ≠ 0 → deg i = e₀) {w : I → k} (hw : w ∈ cyclicSub D v)
    (e : Γ) : homComp deg e w ∈ cyclicSub D v := by
  let N : Submodule k (I → k) :=
    { carrier := {w | ∀ e, homComp deg e w ∈ cyclicSub D v}
      add_mem' := by
        intro x y hx hy e
        rw [show homComp deg e (x + y) =
          homComp deg e x + homComp deg e y from map_add (homCompLin deg e) x y]
        exact Submodule.add_mem _ (hx e) (hy e)
      zero_mem' := by
        intro e
        rw [show homComp deg e (0 : I → k) = 0 from map_zero (homCompLin deg e)]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro a x hx e
        rw [show homComp deg e (a • x) = a • homComp deg e x from map_smul (homCompLin deg e) a x]
        exact Submodule.smul_mem _ a (hx e) }
  have hvN : v ∈ N := by
    intro e
    by_cases he : e = e₀
    · subst e
      have hve : homComp deg e₀ v = v := by
        funext i
        by_cases hi : deg i = e₀
        · simp [homComp, hi]
        · have hvi : v i = 0 := by
            by_contra hne
            exact hi (hv i hne)
          simp [homComp, hi, hvi]
      rw [hve]
      exact mem_cyclicSub_self D v
    · have hve : homComp deg e v = 0 := by
        funext i
        by_cases hi : deg i = e
        · have hvi : v i = 0 := by
            by_contra hne
            exact he (hi.symm.trans (hv i hne))
          simp [homComp, hi, hvi]
        · simp [homComp, hi]
      rw [hve]
      exact Submodule.zero_mem _
  have hstab : ∀ b, ∀ w ∈ N, D b *ᵥ w ∈ N := by
    intro b w hw e
    have hb := mulVec_homComp (deg := deg) (A := D b) (δ := δ b) (hD b) (e := e - δ b) w
    have he : (e - δ b) + δ b = e := by abel
    rw [he] at hb
    rw [← hb]
    exact mulVec_mem_cyclicSub b (hw (e - δ b))
  have hwN : w ∈ N := cyclicSub_le hvN hstab hw
  exact hwN e

theorem homComp_mem_dotRad {Γ : Type*} [DecidableEq Γ] (deg : I → Γ)
    {C : Submodule k (I → k)} (hC : ∀ e, ∀ y ∈ C, homComp deg e y ∈ C) {x : I → k}
    (hx : x ∈ dotRad C) (e : Γ) : homComp deg e x ∈ dotRad C := by
  refine mem_dotRad.mpr ⟨hC e x hx.1, fun y hy => ?_⟩
  rw [dotProduct_homComp]
  exact hx.2 (homComp deg e y) (hC e y hy)

omit [Fintype I] in
theorem homComp_homComp {Γ : Type*} [DecidableEq Γ] (deg : I → Γ) (e e' : Γ) (w : I → k) :
    homComp deg e (homComp deg e' w) = if e = e' then homComp deg e w else 0 := by
  by_cases he : e = e'
  · subst e'
    rw [if_pos rfl]
    funext i
    by_cases hi : deg i = e <;> simp [homComp, hi]
  · rw [if_neg he]
    funext i
    by_cases hi : deg i = e
    · simp [homComp, hi, he]
    · simp [homComp, hi]

theorem mulVec_homComp_mem_dotRad [DecidableEq I] (deg : I → ℤ) {C : Submodule k (I → k)}
    (hC : ∀ e, ∀ y ∈ C, homComp deg e y ∈ C) {A A₁ A₂ : Matrix I I k} (hA : A = 1 + A₁ + A₂)
    (hAR : ∀ x ∈ dotRad C, A *ᵥ x ∈ dotRad C) {h : ℤ}
    (hA₁ : ∀ i j, A₁ i j ≠ 0 → deg i + h = deg j) (hA₂ : ∀ i j, A₂ i j ≠ 0 → deg i + h < deg j)
    {w : I → k} (hwA : A *ᵥ w - w ∈ dotRad C) (e : ℤ)
    (htop : ∀ e', e < e' → homComp deg e' w ∈ dotRad C) :
    A₁ *ᵥ homComp deg e w ∈ dotRad C := by
  let T : Finset ℤ := (Finset.univ.image deg).filter fun e' => e < e'
  let s : I → k := ∑ e' ∈ T, homComp deg e' w
  let t : I → k := w - s
  have hs : s ∈ dotRad C := by
    refine Submodule.sum_mem _ fun e' he' => ?_
    exact htop e' (Finset.mem_filter.mp he').2
  have hAs : A *ᵥ s ∈ dotRad C := by
    have hsum : A *ᵥ s = ∑ e' ∈ T, A *ᵥ homComp deg e' w := by
      change (Matrix.mulVecLin A) (∑ e' ∈ T, homComp deg e' w) = _
      rw [map_sum]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun e' he' => hAR _ (htop e' (Finset.mem_filter.mp he').2)
  have hAst : A *ᵥ s - s ∈ dotRad C := Submodule.sub_mem _ hAs hs
  have ht : A *ᵥ t - t ∈ dotRad C := by
    have heq : A *ᵥ t - t = (A *ᵥ w - w) - (A *ᵥ s - s) := by
      change A *ᵥ (w - s) - (w - s) = (A *ᵥ w - w) - (A *ᵥ s - s)
      rw [Matrix.mulVec_sub]
      abel
    rw [heq]
    exact Submodule.sub_mem _ hwA hAst
  have hsj : ∀ j, e < deg j → s j = w j := by
    intro j hj
    have hmem : deg j ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hj⟩
    have hs_eq : s = ∑ e' ∈ T, homComp deg e' w := rfl
    rw [hs_eq, Finset.sum_apply]
    rw [Finset.sum_eq_single (deg j)]
    · simp [homComp]
    · intro e' _ hne
      have hne' : deg j ≠ e' := fun h => hne h.symm
      simp [homComp, hne']
    · intro hnot
      exact absurd hmem hnot
  have ht_zero : ∀ j, e < deg j → t j = 0 := by
    intro j hj
    change w j - s j = 0
    rw [hsj j hj, sub_self]
  have hse : homComp deg e s = 0 := by
    change homCompLin deg e s = 0
    rw [show s = ∑ e' ∈ T, homComp deg e' w from rfl, map_sum]
    refine Finset.sum_eq_zero fun e' he' => ?_
    have hgt : e < e' := (Finset.mem_filter.mp he').2
    change homComp deg e (homComp deg e' w) = 0
    rw [homComp_homComp, if_neg (ne_of_lt hgt)]
  have hte : homComp deg e t = homComp deg e w := by
    change homCompLin deg e t = homCompLin deg e w
    rw [show t = w - s from rfl, map_sub]
    change homComp deg e w - homComp deg e s = homComp deg e w
    rw [hse, sub_zero]
  have hA₁' : ∀ i j, A₁ i j ≠ 0 → deg i = deg j + (-h) := by
    intro i j hij
    have := hA₁ i j hij
    linarith
  have hA₁comp : homComp deg (e - h) (A₁ *ᵥ t) = A₁ *ᵥ homComp deg e t := by
    have hb := mulVec_homComp (deg := deg) (A := A₁) (δ := -h) hA₁' (e := e) t
    have he : e + -h = e - h := by ring
    rw [he] at hb
    exact hb.symm
  have hA₂comp : homComp deg (e - h) (A₂ *ᵥ t) = 0 := by
    funext i
    change (if deg i = e - h then (A₂ *ᵥ t) i else 0) = 0
    by_cases hi : deg i = e - h
    · rw [if_pos hi]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hij : A₂ i j = 0
      · simp [hij]
      · have hlt : e < deg j := by
          have := hA₂ i j hij
          rw [hi] at this
          linarith
        rw [ht_zero j hlt, mul_zero]
    · rw [if_neg hi]
  have hAt : A *ᵥ t - t = A₁ *ᵥ t + A₂ *ᵥ t := by
    rw [hA, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  have hcomp : homComp deg (e - h) (A *ᵥ t - t) = A₁ *ᵥ homComp deg e w := by
    rw [hAt]
    rw [show homComp deg (e - h) (A₁ *ᵥ t + A₂ *ᵥ t) =
        homComp deg (e - h) (A₁ *ᵥ t) + homComp deg (e - h) (A₂ *ᵥ t) from
      map_add (homCompLin deg (e - h)) _ _]
    rw [hA₁comp, hA₂comp, add_zero, hte]
  rw [← hcomp]
  exact homComp_mem_dotRad deg hC ht (e - h)

end CFSG.LieType.SpecialLinear.ExteriorModel

end
