module

public import CFSG.Sporadic.Schreier.LyChainBound
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.KS.LyFive.G2

open Matrix

abbrev V := Fin 7 → ZMod 5

abbrev M := Matrix (Fin 7) (Fin 7) (ZMod 5)

section Product

variable (cc : Fin 7 → Fin 7 → V)

@[expose] noncomputable def crB : V →ₗ[ZMod 5] V →ₗ[ZMod 5] V :=
  LinearMap.mk₂ (ZMod 5) (fun u v => ∑ i, ∑ j, (u i * v j) • cc i j)
    (fun u u' v => by simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc])
    (fun u v v' => by simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_left_comm])

@[expose] noncomputable def cr (u v : V) : V := crB cc u v

theorem cr_def (u v : V) : cr cc u v = ∑ i, ∑ j, (u i * v j) • cc i j := rfl

theorem cr_single (i j : Fin 7) : cr cc (Pi.single i 1) (Pi.single j 1) = cc i j := by
  rw [cr_def]
  simp [Pi.single_apply]

@[expose] def IsAut (g : M) : Prop := ∀ u v, g *ᵥ cr cc u v = cr cc (g *ᵥ u) (g *ᵥ v)

theorem isAut_of_basis {g : M}
    (h : ∀ i j, g *ᵥ cc i j = cr cc (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1)) : IsAut cc g := by
  have key : (crB cc).compr₂ (Matrix.toLin' g) =
      (crB cc).compl₁₂ (Matrix.toLin' g) (Matrix.toLin' g) := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 5) (Fin 7)) (Pi.basisFun (ZMod 5) (Fin 7))
      fun i j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Pi.basisFun_apply,
      Matrix.toLin'_apply]
    change g *ᵥ cr cc (Pi.single i 1) (Pi.single j 1) = cr cc _ _
    rw [cr_single, h i j]
  intro u v
  have := LinearMap.congr_fun₂ key u v
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Matrix.toLin'_apply] at this
  exact this

theorem isAut_one : IsAut cc 1 := fun u v => by rw [one_mulVec, one_mulVec, one_mulVec]

theorem isAut_mul {a b : M} (ha : IsAut cc a) (hb : IsAut cc b) : IsAut cc (a * b) := by
  intro u v
  rw [← mulVec_mulVec, hb u v, ha, mulVec_mulVec, mulVec_mulVec]

theorem isAut_inv {a : (M)ˣ} (ha : IsAut cc (a : M)) : IsAut cc ((a⁻¹ : (M)ˣ) : M) := by
  intro u v
  have h := ha (((a⁻¹ : (M)ˣ) : M) *ᵥ u) (((a⁻¹ : (M)ˣ) : M) *ᵥ v)
  have e : ∀ x : V, (a : M) *ᵥ (((a⁻¹ : (M)ˣ) : M) *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [e, e] at h
  have e' : ∀ x : V, ((a⁻¹ : (M)ˣ) : M) *ᵥ ((a : M) *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  rw [← h, e']

@[expose] def A : Subgroup (M)ˣ where
  carrier := {g | IsAut cc (g : M)}
  one_mem' := isAut_one cc
  mul_mem' := fun {a b} ha hb => by
    change IsAut cc ((a : M) * (b : M))
    exact isAut_mul cc ha hb
  inv_mem' := fun {a} ha => isAut_inv cc ha

@[expose] noncomputable def Lm (u : V) : M := LinearMap.toMatrix' (crB cc u)

theorem Lm_mulVec (u v : V) : Lm cc u *ᵥ v = cr cc u v := by
  rw [Lm, LinearMap.toMatrix'_mulVec]
  rfl

theorem Lm_add (u u' : V) : Lm cc (u + u') = Lm cc u + Lm cc u' := by
  rw [Lm, Lm, Lm, map_add, map_add]

theorem Lm_smul (c : ZMod 5) (u : V) : Lm cc (c • u) = c • Lm cc u := by
  rw [Lm, Lm, map_smul, map_smul]

theorem mat_ext {X Y : M} (h : ∀ v, X *ᵥ v = Y *ᵥ v) : X = Y :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

theorem Lm_aut {g : (M)ˣ} (hg : g ∈ A cc) (u : V) :
    Lm cc ((g : M) *ᵥ u) = (g : M) * Lm cc u * ((g⁻¹ : (M)ˣ) : M) := by
  apply mat_ext
  intro v
  rw [Lm_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Lm_mulVec, hg, mulVec_mulVec, Units.mul_inv,
    one_mulVec]

@[expose] noncomputable def β (u v : V) : ZMod 5 := (Lm cc u * Lm cc v).trace

theorem β_aut {g : (M)ˣ} (hg : g ∈ A cc) (u v : V) :
    β cc ((g : M) *ᵥ u) ((g : M) *ᵥ v) = β cc u v := by
  rw [β, β, Lm_aut cc hg, Lm_aut cc hg]
  have e : (g : M) * Lm cc u * ((g⁻¹ : (M)ˣ) : M) * ((g : M) * Lm cc v * ((g⁻¹ : (M)ˣ) : M)) =
      (g : M) * (Lm cc u * Lm cc v) * ((g⁻¹ : (M)ˣ) : M) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((g⁻¹ : (M)ˣ) : M) (g : M), Units.inv_mul, Matrix.one_mul]
  rw [e, Matrix.trace_units_conj]

@[expose] noncomputable def βB : V →ₗ[ZMod 5] V →ₗ[ZMod 5] ZMod 5 :=
  LinearMap.mk₂ (ZMod 5) (β cc)
    (fun u u' v => by rw [β, β, β, Lm_add, Matrix.add_mul, Matrix.trace_add])
    (fun c u v => by rw [β, β, Lm_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun u v v' => by rw [β, β, β, Lm_add, Matrix.mul_add, Matrix.trace_add])
    (fun c u v => by rw [β, β, Lm_smul, Matrix.mul_smul, Matrix.trace_smul])

@[expose] noncomputable def Tβ : M := Matrix.of fun i j => β cc (Pi.single i 1) (Pi.single j 1)

theorem β_eq_dot (u v : V) : β cc u v = u ⬝ᵥ (Tβ cc *ᵥ v) := by
  have key : βB cc = Matrix.toLinearMap₂' (ZMod 5) (Tβ cc) := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 5) (Fin 7)) (Pi.basisFun (ZMod 5) (Fin 7))
      fun i j => ?_
    rw [Matrix.toLinearMap₂'_apply']
    simp only [Pi.basisFun_apply]
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
    rfl
  have := LinearMap.congr_fun₂ key u v
  rw [Matrix.toLinearMap₂'_apply'] at this
  exact this

end Product

abbrev Ins := ℕ × ℕ × ℕ × List ℕ

@[expose] def lc (cs : List ℕ) (us : List V) : V :=
  (List.zipWith (fun (c : ℕ) (u : V) => (c : ZMod 5) • u) cs us).sum

section Program

variable (cc : Fin 7 → Fin 7 → V) (ops : List M)

@[expose] noncomputable def pushV (gv : List V) (i : Ins) (us : List V) : List V :=
  if i.1 = 0 then us ++ [gv.getD i.2.1 0]
  else if i.1 = 1 then us ++ [ops.getD i.2.1 0 *ᵥ us.getD i.2.2.1 0]
  else if i.1 = 2 then us ++ [cr cc (us.getD i.2.1 0) (us.getD i.2.2.1 0)]
  else us

@[expose] def chkV (gv : List V) (i : Ins) (us : List V) : Prop :=
  if i.1 = 0 then True
  else if i.1 = 1 then True
  else if i.1 = 2 then True
  else if i.1 = 3 then ops.getD i.2.1 0 *ᵥ us.getD i.2.2.1 0 = lc i.2.2.2 us
  else if i.1 = 4 then cr cc (us.getD i.2.1 0) (us.getD i.2.2.1 0) = lc i.2.2.2 us
  else if i.1 = 5 then β cc (us.getD i.2.1 0) (us.getD i.2.2.1 0) = ((i.2.2.2.getD 0 0 : ℕ) : ZMod 5)
  else if i.1 = 6 then us.getD i.2.1 0 ≠ 0
  else False

@[expose] def mRun (gv : List V) : List Ins → List V → Prop
  | [], _ => True
  | i :: is, us => chkV cc ops gv i us ∧ mRun gv is (pushV cc ops gv i us)

theorem mRun_nil (gv : List V) (us : List V) : mRun cc ops gv [] us ↔ True := Iff.rfl

theorem mRun_cons (gv : List V) (i : Ins) (is : List Ins) (us : List V) :
    mRun cc ops gv (i :: is) us ↔ chkV cc ops gv i us ∧ mRun cc ops gv is (pushV cc ops gv i us) :=
  Iff.rfl

@[expose] noncomputable def mStk (gv : List V) : List Ins → List V → List V
  | [], us => us
  | i :: is, us => mStk gv is (pushV cc ops gv i us)

theorem mStk_cons (gv : List V) (i : Ins) (is : List Ins) (us : List V) :
    mStk cc ops gv (i :: is) us = mStk cc ops gv is (pushV cc ops gv i us) := rfl

variable {cc ops}

theorem getD_map_mulVec (g : M) (l : List V) (n : ℕ) :
    (l.map (g *ᵥ ·)).getD n 0 = g *ᵥ l.getD n 0 := by
  have := List.getD_map (f := (g *ᵥ ·)) (l := l) (n := n) (d := 0)
  rw [mulVec_zero] at this
  exact this

theorem lc_map (g : M) : ∀ (cs : List ℕ) (us : List V), lc cs (us.map (g *ᵥ ·)) = g *ᵥ lc cs us
  | [], us => by simp [lc]
  | c :: cs, [] => by simp [lc]
  | c :: cs, u :: us => by
    have ih := lc_map g cs us
    simp only [lc, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, mulVec_add, mulVec_smul]

variable {g : (M)ˣ} (hg : g ∈ A cc) (hops : ∀ o ∈ ops, (g : M) * o = o * g)
include hg hops

theorem ops_comm (a : ℕ) (v : V) : ops.getD a 0 *ᵥ ((g : M) *ᵥ v) = (g : M) *ᵥ (ops.getD a 0 *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec]
  congr 1
  by_cases ha : a < ops.length
  · rw [List.getD_eq_getElem _ _ ha]
    exact (hops _ (List.getElem_mem ha)).symm
  · rw [List.getD_eq_default _ _ (by omega), Matrix.zero_mul, Matrix.mul_zero]

theorem pushV_map (gv : List V) (i : Ins) (us : List V) :
    pushV cc ops (gv.map ((g : M) *ᵥ ·)) i (us.map ((g : M) *ᵥ ·)) =
      (pushV cc ops gv i us).map ((g : M) *ᵥ ·) := by
  unfold pushV
  split_ifs
  · rw [List.map_append, getD_map_mulVec]
    rfl
  · rw [List.map_append, getD_map_mulVec, ops_comm hg hops]
    rfl
  · rw [List.map_append, getD_map_mulVec, getD_map_mulVec, ← hg]
    rfl
  · rfl

theorem chkV_map (gv : List V) (i : Ins) (us : List V) (h : chkV cc ops gv i us) :
    chkV cc ops (gv.map ((g : M) *ᵥ ·)) i (us.map ((g : M) *ᵥ ·)) := by
  unfold chkV at h ⊢
  by_cases h0 : i.1 = 0
  · rw [if_pos h0]
    trivial
  rw [if_neg h0] at h ⊢
  by_cases h1 : i.1 = 1
  · rw [if_pos h1]
    trivial
  rw [if_neg h1] at h ⊢
  by_cases h2 : i.1 = 2
  · rw [if_pos h2]
    trivial
  rw [if_neg h2] at h ⊢
  by_cases h3 : i.1 = 3
  · rw [if_pos h3] at h ⊢
    rw [getD_map_mulVec, ops_comm hg hops, lc_map, h]
  rw [if_neg h3] at h ⊢
  by_cases h4 : i.1 = 4
  · rw [if_pos h4] at h ⊢
    rw [getD_map_mulVec, getD_map_mulVec, ← hg, lc_map, h]
  rw [if_neg h4] at h ⊢
  by_cases h5 : i.1 = 5
  · rw [if_pos h5] at h ⊢
    rw [getD_map_mulVec, getD_map_mulVec, β_aut cc hg]
    exact h
  rw [if_neg h5] at h ⊢
  by_cases h6 : i.1 = 6
  · rw [if_pos h6] at h ⊢
    rw [getD_map_mulVec]
    intro e
    apply h
    have := congrArg (((g⁻¹ : (M)ˣ) : M) *ᵥ ·) e
    simp only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at this
    exact this
  rw [if_neg h6] at h
  exact h.elim

theorem mRun_map (gv : List V) :
    ∀ (is : List Ins) (us : List V), mRun cc ops gv is us →
      mRun cc ops (gv.map ((g : M) *ᵥ ·)) is (us.map ((g : M) *ᵥ ·))
  | [], _, _ => trivial
  | i :: is, us, ⟨h1, h2⟩ => ⟨chkV_map hg hops gv i us h1, by
      rw [pushV_map hg hops]
      exact mRun_map gv is _ h2⟩

theorem mStk_map (gv : List V) :
    ∀ (is : List Ins) (us : List V),
      mStk cc ops (gv.map ((g : M) *ᵥ ·)) is (us.map ((g : M) *ᵥ ·)) =
        (mStk cc ops gv is us).map ((g : M) *ᵥ ·)
  | [], _ => rfl
  | i :: is, us => by
    change mStk cc ops _ is (pushV cc ops _ i _) = _
    rw [pushV_map hg hops]
    exact mStk_map gv is _

end Program

section Count

variable (cc : Fin 7 → Fin 7 → V) (ops : List M)

@[expose] def AC : Subgroup (M)ˣ where
  carrier := {g | g ∈ A cc ∧ ∀ o ∈ ops, (g : M) * o = o * g}
  one_mem' := ⟨(A cc).one_mem, fun o _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(A cc).mul_mem ha hb, fun o ho => ?_⟩
    rw [Units.val_mul, Matrix.mul_assoc, hb' o ho, ← Matrix.mul_assoc, ha' o ho, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(A cc).inv_mem ha, fun o ho => ?_⟩
    have h := ha' o ho
    have e1 : ((a⁻¹ : (M)ˣ) : M) * ((a : M) * o) * ((a⁻¹ : (M)ˣ) : M) = o * ((a⁻¹ : (M)ˣ) : M) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have e2 : ((a⁻¹ : (M)ˣ) : M) * (o * (a : M)) * ((a⁻¹ : (M)ˣ) : M) = ((a⁻¹ : (M)ˣ) : M) * o := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← e2, ← h, e1]

@[expose] noncomputable def passSet (F : List V) (is : List Ins) : Finset V := by
  classical
  exact Finset.univ.filter fun w => mRun cc ops (F ++ [w]) is []

theorem mem_passSet {F : List V} {is : List Ins} {w : V} :
    w ∈ passSet cc ops F is ↔ mRun cc ops (F ++ [w]) is [] := by
  classical
  unfold passSet
  simp

@[expose] noncomputable def fixS (F : List V) : Subgroup (M)ˣ :=
  CFSG.Sporadic.LySchreier.levelStab (AC cc ops) (fun l => F.getD l 0) F.length

theorem mem_fixS {F : List V} {g : (M)ˣ} :
    g ∈ fixS cc ops F ↔ g ∈ AC cc ops ∧ ∀ f ∈ F, (g : M) *ᵥ f = f := by
  rw [fixS, CFSG.Sporadic.LySchreier.mem_levelStab]
  refine and_congr Iff.rfl ⟨fun h f hf => ?_, fun h l hl => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hf
    have := h l hl
    rwa [List.getD_eq_getElem _ _ hl] at this
  · change (g : M) *ᵥ F.getD l 0 = F.getD l 0
    rw [List.getD_eq_getElem _ _ hl]
    exact h _ (List.getElem_mem hl)

theorem map_fix {F : List V} {g : (M)ˣ} (h : ∀ f ∈ F, (g : M) *ᵥ f = f) :
    F.map ((g : M) *ᵥ ·) = F := by
  conv_rhs => rw [← List.map_id F]
  exact List.map_congr_left h

theorem card_level_le {F : List V} {b : V} {is : List Ins}
    (hb : mRun cc ops (F ++ [b]) is []) :
    Nat.card (fixS cc ops F) ≤ (passSet cc ops F is).card * Nat.card (fixS cc ops (F ++ [b])) := by
  classical
  let bs : ℕ → V := fun l => (F ++ [b]).getD l 0
  have hL : fixS cc ops F = CFSG.Sporadic.LySchreier.levelStab (AC cc ops) bs F.length := by
    ext g
    rw [mem_fixS, CFSG.Sporadic.LySchreier.mem_levelStab]
    refine and_congr Iff.rfl ⟨fun h l hl => ?_, fun h f hf => ?_⟩
    · change (g : M) *ᵥ (F ++ [b]).getD l 0 = (F ++ [b]).getD l 0
      rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl]
      exact h _ (List.getElem_mem hl)
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hf
      have := h l hl
      change (g : M) *ᵥ (F ++ [b]).getD l 0 = (F ++ [b]).getD l 0 at this
      rwa [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl] at this
  have hLb : fixS cc ops (F ++ [b]) = CFSG.Sporadic.LySchreier.levelStab (AC cc ops) bs (F.length + 1) := by
    rw [fixS, List.length_append, List.length_singleton]
  have hb' : bs F.length = b := by simp [bs]
  have hstab : Nat.card (fixS cc ops (F ++ [b])) =
      Nat.card (MulAction.stabilizer (CFSG.Sporadic.LySchreier.levelStab (AC cc ops) bs F.length) b) := by
    rw [hLb, Nat.card_congr (CFSG.Sporadic.LySchreier.levelStabEquiv (AC cc ops) bs F.length), hb']
  rw [hstab, hL, ← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ b), Nat.card_prod]
  apply Nat.mul_le_mul_right
  have hsub : MulAction.orbit (CFSG.Sporadic.LySchreier.levelStab (AC cc ops) bs F.length) b ⊆
      (passSet cc ops F is : Set V) := by
    rintro _ ⟨⟨g, hgL⟩, rfl⟩
    rw [← hL] at hgL
    obtain ⟨⟨hgA, hgO⟩, hfix⟩ := (mem_fixS cc ops).1 hgL
    rw [Finset.mem_coe, mem_passSet]
    have := mRun_map hgA hgO (F ++ [b]) is [] hb
    rw [List.map_append, map_fix hfix, List.map_singleton, List.map_nil] at this
    exact this
  calc Nat.card (MulAction.orbit (CFSG.Sporadic.LySchreier.levelStab (AC cc ops) bs F.length) b)
      ≤ Nat.card (passSet cc ops F is : Set V) := Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (passSet cc ops F is).card := by simp

theorem eq_one_of_fix {gv : List V} {is : List Ins} {Ui : M}
    (hU : Ui * Matrix.of (fun r t : Fin 7 => (mStk cc ops gv is []).getD t 0 r) = 1)
    {g : (M)ˣ} (hg : g ∈ AC cc ops) (hfix : ∀ f ∈ gv, (g : M) *ᵥ f = f) : g = 1 := by
  set W := mStk cc ops gv is []
  set U : M := Matrix.of fun r t : Fin 7 => W.getD t 0 r
  have hW : W.map ((g : M) *ᵥ ·) = W := by
    have := mStk_map hg.1 hg.2 gv is []
    rw [map_fix hfix] at this
    exact this.symm
  have hGU : (g : M) * U = U := by
    ext r t
    have h1 := congrArg (fun l => l.getD t.val 0 r) hW
    simp only [getD_map_mulVec] at h1
    rw [Matrix.mul_apply]
    have : ((g : M) *ᵥ W.getD t.val 0) r = ∑ x, (g : M) r x * U x t := by
      rw [Matrix.mulVec]
      rfl
    rw [← this, h1]
    rfl
  have hUi : U * Ui = 1 := mul_eq_one_comm.1 hU
  apply Units.ext
  calc (g : M) = (g : M) * (U * Ui) := by rw [hUi, Matrix.mul_one]
    _ = U * Ui := by rw [← Matrix.mul_assoc, hGU]
    _ = 1 := hUi

end Count

end CFSG.KS.LyFive.G2

end
