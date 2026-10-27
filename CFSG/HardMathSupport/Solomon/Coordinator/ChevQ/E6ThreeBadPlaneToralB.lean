module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralBH
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompFix

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Mat

variable {K : Type} [Field K]

private theorem e6ToralB_cyc_cube : (signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_succ, signedCycMat_sq_mul]

private theorem e6ToralB_cyc_pow_mod (n : ℕ) :
    (signedCycMat : Matrix (Fin 3) (Fin 3) K) ^ n = signedCycMat ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, e6ToralB_cyc_cube, one_pow, one_mul]

private theorem e6ToralB_mono_conj (k : Fin 3) (μ : Fin 3 → K) {a b : Fin 3} {lam t : K}
    (h : lam * μ b = μ a) :
    (1 + Matrix.single (a + k) (b + k) (lam * t)) *
        Matrix.of (fun x y : Fin 3 => if x = y + k then μ y else 0) =
      Matrix.of (fun x y : Fin 3 => if x = y + k then μ y else 0) *
        (1 + Matrix.single a b t) := by
  ext x y
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
    Matrix.add_apply]
  congr 1
  by_cases hx : x = a + k
  · subst hx
    rw [Matrix.single_mul_apply_same]
    by_cases hy : y = b
    · subst hy
      rw [Matrix.mul_single_apply_same]
      simp only [Matrix.of_apply, eq_self_iff_true, if_true]
      linear_combination t * h
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hy]
      simp only [Matrix.of_apply]
      rw [if_neg fun e => hy (add_right_cancel e).symm, mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx]
    by_cases hy : y = b
    · subst hy
      rw [Matrix.mul_single_apply_same]
      simp only [Matrix.of_apply]
      rw [if_neg hx, zero_mul]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hy]

private theorem e6ToralB_diag_eq (d : Fin 3 → K) :
    diagonal d = Matrix.of (fun x y : Fin 3 => if x = y + 0 then d y else 0) := by
  ext x y
  simp only [Matrix.diagonal_apply, Matrix.of_apply, add_zero]
  split_ifs with h <;> simp [h]

private theorem e6ToralB_diag_cyc (d : Fin 3 → K) :
    diagonal d * signedCycMat =
      Matrix.of (fun x y : Fin 3 => if x = y + 1 then ![-d 1, -d 2, d 0] y else 0) := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [signedCycMat, Matrix.diagonal_mul]

private theorem e6ToralB_diag_cyc_sq (d : Fin 3 → K) :
    diagonal d * signedCycMat ^ 2 =
      Matrix.of (fun x y : Fin 3 => if x = y + 2 then ![d 2, -d 0, -d 1] y else 0) := by
  rw [signedCycMat_sq]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Matrix.diagonal_mul]

private theorem e6ToralB_mform {d : Fin 3 → K} (hd : ∀ a, d a ≠ 0) (n : ℕ) :
    ∃ (k : Fin 3) (μ : Fin 3 → K), (∀ a, μ a ≠ 0) ∧ (3 ∣ n → k = 0 ∧ μ = d) ∧
      (¬ 3 ∣ n → k = 1 ∨ k = 2) ∧
      diagonal d * signedCycMat ^ n =
        Matrix.of (fun x y : Fin 3 => if x = y + k then μ y else 0) := by
  rw [e6ToralB_cyc_pow_mod]
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · refine ⟨0, d, hd, fun _ => ⟨rfl, rfl⟩, fun h' => absurd (Nat.dvd_of_mod_eq_zero h) h', ?_⟩
    rw [h, pow_zero, Matrix.mul_one, e6ToralB_diag_eq]
  · refine ⟨1, ![-d 1, -d 2, d 0], ?_,
      fun h' => absurd (Nat.mod_eq_zero_of_dvd h') (by omega), fun _ => Or.inl rfl, ?_⟩
    · intro a
      fin_cases a <;> simp [hd]
    · rw [h, pow_one, e6ToralB_diag_cyc]
  · refine ⟨2, ![d 2, -d 0, -d 1], ?_,
      fun h' => absurd (Nat.mod_eq_zero_of_dvd h') (by omega), fun _ => Or.inr rfl, ?_⟩
    · intro a
      fin_cases a <;> simp [hd]
    · rw [h, e6ToralB_diag_cyc_sq]

private theorem e6ToralB_conj_aux {D E W Wi T T' : Matrix (Fin 3) (Fin 3) K} (hDE : D * E = 1)
    (hWWi : W * Wi = 1) (key : T' * (D * W) = (D * W) * T) : D * (W * T * Wi) * E = T' := by
  calc D * (W * T * Wi) * E = (D * W) * T * (Wi * E) := by simp only [Matrix.mul_assoc]
    _ = T' * (D * W) * (Wi * E) := by rw [key]
    _ = T' * (D * (W * Wi) * E) := by simp only [Matrix.mul_assoc]
    _ = T' := by rw [hWWi, Matrix.mul_one, hDE, Matrix.mul_one]

private theorem e6ToralB_conj_transvection {dd : Fin 3 → Kˣ} {w : SpecialLinearGroup (Fin 3) K}
    {k : Fin 3} {μ : Fin 3 → K} (hμ : ∀ a, μ a ≠ 0)
    (hM : ((diagGL3 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (w : Matrix (Fin 3) (Fin 3) K) =
      Matrix.of (fun x y : Fin 3 => if x = y + k then μ y else 0))
    {a b a' b' : Fin 3} (hab : a ≠ b) (hab' : a' ≠ b') (ha : a' = a + k) (hb : b' = b + k)
    (t : K) :
    conjDiag3 dd (w * Matrix.SpecialLinearGroup.transvection hab t * w⁻¹) =
      Matrix.SpecialLinearGroup.transvection hab' (μ a / μ b * t) := by
  subst ha hb
  apply Subtype.ext
  rw [coe_conjDiag3, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  refine e6ToralB_conj_aux ?_ ?_ ?_
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [hM]
    exact e6ToralB_mono_conj k μ (div_mul_cancel₀ (μ a) (hμ b))

private theorem e6ToralB_d_ne_zero {dd : Fin 3 → Kˣ} {w : SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} {n : ℕ}
    (h : ((diagGL3 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (w : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ n) (a : Fin 3) :
    d a ≠ 0 := by
  have h1 := congrArg Matrix.det h
  simp only [Matrix.det_mul, w.2, mul_one, Matrix.det_pow, det_signedCycMat, one_pow,
    Matrix.det_diagonal] at h1
  have hD : IsUnit ((diagGL3 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [h1] at hD
  exact Finset.prod_ne_zero_iff.1 hD.ne_zero a (Finset.mem_univ a)

private theorem e6ToralB_w_eq {dd : Fin 3 → Kˣ} {w : SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} {n : ℕ}
    (h : ((diagGL3 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (w : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ n) :
    (w : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun j => (((dd j)⁻¹ : Kˣ) : K) * d j) * signedCycMat ^ n := by
  have hE : (((diagGL3 dd)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun j => (((dd j)⁻¹ : Kˣ) : K)) := rfl
  calc (w : Matrix (Fin 3) (Fin 3) K)
      = (((diagGL3 dd)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((diagGL3 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (w : Matrix (Fin 3) (Fin 3) K)) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = _ := by rw [h, hE, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

end Mat

section Pattern

variable {K : Type*} [Field K]

private theorem e6ToralB_cyc_vanish {f : Fin 3 → Fin 3 → K} {k : Fin 3} (hk : k = 1 ∨ k = 2)
    (hstep : ∀ a b, a ≠ b → ∃ c : K, f (a + k) (b + k) = c * f a b) (h01 : f 0 1 = 0)
    (h10 : f 1 0 = 0) : ∀ a b, a ≠ b → f a b = 0 := by
  have hs : ∀ a b, a ≠ b → f a b = 0 → f (a + k) (b + k) = 0 := fun a b hab h0 => by
    obtain ⟨c, hc⟩ := hstep a b hab
    rw [hc, h0, mul_zero]
  rcases hk with rfl | rfl
  · have h12 : f 1 2 = 0 := hs 0 1 (by decide) h01
    have h20 : f 2 0 = 0 := hs 1 2 (by decide) h12
    have h21 : f 2 1 = 0 := hs 1 0 (by decide) h10
    have h02 : f 0 2 = 0 := hs 2 1 (by decide) h21
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption
  · have h20 : f 2 0 = 0 := hs 0 1 (by decide) h01
    have h12 : f 1 2 = 0 := hs 2 0 (by decide) h20
    have h02 : f 0 2 = 0 := hs 1 0 (by decide) h10
    have h21 : f 2 1 = 0 := hs 0 2 (by decide) h02
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption

private theorem e6ToralB_exists_pair {d : Fin 3 → K} (hd : ∃ a b, d a ≠ d b) :
    ∃ p q : Fin 3, ∀ a b, a ≠ b → d a = d b → (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  obtain ⟨a0, b0, h0⟩ := hd
  by_cases h01 : d 0 = d 1
  · have h12 : d 1 ≠ d 2 := fun h => h0 (by fin_cases a0 <;> fin_cases b0 <;> simp [h01, h])
    have h02 : d 0 ≠ d 2 := fun h => h12 (h01.symm.trans h)
    refine ⟨0, 1, fun a b hab hd => ?_⟩
    fin_cases a <;> fin_cases b <;>
      first | exact absurd rfl hab | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ |
        exact absurd hd ‹_› | exact absurd hd.symm ‹_›
  · by_cases h12 : d 1 = d 2
    · have h02 : d 0 ≠ d 2 := fun h => h01 (h.trans h12.symm)
      refine ⟨1, 2, fun a b hab hd => ?_⟩
      fin_cases a <;> fin_cases b <;>
        first | exact absurd rfl hab | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ |
          exact absurd hd ‹_› | exact absurd hd.symm ‹_›
    · by_cases h02 : d 0 = d 2
      · refine ⟨0, 2, fun a b hab hd => ?_⟩
        fin_cases a <;> fin_cases b <;>
          first | exact absurd rfl hab | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ |
            exact absurd hd ‹_› | exact absurd hd.symm ‹_›
      · refine ⟨0, 1, fun a b hab hd => ?_⟩
        fin_cases a <;> fin_cases b <;>
          first | exact absurd rfl hab | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ |
            exact absurd hd ‹_› | exact absurd hd.symm ‹_›

private theorem e6ToralB_diag_vanish {f : Fin 3 → Fin 3 → K} {d : Fin 3 → K}
    (hd0 : ∀ a, d a ≠ 0) (hstep : ∀ a b, a ≠ b → f a b = d a / d b * f a b) {p q : Fin 3}
    (hpq : ∀ a b, a ≠ b → d a = d b → (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (hp : f p q = 0) (hq : f q p = 0) : ∀ a b, a ≠ b → f a b = 0 := by
  intro a b hab
  by_cases hd : d a = d b
  · rcases hpq a b hab hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact hq
  · have h1 : d a / d b - 1 ≠ 0 := sub_ne_zero.2 fun h => hd ((div_eq_one_iff_eq (hd0 b)).1 h)
    have h2 : (d a / d b - 1) * f a b = 0 := by
      rw [sub_mul, one_mul, ← hstep a b hab, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left h1

end Pattern

section Toral

variable
  {K : Type} [Field K]

private def e6ToralBH (K : Type) [Field K] : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K (Set.range (hVec Tag.E6 K))

open Classical in
private def e6ToralBCoord (γ : Fin Tag.E6.rank → ℤ) : RootModule Tag.E6 K →ₗ[K] K :=
  if h : IsRoot Tag.E6 γ then Finsupp.lapply (Sum.inr ⟨γ, h⟩) else 0

private theorem e6ToralBCoord_apply {γ : Fin Tag.E6.rank → ℤ} (h : IsRoot Tag.E6 γ)
    (x : RootModule Tag.E6 K) : e6ToralBCoord γ x = x (Sum.inr ⟨γ, h⟩) := by
  rw [e6ToralBCoord, dif_pos h, Finsupp.lapply_apply]

private theorem e6ToralBH_coord {v : RootModule Tag.E6 K} (hv : v ∈ e6ToralBH K)
    (β : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) : v (Sum.inr β) = 0 := by
  have hv' : v ∈ Submodule.span K (Set.range (hVec Tag.E6 K)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact Finsupp.single_eq_of_ne Sum.inr_ne_inl
  | zero => simp
  | add x y _ _ hx hy => rw [Finsupp.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Finsupp.smul_apply, hx, smul_zero]

private theorem e6ToralBH_of_coord {v : RootModule Tag.E6 K}
    (hv : ∀ β : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}, v (Sum.inr β) = 0) :
    v ∈ e6ToralBH K := by
  have e : v = ∑ j, v (Sum.inl j) • hVec Tag.E6 K j := by
    ext b
    rcases b with j | β
    · simp [hVec, Finsupp.single_apply]
    · simp [hVec, Finsupp.single_apply, hv β]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem e6ToralBH_map {g : ModGL Tag.E6 K}
    (hg : ∀ j, (g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) ∈ e6ToralBH K)
    {v : RootModule Tag.E6 K} (hv : v ∈ e6ToralBH K) :
    (g : Module.End K (RootModule Tag.E6 K)) v ∈ e6ToralBH K := by
  have h : e6ToralBH K ≤ (e6ToralBH K).comap (g : Module.End K (RootModule Tag.E6 K)) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hg j)
  exact h hv

private theorem e6ToralBH_list (l : List (Fin Tag.E6.rank)) (j : Fin Tag.E6.rank) :
    (((l.map fun i => weylElt Tag.E6 K i 1).prod : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) ∈ e6ToralBH K := by
  induction l generalizing j with
  | nil =>
    rw [List.map_nil, List.prod_nil, Units.val_one, Module.End.one_apply]
    exact Submodule.subset_span ⟨j, rfl⟩
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply]
    refine e6ToralBH_map (fun j' => ?_) (ih j)
    rw [weylElt_hVec]
    exact sub_mem (Submodule.subset_span ⟨j', rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

private theorem e6ToralBH_monomial {m : ModGL Tag.E6 K} (hm : m ∈ monomialSubgroup Tag.E6 K)
    (j : Fin Tag.E6.rank) :
    (m : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) ∈ e6ToralBH K := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hm
  obtain ⟨ν, hν, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hν, Units.val_mul, Module.End.mul_apply]
  refine e6ToralBH_map (fun j' => ?_) (e6ToralBH_list ν j)
  rw [(torusGroup_le_diagonalGroup hk).1 j']
  exact Submodule.subset_span ⟨j', rfl⟩

private theorem e6ToralB_rootDiagUnit_hVec (c : Fin Tag.E6.rank → Kˣ) (j : Fin Tag.E6.rank) :
    ((rootDiagUnit Tag.E6 c : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (hVec Tag.E6 K j) = hVec Tag.E6 K j :=
  rootDiag_hVec c j

private theorem e6ToralB_rootDiagUnit_rootVec (c : Fin Tag.E6.rank → Kˣ)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ((rootDiagUnit Tag.E6 c : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (rootVec Tag.E6 K α) = ((rootChar c α : Kˣ) : K) • rootVec Tag.E6 K α :=
  rootDiag_rootVec c hα

private theorem e6ToralBH_rootDiag (c : Fin Tag.E6.rank → Kˣ) {v : RootModule Tag.E6 K}
    (hv : v ∈ e6ToralBH K) :
    ((rootDiagUnit Tag.E6 c : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v ∈
      e6ToralBH K :=
  e6ToralBH_map (fun j => by
    rw [e6ToralB_rootDiagUnit_hVec]
    exact Submodule.subset_span ⟨j, rfl⟩) hv

private theorem e6ToralB_mapsRootLines_rootDiagUnit (c : Fin Tag.E6.rank → Kˣ) :
    MapsRootLines (rootDiagUnit Tag.E6 c : ModGL Tag.E6 K) (1 : WeylGroup Tag.E6) := fun α hα =>
  ⟨rootChar c α, by rw [one_smul]; exact e6ToralB_rootDiagUnit_rootVec c hα⟩

private theorem e6ToralB_coord {g : ModGL Tag.E6 K} {W : WeylGroup Tag.E6}
    (hW : MapsRootLines g W)
    (hH : ∀ j, (g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) ∈ e6ToralBH K)
    {α γ : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hγ : IsRoot Tag.E6 γ) {c : Kˣ}
    (hc : (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) =
      (c : K) • rootVec Tag.E6 K γ) (x : RootModule Tag.E6 K) :
    e6ToralBCoord γ ((g : Module.End K (RootModule Tag.E6 K)) x) =
      (c : K) * e6ToralBCoord α x := by
  obtain ⟨c', hc'⟩ := hW α hα
  have hγW : γ = W • α := by
    rw [hc] at hc'
    exact eq_of_smul_rootVec_eq hγ (IsRoot.smul hα W) hc'
  subst hγW
  rw [e6ToralBCoord_apply hγ, e6ToralBCoord_apply hα]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]
  | single l r =>
    have e : (g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single l r) =
        r • (g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single l 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, Finsupp.smul_apply, smul_eq_mul]
    rcases l with j | ⟨β, hβ⟩
    · have h0 : (g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single (Sum.inl j) 1)
          (Sum.inr ⟨W • α, hγ⟩) = 0 := e6ToralBH_coord (hH j) _
      rw [h0, mul_zero, Finsupp.single_eq_of_ne Sum.inr_ne_inl, mul_zero]
    · by_cases hβα : β = α
      · have hβα' : (⟨β, hβ⟩ : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) = ⟨α, hα⟩ :=
          Subtype.ext hβα
        rw [hβα']
        have hv : (g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) =
            (c : K) • Finsupp.single (Sum.inr ⟨W • α, hγ⟩) 1 := by
          rw [← CFSG.Blueprint.Chevalley.rootVec_eq_single_of_isRoot hα,
            ← CFSG.Blueprint.Chevalley.rootVec_eq_single_of_isRoot hγ]
          exact hc
        rw [hv, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same, Finsupp.single_eq_same]
        ring
      · obtain ⟨c'', hc''⟩ := hW β hβ
        have hv : (g : Module.End K (RootModule Tag.E6 K)) (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1) =
            (c'' : K) • Finsupp.single (Sum.inr ⟨W • β, IsRoot.smul hβ W⟩) 1 := by
          rw [← CFSG.Blueprint.Chevalley.rootVec_eq_single_of_isRoot hβ,
            ← CFSG.Blueprint.Chevalley.rootVec_eq_single_of_isRoot (IsRoot.smul hβ W)]
          exact hc''
        have hne1 : (Sum.inr ⟨W • α, hγ⟩ : Label Tag.E6) ≠ Sum.inr ⟨W • β, IsRoot.smul hβ W⟩ :=
          fun h => hβα ((smul_left_cancel_iff W).1 (congrArg Subtype.val (Sum.inr.inj h))).symm
        have hne2 : (Sum.inr ⟨α, hα⟩ : Label Tag.E6) ≠ Sum.inr ⟨β, hβ⟩ :=
          fun h => hβα (congrArg Subtype.val (Sum.inr.inj h)).symm
        rw [hv, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_of_ne hne1, mul_zero,
          Finsupp.single_eq_of_ne hne2, mul_zero, mul_zero]

private theorem e6ToralB_count (T : Submodule K (RootModule Tag.E6 K))
    (L : RootModule Tag.E6 K →ₗ[K] (Fin 3 → K)) :
    Module.finrank K T ≤ Module.finrank K ↥(T ⊓ LinearMap.ker L) + 3 := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker L)
  have e2 := LinearMap.finrank_range_add_finrank_ker L
  have e3 := Submodule.finrank_le (T ⊔ LinearMap.ker L)
  have e4 := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_fin_fun] at e4
  omega

private theorem e6ToralB_prod_conj {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (i : Fin 3) {Y : ModGL Tag.E6 K} (hY : Y ∈ e6LineFactor K i) :
    (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) * Y * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2))⁻¹ =
      ρ i (w i) * Y * (ρ i (w i))⁻¹ := by
  have hm : ∀ j, ρ j (w j) ∈ e6LineFactor K j := fun j => by
    rw [← hrange j]
    exact ⟨_, rfl⟩
  have hc : ∀ j, j ≠ i → ∀ Z ∈ e6LineFactor K i, ρ j (w j) * Z * (ρ j (w j))⁻¹ = Z :=
    fun j hj Z hZ => mul_inv_eq_of_eq_mul (e6LineFactor_commute hj (hm j) hZ)
  have hci : ρ i (w i) * Y * (ρ i (w i))⁻¹ ∈ e6LineFactor K i :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hm i) hY) (Subgroup.inv_mem _ (hm i))
  have e : (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) * Y * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2))⁻¹ =
      ρ 0 (w 0) * (ρ 1 (w 1) * (ρ 2 (w 2) * Y * (ρ 2 (w 2))⁻¹) * (ρ 1 (w 1))⁻¹) *
        (ρ 0 (w 0))⁻¹ := by group
  rw [e]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [hc 2 (by decide) Y hY, hc 1 (by decide) Y hY]
  · rw [hc 2 (by decide) Y hY, hc 0 (by decide) _ hci]
  · rw [hc 1 (by decide) _ hci, hc 0 (by decide) _ hci]

private theorem e6ToralB_prod_rootVec
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
    {i : Fin 3} {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ e6LineRoots i) {lam : K}
    (h : (ρ i (w i) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
      lam • rootVec Tag.E6 K β) :
    ((ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) = lam • rootVec Tag.E6 K β := by
  have hm : ∀ j, ρ j (w j) ∈ e6LineFactor K j := fun j => by
    rw [← hrange j]
    exact ⟨_, rfl⟩
  have hfix : ∀ j, j ≠ i →
      (ρ j (w j) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
        rootVec Tag.E6 K β := fun j hj =>
    e6LineFactor_fix_rootVec (Ne.symm hj) hβ (hm j)
  simp only [Units.val_mul, Module.End.mul_apply]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [hfix 2 (by decide), hfix 1 (by decide), h]
  · rw [hfix 2 (by decide), h, map_smul, hfix 0 (by decide)]
  · rw [h, map_smul, hfix 1 (by decide), map_smul, hfix 0 (by decide)]

private theorem e6ToralB_weyl {P g : ModGL Tag.E6 K} (hP : P ∈ monomialSubgroup Tag.E6 K)
    {c : Fin Tag.E6.rank → Kˣ} (hg : rootDiagUnit Tag.E6 c * P = g)
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (hγ : IsRoot Tag.E6 γ)
    (hγp : 0 < height γ) {κ : K}
    (h : g * pinnedX Tag.E6 K β 1 * g⁻¹ = pinnedX Tag.E6 K γ κ) :
    weylQuotientHom Tag.E6 K ⟨P, hP⟩ • β = γ := by
  subst hg
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hP hβ
  have e : rootDiagUnit Tag.E6 c * P * pinnedX Tag.E6 K β 1 * (rootDiagUnit Tag.E6 c * P)⁻¹ =
      pinnedX Tag.E6 K (weylQuotientHom Tag.E6 K ⟨P, hP⟩ • β)
        ((rootChar c (weylQuotientHom Tag.E6 K ⟨P, hP⟩ • β) : K) * ((μ : K) * 1)) := by
    calc rootDiagUnit Tag.E6 c * P * pinnedX Tag.E6 K β 1 * (rootDiagUnit Tag.E6 c * P)⁻¹ =
        rootDiagUnit Tag.E6 c * (P * pinnedX Tag.E6 K β 1 * P⁻¹) *
          (rootDiagUnit Tag.E6 c)⁻¹ := by group
      _ = _ := by rw [hμ 1, rootDiagUnit_conj_pinnedX c (IsRoot.smul hβ _)]
  rw [e] at h
  exact CFSG.SeitzReduction.F4Pilot.eq_of_pinnedX_eq_pinnedX (IsRoot.smul hβ _) ⟨hγ, hγp⟩
    (mul_ne_zero (Units.ne_zero _) (by rw [mul_one]; exact Units.ne_zero _)) h

theorem e6Toral_caseB_bound_of_cartan {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hfr : ∀ i, IsA2Frame (ρ i) (σ i)) (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (h01 : ∀ i, σ i 0 1 = (e6LinePair i).1) (h12 : ∀ i, σ i 1 2 = (e6LinePair i).2)
    (hmono : ∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K)
    (c : Fin Tag.E6.rank → Kˣ) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (d : Fin 3 → Fin 3 → K) (n : Fin 3 → ℕ)
    (hw : ∀ i, ((diagGL3 fun j => rootChar c (σ i j 0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (w i : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d i) * signedCycMat ^ n i)
    (hsc : ∀ i, 3 ∣ n i → ∃ a b, d i a ≠ d i b)
    (hcart : ∃ k : Fin Tag.E6.rank,
      ((rootDiagUnit Tag.E6 c * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K k) ≠ hVec Tag.E6 K k) :
    Module.finrank K ↥(LinearMap.ker
        (((rootDiagUnit Tag.E6 c * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) - 1) ⊓
      LinearMap.ker ((rootDiagUnit Tag.E6 (e6LineChar ω) : Module.End K (RootModule Tag.E6 K)) - 1))
      ≤ 11 := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P, ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2) = P := ⟨_, rfl⟩
  rw [hPdef] at hcart ⊢
  obtain ⟨g, hgdef⟩ : ∃ g, rootDiagUnit Tag.E6 c * P = g := ⟨_, rfl⟩
  rw [hgdef] at hcart ⊢
  obtain ⟨F, hFdef⟩ : ∃ F, LinearMap.ker
      ((rootDiagUnit Tag.E6 (e6LineChar ω) : Module.End K (RootModule Tag.E6 K)) - 1) = F :=
    ⟨_, rfl⟩
  rw [hFdef]
  have hdet : ∀ i a, d i a ≠ 0 := fun i => e6ToralB_d_ne_zero (hw i)
  have hwm := fun i => e6ToralB_w_eq (hw i)
  have hρM : ∀ i, ρ i (w i) ∈ monomialSubgroup Tag.E6 K := fun i =>
    frame_mem_monomialSubgroup (hfr i) (hmono i) (hwm i)
  have hPM : P ∈ monomialSubgroup Tag.E6 K := by
    rw [← hPdef]
    exact mul_mem (mul_mem (hρM 0) (hρM 1)) (hρM 2)
  choose k μ hμ0 hk0 hk12 hform using fun i => e6ToralB_mform (hdet i) (n i)
  have hPconj : ∀ i (Y : ModGL Tag.E6 K), Y ∈ e6LineFactor K i →
      P * Y * P⁻¹ = ρ i (w i) * Y * (ρ i (w i))⁻¹ := fun i Y hY => by
    rw [← hPdef]
    exact e6ToralB_prod_conj hrange w i hY
  have hPv : ∀ i (β : Fin Tag.E6.rank → ℤ), β ∈ e6LineRoots i → ∀ lam : K,
      (ρ i (w i) : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
        lam • rootVec Tag.E6 K β →
      (P : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K β) =
        lam • rootVec Tag.E6 K β := fun i β hβ lam h => by
    rw [← hPdef]
    exact e6ToralB_prod_rootVec hrange w hβ h
  have hgconj : ∀ i A, g * ρ i A * g⁻¹ =
      ρ i (conjDiag3 (fun j => rootChar c (σ i j 0)) (w i * A * (w i)⁻¹)) := by
    intro i A
    have hA : ρ i A ∈ e6LineFactor K i := by
      rw [← hrange i]
      exact ⟨_, rfl⟩
    rw [← hgdef]
    calc rootDiagUnit Tag.E6 c * P * ρ i A * (rootDiagUnit Tag.E6 c * P)⁻¹ =
        rootDiagUnit Tag.E6 c * (P * ρ i A * P⁻¹) * (rootDiagUnit Tag.E6 c)⁻¹ := by group
      _ = rootDiagUnit Tag.E6 c * ρ i (w i * A * (w i)⁻¹) * (rootDiagUnit Tag.E6 c)⁻¹ := by
        rw [hPconj i _ hA, map_mul, map_mul, map_inv]
      _ = _ := (hfr i).torus c _
  obtain ⟨W, hWdef⟩ : ∃ W, weylQuotientHom Tag.E6 K ⟨P, hPM⟩ = W := ⟨_, rfl⟩
  have hWg : MapsRootLines g W := by
    have h : MapsRootLines (rootDiagUnit Tag.E6 c * P) (1 * weylQuotientHom Tag.E6 K ⟨P, hPM⟩) :=
      (e6ToralB_mapsRootLines_rootDiagUnit c).mul (mapsRootLines_weylQuotientHom ⟨P, hPM⟩)
    rwa [one_mul, hWdef, hgdef] at h
  have hH : ∀ j, (g : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K j) ∈ e6ToralBH K := by
    intro j
    rw [← hgdef, Units.val_mul, Module.End.mul_apply]
    exact e6ToralBH_rootDiag c (e6ToralBH_monomial hPM j)
  have hmemR : ∀ i a b, a ≠ b → σ i a b ∈ e6LineRoots i := by
    intro i a b hab
    have h := frame_roots_eq (hfr i).neg (hfr i).add (h01 i) (h12 i)
    rw [← e6LineRoots_eq_pair] at h
    have hr : σ i a b ∈ {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ i a b} := ⟨a, b, hab, rfl⟩
    rw [h] at hr
    exact hr
  have hrootsR : ∀ i β, β ∈ e6LineRoots i → ∃ a b, a ≠ b ∧ β = σ i a b := by
    intro i β hβ
    have h := frame_roots_eq (hfr i).neg (hfr i).add (h01 i) (h12 i)
    rw [← e6LineRoots_eq_pair] at h
    have hr : β ∈ (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) := hβ
    rw [← h] at hr
    exact hr
  have hconjX : ∀ i a b, a ≠ b → ∃ κ : K, g * pinnedX Tag.E6 K (σ i a b) 1 * g⁻¹ =
      pinnedX Tag.E6 K (σ i (a + k i) (b + k i)) κ := by
    intro i a b hab
    have hab' : a + k i ≠ b + k i := fun h => hab (add_right_cancel h)
    obtain ⟨ε, hε⟩ := (hfr i).transv a b hab
    obtain ⟨ε', hε'⟩ := (hfr i).transv (a + k i) (b + k i) hab'
    refine ⟨(ε' : K) * (μ i a / μ i b * ((ε⁻¹ : Kˣ) : K)), ?_⟩
    have h1 : pinnedX Tag.E6 K (σ i a b) 1 =
        ρ i (Matrix.SpecialLinearGroup.transvection hab ((ε⁻¹ : Kˣ) : K)) := by
      rw [hε, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, hgconj, e6ToralB_conj_transvection (hμ0 i) ((hw i).trans (hform i)) hab hab' rfl rfl,
      hε']
  have hWσ : ∀ i a b, a ≠ b → W • σ i a b = σ i (a + k i) (b + k i) := by
    intro i
    have key : ∀ a b, a ≠ b → 0 < height (σ i (a + k i) (b + k i)) →
        W • σ i a b = σ i (a + k i) (b + k i) := by
      intro a b hab hpos
      obtain ⟨κ, hκ⟩ := hconjX i a b hab
      rw [← hWdef]
      exact e6ToralB_weyl hPM hgdef ((hfr i).isRoot a b hab)
        ((hfr i).isRoot _ _ fun h => hab (add_right_cancel h)) hpos hκ
    intro a b hab
    rcases IsRoot.height_pos_or_neg ((hfr i).isRoot _ _ fun h => hab (add_right_cancel h)) with
      hpos | hneg
    · exact key a b hab hpos
    · have hpos' : 0 < height (σ i (b + k i) (a + k i)) := by
        rw [(hfr i).neg (a + k i) (b + k i), height_neg]
        linarith
      have h := key b a (Ne.symm hab) hpos'
      rw [(hfr i).neg a b, (hfr i).neg (a + k i) (b + k i), smul_neg] at h
      exact neg_injective h
  have hdiag : ∀ i, 3 ∣ n i → ∀ a b, a ≠ b →
      (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (σ i a b)) =
        (d i a / d i b) • rootVec Tag.E6 K (σ i a b) := by
    intro i hn a b hab
    obtain ⟨hk, hμ⟩ := hk0 i hn
    have hβ := (hfr i).isRoot a b hab
    have hβm := hmemR i a b hab
    have hoff : ∀ x y, x ≠ y → (w i : Matrix (Fin 3) (Fin 3) K) x y = 0 := by
      intro x y hxy
      rw [hwm i, e6ToralB_cyc_pow_mod, Nat.mod_eq_zero_of_dvd hn, pow_zero, Matrix.mul_one,
        Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨e, he⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ((hfr i).diag _ hoff)
    obtain ⟨ε, hε⟩ := (hfr i).transv a b hab
    have hY : pinnedX Tag.E6 K (σ i a b) ((ε : K) * 1) ∈ e6LineFactor K i :=
      pinnedX_mem_rootSpan (S := (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) hβm _
    have hX1 : g * pinnedX Tag.E6 K (σ i a b) ((ε : K) * 1) * g⁻¹ =
        pinnedX Tag.E6 K (σ i a b)
          ((rootChar c (σ i a b) : K) * ((rootChar e (σ i a b) : K) * ((ε : K) * 1))) := by
      rw [← hgdef]
      calc rootDiagUnit Tag.E6 c * P * pinnedX Tag.E6 K (σ i a b) ((ε : K) * 1) *
            (rootDiagUnit Tag.E6 c * P)⁻¹ =
          rootDiagUnit Tag.E6 c * (P * pinnedX Tag.E6 K (σ i a b) ((ε : K) * 1) * P⁻¹) *
            (rootDiagUnit Tag.E6 c)⁻¹ := by group
        _ = _ := by
          rw [hPconj i _ hY, he, rootDiagUnit_conj_pinnedX e hβ, rootDiagUnit_conj_pinnedX c hβ]
    have hX2 : g * pinnedX Tag.E6 K (σ i a b) ((ε : K) * 1) * g⁻¹ =
        pinnedX Tag.E6 K (σ i a b) ((ε : K) * (d i a / d i b * 1)) := by
      rw [← hε 1, hgconj, e6ToralB_conj_transvection (hμ0 i) ((hw i).trans (hform i)) hab hab
        (by rw [hk, add_zero]) (by rw [hk, add_zero]), hε, hμ]
    have hs : (rootChar c (σ i a b) : K) * (rootChar e (σ i a b) : K) = d i a / d i b := by
      have h := pinnedX_injective Tag.E6 K _ (hX1.symm.trans hX2)
      exact mul_right_cancel₀ (Units.ne_zero ε) (by linear_combination h)
    rw [← hgdef, Units.val_mul, Module.End.mul_apply,
      hPv i _ hβm (rootChar e (σ i a b) : K)
        (by rw [he]; exact e6ToralB_rootDiagUnit_rootVec e hβ),
      map_smul, e6ToralB_rootDiagUnit_rootVec c hβ, smul_smul,
      mul_comm (rootChar e (σ i a b) : K), hs]
  have hpair : ∀ i, ∃ p q : Fin 3, (3 ∣ n i → ∀ a b, a ≠ b → d i a = d i b →
      (a = p ∧ b = q) ∨ (a = q ∧ b = p)) ∧ (¬ 3 ∣ n i → p = 0 ∧ q = 1) := by
    intro i
    by_cases hi : 3 ∣ n i
    · obtain ⟨p, q, h⟩ := e6ToralB_exists_pair (hsc i hi)
      exact ⟨p, q, fun _ => h, fun h' => absurd hi h'⟩
    · exact ⟨0, 1, fun h' => absurd h' hi, fun _ => ⟨rfl, rfl⟩⟩
  choose p q hpd hpc using hpair
  obtain ⟨L₀, hL₀⟩ : ∃ L : RootModule Tag.E6 K →ₗ[K] (Fin 3 → K),
      ∀ x i, L x i = e6ToralBCoord (σ i (p i) (q i)) x :=
    ⟨LinearMap.pi fun i => e6ToralBCoord (σ i (p i) (q i)), fun _ _ => rfl⟩
  obtain ⟨L₁, hL₁⟩ : ∃ L : RootModule Tag.E6 K →ₗ[K] (Fin 3 → K),
      ∀ x i, L x i = e6ToralBCoord (σ i (q i) (p i)) x :=
    ⟨LinearMap.pi fun i => e6ToralBCoord (σ i (q i) (p i)), fun _ _ => rfl⟩
  have hTL : LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F ⊓
      LinearMap.ker L₀ ⊓ LinearMap.ker L₁ ≤
      LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ e6ToralBH K := by
    intro x hx
    obtain ⟨hx', hx1⟩ := Submodule.mem_inf.1 hx
    obtain ⟨hx'', hx0⟩ := Submodule.mem_inf.1 hx'
    obtain ⟨hxg, hxF⟩ := Submodule.mem_inf.1 hx''
    refine Submodule.mem_inf.2 ⟨hxg, e6ToralBH_of_coord fun β => ?_⟩
    have hgx : (g : Module.End K (RootModule Tag.E6 K)) x = x := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hxg
      exact hxg
    by_contra hz
    rw [← hFdef] at hxF
    have hF' : x ∈ LinearMap.ker (rootDiag (e6LineChar ω) - 1) := hxF
    rw [ker_rootDiag_sub_one, Finsupp.mem_supported] at hF'
    have hb : rootChar (e6LineChar ω) β.1 = 1 := hF' (Finsupp.mem_support_iff.2 hz)
    rw [rootChar_e6LineChar, e6Line_zpow_eq_one_iff_three_dvd hw3 hw1] at hb
    obtain ⟨i, hi⟩ := (three_dvd_iff_mem_e6LineRoots β.2).1 hb
    obtain ⟨a, b, hab, hβab⟩ := hrootsR i β.1 hi
    have hc0 : e6ToralBCoord (σ i (p i) (q i)) x = 0 := by
      rw [← hL₀]
      exact congrFun (LinearMap.mem_ker.1 hx0) i
    have hc1 : e6ToralBCoord (σ i (q i) (p i)) x = 0 := by
      rw [← hL₁]
      exact congrFun (LinearMap.mem_ker.1 hx1) i
    have hvan : ∀ a b, a ≠ b → e6ToralBCoord (σ i a b) x = 0 := by
      by_cases hn : 3 ∣ n i
      · refine e6ToralB_diag_vanish (f := fun a b => e6ToralBCoord (σ i a b) x) (hdet i) ?_
          (hpd i hn) hc0 hc1
        intro a b hab
        have h := e6ToralB_coord hWg hH ((hfr i).isRoot a b hab) ((hfr i).isRoot a b hab)
          (c := Units.mk0 (d i a / d i b) (div_ne_zero (hdet i a) (hdet i b)))
          (hdiag i hn a b hab) x
        rw [hgx] at h
        exact h
      · obtain ⟨hp0, hq1⟩ := hpc i hn
        rw [hp0, hq1] at hc0 hc1
        refine e6ToralB_cyc_vanish (f := fun a b => e6ToralBCoord (σ i a b) x) (hk12 i hn) ?_
          hc0 hc1
        intro a b hab
        have hab' : a + k i ≠ b + k i := fun h => hab (add_right_cancel h)
        obtain ⟨c', hc'⟩ := hWg _ ((hfr i).isRoot a b hab)
        rw [hWσ i a b hab] at hc'
        have h := e6ToralB_coord hWg hH ((hfr i).isRoot a b hab) ((hfr i).isRoot _ _ hab') hc' x
        rw [hgx] at h
        exact ⟨c', h⟩
    apply hz
    have h := hvan a b hab
    rw [e6ToralBCoord_apply ((hfr i).isRoot a b hab)] at h
    have hβeq : β = ⟨σ i a b, (hfr i).isRoot a b hab⟩ := Subtype.ext hβab
    rw [hβeq]
    exact h
  have hlt : LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ e6ToralBH K <
      e6ToralBH K := by
    refine lt_of_le_of_ne inf_le_right fun h => ?_
    obtain ⟨j, hj⟩ := hcart
    have hmem : hVec Tag.E6 K j ∈
        LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ e6ToralBH K := by
      rw [h]
      exact Submodule.subset_span ⟨j, rfl⟩
    apply hj
    have h' := (Submodule.mem_inf.1 hmem).1
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h'
  have h6 : Module.finrank K ↥(e6ToralBH K) ≤ 6 :=
    (finrank_range_le_card (R := K) (hVec Tag.E6 K)).trans (le_of_eq (Fintype.card_fin _))
  have c1 := e6ToralB_count (LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F) L₀
  have c2 := e6ToralB_count (LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F ⊓
    LinearMap.ker L₀) L₁
  have c3 : Module.finrank K ↥(LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓ F ⊓
      LinearMap.ker L₀ ⊓ LinearMap.ker L₁) ≤
      Module.finrank K ↥(LinearMap.ker ((g : Module.End K (RootModule Tag.E6 K)) - 1) ⊓
        e6ToralBH K) :=
    Submodule.finrank_mono hTL
  have c4 := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem e6Toral_caseB_bound {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hfr : ∀ i, IsA2Frame (ρ i) (σ i)) (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (h01 : ∀ i, σ i 0 1 = (e6LinePair i).1) (h12 : ∀ i, σ i 1 2 = (e6LinePair i).2)
    (hmono : ∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K)
    (c : Fin Tag.E6.rank → Kˣ) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (d : Fin 3 → Fin 3 → K) (n : Fin 3 → ℕ)
    (hw : ∀ i, ((diagGL3 fun j => rootChar c (σ i j 0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (w i : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d i) * signedCycMat ^ n i)
    (hcyc : ∃ i, ¬ 3 ∣ n i) (hsc : ∀ i, 3 ∣ n i → ∃ a b, d i a ≠ d i b) :
    Module.finrank K ↥(LinearMap.ker
        (((rootDiagUnit Tag.E6 c * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) - 1) ⊓
      LinearMap.ker ((rootDiagUnit Tag.E6 (e6LineChar ω) : Module.End K (RootModule Tag.E6 K)) - 1))
      ≤ 11 :=
  e6Toral_caseB_bound_of_cartan hw3 hw1 hfr hrange h01 h12 hmono c w d n hw hsc
    (e6Toral_caseB_cartan hw3 hw1 hfr hrange h01 h12 hmono c w d n hw hcyc)

end Toral

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
