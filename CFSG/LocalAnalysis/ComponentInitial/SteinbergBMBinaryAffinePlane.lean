module

public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace BinaryAffinePlane

open Matrix

@[expose] def translations (V : Type*) [AddCommGroup V] : Subgroup (Equiv.Perm V) where
  carrier := {g | ∃ b : V, ∀ x, g x = x + b}
  mul_mem' := by
    rintro σ τ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨b + a, fun x => by rw [Equiv.Perm.mul_apply, hb, ha, add_assoc]⟩
  one_mem' := ⟨0, fun x => by rw [Equiv.Perm.one_apply, add_zero]⟩
  inv_mem' := by
    rintro τ ⟨c, hc⟩
    exact ⟨-c, fun x => by rw [Equiv.Perm.inv_eq_iff_eq, hc, neg_add_cancel_right]⟩

theorem translations_props {V : Type*} [AddCommGroup V] (h2 : ∀ v : V, v + v = 0) :
    CFSG.Assembly.IsElemAbelian 2 (translations V) ∧ Nat.card (translations V) = Nat.card V ∧
      ∀ x y : V, ∃! τ : Equiv.Perm V, τ ∈ translations V ∧ τ x = y := by
  refine ⟨⟨⟨⟨fun σ τ => Subtype.ext (Equiv.ext fun x => ?_)⟩⟩, fun σ hσ => ?_⟩, ?_, fun x y => ?_⟩
  · obtain ⟨a, ha⟩ := σ.2
    obtain ⟨b, hb⟩ := τ.2
    change σ.1 (τ.1 x) = τ.1 (σ.1 x)
    rw [ha, hb, ha, hb, add_assoc, add_assoc, add_comm a]
  · obtain ⟨a, ha⟩ := hσ
    refine Equiv.ext fun x => ?_
    rw [pow_two, Equiv.Perm.mul_apply, ha, ha, add_assoc, h2, add_zero, Equiv.Perm.one_apply]
  · refine (Nat.card_congr (Equiv.ofBijective (fun b : V => (⟨Equiv.addRight b, b, fun x => rfl⟩ :
      translations V)) ⟨fun b c h => ?_, fun τ => ?_⟩)).symm
    · have := congrArg (fun τ : translations V => (τ : Equiv.Perm V) 0) h
      simpa using this
    · obtain ⟨b, hb⟩ := τ.2
      exact ⟨b, Subtype.ext (Equiv.ext fun x => (hb x).symm)⟩
  · refine ⟨Equiv.addRight (y - x), ⟨⟨y - x, fun z => rfl⟩, by simp⟩, ?_⟩
    rintro τ ⟨⟨c, hc⟩, hτx⟩
    refine Equiv.ext fun z => ?_
    rw [hc, Equiv.coe_addRight]
    rw [hc] at hτx
    rw [← hτx, add_sub_cancel_left]

section Algebra

variable {K : Type*} [Field K]

@[expose] def e1 : Fin 2 → K := ![1, 0]

@[expose] def e2 : Fin 2 → K := ![0, 1]

omit [Field K] in
theorem perm_apply_inv {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x := by
  simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

omit [Field K] in
theorem perm_inv_apply {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x := by
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

omit [Field K] in
theorem vec_ext {x y : Fin 2 → K} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem e1_ne_zero : (e1 : Fin 2 → K) ≠ 0 := fun h => by
  have := congrFun h 0
  simp [e1] at this

@[expose] def linPermFun (M : GL (Fin 2) K) : Equiv.Perm (Fin 2 → K) where
  toFun x := (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x
  invFun x := ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem linPermFun_apply (M : GL (Fin 2) K) (x : Fin 2 → K) :
    linPermFun M x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x := rfl

@[expose] def linPerm : GL (Fin 2) K →* Equiv.Perm (Fin 2 → K) where
  toFun := linPermFun
  map_one' := Equiv.ext fun x => by
    rw [linPermFun_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  map_mul' M N := Equiv.ext fun x => by
    rw [Equiv.Perm.mul_apply, linPermFun_apply, linPermFun_apply, linPermFun_apply,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem linPerm_apply (M : GL (Fin 2) K) (x : Fin 2 → K) :
    linPerm M x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x := rfl

theorem linPerm_injective : Function.Injective (linPerm (K := K)) := by
  intro M N h
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact congrArg (fun g : Equiv.Perm (Fin 2 → K) => g v) h

@[expose] def tr (b : K) : GL (Fin 2) K :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [Matrix.one_fin_two], by
    simp [Matrix.one_fin_two]⟩

theorem tr_mulVec (b : K) (x : Fin 2 → K) :
    (tr b : Matrix (Fin 2) (Fin 2) K) *ᵥ x = ![x 0 + b * x 1, x 1] := by
  refine vec_ext ?_ ?_ <;> simp [tr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem tr_add (b c : K) : tr (b + c) = tr b * tr c := by
  refine linPerm_injective (Equiv.ext fun x => ?_)
  rw [map_mul, Equiv.Perm.mul_apply, linPerm_apply, linPerm_apply, linPerm_apply, tr_mulVec,
    tr_mulVec, tr_mulVec]
  refine vec_ext ?_ ?_ <;> simp
  ring

theorem tr_zero : tr (0 : K) = 1 := by
  refine linPerm_injective (Equiv.ext fun x => ?_)
  rw [map_one, Equiv.Perm.one_apply, linPerm_apply, tr_mulVec]
  refine vec_ext ?_ ?_ <;> simp

theorem tr_injective : Function.Injective (tr (K := K)) := by
  intro b c h
  have h' := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [tr] using h'

theorem tr_mulVec_eq_self {b : K} (hb : b ≠ 0) (x : Fin 2 → K) :
    (tr b : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x ↔ x 1 = 0 := by
  rw [tr_mulVec]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    have : b * x 1 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left hb
  · intro h
    refine vec_ext ?_ ?_ <;> simp [h]

theorem tr_mulVec_of {b : K} {x : Fin 2 → K} (hx : x 1 = 0) :
    (tr b : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x := by
  rw [tr_mulVec]
  refine vec_ext ?_ ?_ <;> simp [hx]

theorem exists_mulVec_e1 {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ M : GL (Fin 2) K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (vec_ext (by simp [h0]) (by simp [h1]))
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; v 1, 0] (by simp [h1]), ?_⟩
    refine vec_ext ?_ ?_ <;> simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [h0]), ?_⟩
    refine vec_ext ?_ ?_ <;> simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_mulVec_e1_e2 {u₁ u₂ : Fin 2 → K} (hu₁ : u₁ ≠ 0) (hu : ¬ ∃ s : K, u₂ = s • u₁) :
    ∃ N : GL (Fin 2) K, (N : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = u₁ ∧
      (N : Matrix (Fin 2) (Fin 2) K) *ᵥ e2 = u₂ := by
  have hdet : (!![u₁ 0, u₂ 0; u₁ 1, u₂ 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro hd
    apply hu
    by_cases h0 : u₁ 0 = 0
    · have h1 : u₁ 1 ≠ 0 := fun h1 => hu₁ (vec_ext (by simp [h0]) (by simp [h1]))
      have h20 : u₂ 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hd
        exact (mul_eq_zero.mp hd).resolve_right h1
      refine ⟨u₂ 1 / u₁ 1, vec_ext ?_ ?_⟩
      · simp [h0, h20]
      · simp [div_mul_cancel₀ _ h1]
    · refine ⟨u₂ 0 / u₁ 0, vec_ext ?_ ?_⟩
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination hd
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, ?_⟩ <;>
    refine vec_ext ?_ ?_ <;> simp [e1, e2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_eq_self_iff [CharP K 2] {N : GL (Fin 2) K}
    (h1 : (N : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = e1) (h2 : N * N = 1) (h3 : N ≠ 1)
    (y : Fin 2 → K) : (N : Matrix (Fin 2) (Fin 2) K) *ᵥ y = y ↔ y 1 = 0 := by
  have h00 : (N : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun h1 0
    simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : (N : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun h1 1
    simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h11 : (N : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) h2
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h10,
      zero_mul, zero_add, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at h
    have h' : ((N : Matrix (Fin 2) (Fin 2) K) 1 1 + 1) ^ 2 = 0 := by
      linear_combination h + ((N : Matrix (Fin 2) (Fin 2) K) 1 1 + 1) *
        CharTwo.two_eq_zero (R := K)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
    linear_combination this - CharTwo.two_eq_zero (R := K)
  have h01 : (N : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
    intro h01
    apply h3
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have hN : ∀ y : Fin 2 → K, (N : Matrix (Fin 2) (Fin 2) K) *ᵥ y =
      ![y 0 + (N : Matrix (Fin 2) (Fin 2) K) 0 1 * y 1, y 1] := fun y => by
    refine vec_ext ?_ ?_ <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h10, h11]
  rw [hN]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    have : (N : Matrix (Fin 2) (Fin 2) K) 0 1 * y 1 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left h01
  · intro h
    refine vec_ext ?_ ?_ <;> simp [h]

end Algebra

section Plane

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
  {F : Subgroup (Equiv.Perm (Fin 2 → K))}

omit [Fintype K] [CharP K 2] in
theorem inv_apply_of_affine {g : Equiv.Perm (Fin 2 → K)} {b : Fin 2 → K}
    {f : (Fin 2 → K) ≃+ (Fin 2 → K)} (hgf : ∀ x, g x = b + f x) (x : Fin 2 → K) :
    g⁻¹ x = f.symm (x - b) := by
  rw [Equiv.Perm.inv_eq_iff_eq, hgf, AddEquiv.apply_symm_apply, add_sub_cancel]

omit [Fintype K] [CharP K 2] in
theorem linPerm_mem (hGL : ∀ M : GL (Fin 2) K, ∃ g ∈ F, ∀ x,
    g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x) (M : GL (Fin 2) K) : linPerm M ∈ F := by
  obtain ⟨g, hg, hgM⟩ := hGL M
  rwa [show linPerm M = g from Equiv.ext fun x => (hgM x).symm]

omit [Fintype K] [CharP K 2] in
theorem exists_mem_apply_zero_e1 (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F) {c d : Fin 2 → K} (hcd : c ≠ d) :
    ∃ h ∈ F, h c = 0 ∧ h d = e1 := by
  obtain ⟨a, ha, hac⟩ := hFtr c 0
  have had : a d ≠ 0 := fun h => hcd (a.injective (hac.trans h.symm))
  obtain ⟨M, hM⟩ := exists_mulVec_e1 had
  refine ⟨linPerm M⁻¹ * a, mul_mem (hGL _) ha, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hac, linPerm_apply, Matrix.mulVec_zero]
  · rw [Equiv.Perm.mul_apply, linPerm_apply, ← hM, Matrix.mulVec_mulVec,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec]

theorem fix_line_of_mem (hq : Fintype.card K = 2 ^ n)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    {k : Equiv.Perm (Fin 2 → K)} (hk : k ∈ F) (h0 : (k⁻¹ 0) 1 = 0) (h1 : (k⁻¹ e1) 1 = 0)
    (x : Fin 2 → K) : (k⁻¹ x) 1 = 0 ↔ x 1 = 0 := by
  set P : K → Equiv.Perm (Fin 2 → K) := fun b => k * linPerm (tr b) * k⁻¹ with hP
  have hPF : ∀ b, P b ∈ F := fun b => mul_mem (mul_mem hk (hGL _)) (inv_mem hk)
  have hfix : ∀ b y, (k⁻¹ y) 1 = 0 → P b y = y := by
    intro b y hy
    simp only [hP, Equiv.Perm.mul_apply, linPerm_apply]
    rw [tr_mulVec_of hy, perm_apply_inv]
  choose M j hj hM using fun b => hΓL (P b) (hPF b) (hfix b 0 h0)
  obtain ⟨b, b', hbb', hjj⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun b => (⟨j b, hj b⟩ : Fin n)) (by rw [Fintype.card_fin, hq]; exact Nat.lt_two_pow_self)
  have hjj' : j b = j b' := congrArg Fin.val hjj
  set N : GL (Fin 2) K := M b' * (M b)⁻¹ with hNdef
  have hN : linPerm N = P b' * (P b)⁻¹ := by
    refine Equiv.ext fun z => ?_
    have h1 := hM b ((P b)⁻¹ z)
    rw [perm_apply_inv] at h1
    have h2 : ((M b)⁻¹ : GL (Fin 2) K) *ᵥ z = fun i => ((P b)⁻¹ z) i ^ 2 ^ j b := by
      calc ((M b)⁻¹ : GL (Fin 2) K) *ᵥ z = ((M b)⁻¹ : GL (Fin 2) K) *ᵥ
          ((M b : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => ((P b)⁻¹ z) i ^ 2 ^ j b) := by
            rw [← h1]
        _ = fun i => ((P b)⁻¹ z) i ^ 2 ^ j b := by
          rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rw [Equiv.Perm.mul_apply, hM b', ← hjj', ← h2, linPerm_apply, hNdef,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  set c := b' - b with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hbb'.symm
  have hQ : P b' * (P b)⁻¹ = k * linPerm (tr c) * k⁻¹ := by
    have e : tr c = tr b' * (tr b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← tr_add, hc, sub_add_cancel]
    rw [e, map_mul, map_inv]
    simp only [hP]
    group
  rw [hQ] at hN
  have hNe1 : (N : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = e1 := by
    rw [← linPerm_apply, hN, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, linPerm_apply,
      tr_mulVec_of h1, perm_apply_inv]
  have hNN : N * N = 1 := by
    refine linPerm_injective ?_
    rw [map_mul, hN, map_one]
    have e : linPerm (tr c) * linPerm (tr c) = 1 := by
      rw [← map_mul, ← tr_add, CharTwo.add_self_eq_zero, tr_zero, map_one]
    calc k * linPerm (tr c) * k⁻¹ * (k * linPerm (tr c) * k⁻¹) =
        k * (linPerm (tr c) * linPerm (tr c)) * k⁻¹ := by group
      _ = 1 := by rw [e, mul_one, mul_inv_cancel]
  have hN1 : N ≠ 1 := by
    intro h
    rw [h, map_one] at hN
    have e : linPerm (tr c) = 1 := by
      calc linPerm (tr c) = k⁻¹ * (k * linPerm (tr c) * k⁻¹) * k := by group
        _ = 1 := by rw [← hN]; group
    rw [← map_one linPerm, ← tr_zero] at e
    exact hc0 (tr_injective (linPerm_injective e))
  rw [← mulVec_eq_self_iff hNe1 hNN hN1 x, ← linPerm_apply, hN, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, linPerm_apply, ← tr_mulVec_eq_self hc0 (k⁻¹ x)]
  constructor
  · intro h
    rw [h, perm_apply_inv]
  · intro h
    calc (tr c : Matrix (Fin 2) (Fin 2) K) *ᵥ k⁻¹ x =
        k⁻¹ (k ((tr c : Matrix (Fin 2) (Fin 2) K) *ᵥ k⁻¹ x)) := (perm_inv_apply _ _).symm
      _ = k⁻¹ x := by rw [h]

theorem line_eq (hq : Fintype.card K = 2 ^ n) (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    {g g' : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) (hg' : g' ∈ F) {c d : Fin 2 → K} (hcd : c ≠ d)
    (hc : (g⁻¹ c) 1 = 0) (hd : (g⁻¹ d) 1 = 0) (hc' : (g'⁻¹ c) 1 = 0) (hd' : (g'⁻¹ d) 1 = 0)
    (x : Fin 2 → K) : (g⁻¹ x) 1 = 0 ↔ (g'⁻¹ x) 1 = 0 := by
  obtain ⟨h, hh, hc0, hde⟩ := exists_mem_apply_zero_e1 hFtr hGL hcd
  have hhc : h⁻¹ 0 = c := by rw [Equiv.Perm.inv_eq_iff_eq, hc0]
  have hhd : h⁻¹ e1 = d := by rw [Equiv.Perm.inv_eq_iff_eq, hde]
  have key : ∀ g ∈ F, (g⁻¹ c) 1 = 0 → (g⁻¹ d) 1 = 0 →
      ∀ y, (g⁻¹ (h⁻¹ y)) 1 = 0 ↔ y 1 = 0 := by
    intro g hg hc hd y
    have h' := fix_line_of_mem hq hGL hΓL (mul_mem hh hg)
      (by rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply, hhc]; exact hc)
      (by rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply, hhd]; exact hd) y
    rwa [_root_.mul_inv_rev, Equiv.Perm.mul_apply] at h'
  rw [← perm_inv_apply h x, key g hg hc hd, key g' hg' hc' hd']

omit [Fintype K] [CharP K 2] in
theorem line_linPerm {M : GL (Fin 2) K} {v : Fin 2 → K}
    (hM : (M : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = v) (x : Fin 2 → K) :
    ((linPerm M)⁻¹ x) 1 = 0 ↔ ∃ t : K, x = t • v := by
  rw [← map_inv, linPerm_apply]
  constructor
  · intro h
    set y := ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ x with hy
    refine ⟨y 0, ?_⟩
    have e : y = y 0 • e1 := vec_ext (by simp [e1]) (by simp [e1, h])
    have hx : x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ y := by
      rw [hy, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rw [hx]
    conv_lhs => rw [e]
    rw [Matrix.mulVec_smul, hM]
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, ← hM, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    simp [e1]

theorem line_eq_span (hq : Fintype.card K = 2 ^ n) (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    {g : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) {v : Fin 2 → K} (hv : v ≠ 0)
    (h0 : (g⁻¹ 0) 1 = 0) (hv' : (g⁻¹ v) 1 = 0) (x : Fin 2 → K) :
    (g⁻¹ x) 1 = 0 ↔ ∃ t : K, x = t • v := by
  obtain ⟨M, hM⟩ := exists_mulVec_e1 hv
  rw [line_eq hq hGL hΓL hFtr hg (hGL M) (Ne.symm hv) h0 hv'
    ((line_linPerm hM 0).mpr ⟨0, (zero_smul K v).symm⟩)
    ((line_linPerm hM v).mpr ⟨1, (one_smul K v).symm⟩) x, line_linPerm hM]

omit [CharP K 2] in
theorem card_filter_perm [DecidableEq K] (g : Equiv.Perm (Fin 2 → K)) :
    (Finset.univ.filter fun x : Fin 2 → K => (g⁻¹ x) 1 = 0).card = Fintype.card K := by
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun x => (g⁻¹ x.1) 0
      invFun := fun t => ⟨g ![t, 0], by simp [perm_inv_apply]⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun t => by simp [perm_inv_apply] }
  have e : ![(g⁻¹ x.1) 0, 0] = g⁻¹ x.1 := vec_ext (by simp) (by simp [x.2])
  simp only
  rw [e, perm_apply_inv]

omit [CharP K 2] in
theorem card_filter_addEquiv [DecidableEq K] (f : (Fin 2 → K) ≃+ (Fin 2 → K)) :
    (Finset.univ.filter fun x : Fin 2 → K => (f.symm x) 1 = 0).card = Fintype.card K := by
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun x => (f.symm x.1) 0
      invFun := fun t => ⟨f ![t, 0], by simp⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun t => by simp }
  have e : ![(f.symm x.1) 0, 0] = f.symm x.1 := vec_ext (by simp) (by simp [x.2])
  simp only
  rw [e, AddEquiv.apply_symm_apply]

@[expose] def slope [DecidableEq K] (x : Fin 2 → K) : Option K :=
  if x 0 = 0 then none else some (x 1 / x 0)

omit [Fintype K] [CharP K 2] in
theorem eq_smul_of_slope_eq [DecidableEq K] {x y : Fin 2 → K} (hx : x ≠ 0)
    (h : slope x = slope y) : ∃ s : K, y = s • x := by
  unfold slope at h
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := fun h1 => hx (vec_ext (by simp [hx0]) (by simp [h1]))
    by_cases hy0 : y 0 = 0
    · exact ⟨y 1 / x 1, vec_ext (by simp [hx0, hy0]) (by simp [div_mul_cancel₀ _ hx1])⟩
    · rw [ite_eq_left hx0, ite_eq_right hy0] at h
      exact absurd h (by simp)
  · by_cases hy0 : y 0 = 0
    · rw [ite_eq_right hx0, ite_eq_left hy0] at h
      exact absurd h (by simp)
    · rw [ite_eq_right hx0, ite_eq_right hy0, Option.some.injEq] at h
      refine ⟨y 0 / x 0, vec_ext (by simp [div_mul_cancel₀ _ hx0]) ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp at h ⊢
      linear_combination -h

theorem line_affine_of_not_mem (hq : Fintype.card K = 2 ^ n)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    {g : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) {b : Fin 2 → K} {f : (Fin 2 → K) ≃+ (Fin 2 → K)}
    (hgf : ∀ x, g x = b + f x) (h0 : (g⁻¹ 0) 1 ≠ 0) (y : Fin 2 → K) :
    (f.symm y) 1 = 0 ↔ ∃ t : K, y = t • f e1 := by
  classical
  have hginv := inv_apply_of_affine hgf
  set w := f e1 with hw
  have hw0 : w ≠ 0 := fun h => e1_ne_zero (f.injective (h.trans (map_zero f).symm))
  have hwD : (f.symm w) 1 = 0 := by simp [hw, e1]
  have hcontra : ∀ v : Fin 2 → K, v ≠ 0 → ∀ x x' : Fin 2 → K, x ≠ x' → (g⁻¹ x) 1 = 0 →
      (g⁻¹ x') 1 = 0 → (∃ s : K, x = s • v) → (∃ s : K, x' = s • v) → False := by
    intro v hv x x' hne hx hx' hxv hx'v
    obtain ⟨M, hM⟩ := exists_mulVec_e1 hv
    exact h0 ((line_eq hq hGL hΓL hFtr hg (hGL M) hne hx hx' ((line_linPerm hM x).mpr hxv)
      ((line_linPerm hM x').mpr hx'v) 0).mpr ((line_linPerm hM 0).mpr ⟨0, (zero_smul K v).symm⟩))
  have hne0 : ∀ x, (g⁻¹ x) 1 = 0 → x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  have hdisj : ∀ y, (f.symm y) 1 = 0 → y ≠ 0 → ∀ x, (g⁻¹ x) 1 = 0 → ¬ ∃ s : K, x = s • y := by
    rintro y hy hy0 x hx ⟨s, rfl⟩
    have hx' : (g⁻¹ (s • y + y)) 1 = 0 := by
      rw [hginv] at hx ⊢
      rw [show s • y + y - b = (s • y - b) + y by abel, map_add, Pi.add_apply, hx, hy, add_zero]
    refine hcontra y hy0 (s • y) (s • y + y) (fun h => hy0 ?_) hx hx' ⟨s, rfl⟩
      ⟨s + 1, by rw [add_smul, one_smul]⟩
    simpa using (congrArg (· - s • y) h).symm
  have hsub : ∀ y, (f.symm y) 1 = 0 → y ≠ 0 → ∃ s : K, y = s • w := by
    intro y hy hy0
    by_contra hyw
    have hslope : slope y ≠ slope w := fun h => hyw (eq_smul_of_slope_eq hw0 h.symm)
    have hcardL : (Finset.univ.filter fun x : Fin 2 → K => (g⁻¹ x) 1 = 0).card =
        Fintype.card K := card_filter_perm g
    have hle := Finset.card_le_card_of_injOn slope
      (s := Finset.univ.filter fun x : Fin 2 → K => (g⁻¹ x) 1 = 0)
      (t := (Finset.univ.erase (slope w)).erase (slope y)) ?_ ?_
    · rw [hcardL, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hslope,
        Finset.mem_univ _⟩), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_option] at hle
      have : 0 < Fintype.card K := Fintype.card_pos
      omega
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hdisj y hy hy0 x hx.2 (eq_smul_of_slope_eq hy0 h.symm),
        fun h => hdisj w hwD hw0 x hx.2 (eq_smul_of_slope_eq hw0 h.symm), Finset.mem_univ _⟩
    · intro x hx x' hx' h
      rw [Finset.mem_coe, Finset.mem_filter] at hx hx'
      replace hx := hx.2
      replace hx' := hx'.2
      by_contra hne
      exact hcontra x (hne0 x hx) x x' hne hx hx' ⟨1, (one_smul K x).symm⟩
        (eq_smul_of_slope_eq (hne0 x hx) h)
  have hDF : (Finset.univ.filter fun y => (f.symm y) 1 = 0) =
      Finset.univ.image fun t : K => t • w := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      by_cases hy0 : y = 0
      · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by rw [hy0, zero_smul]⟩
      · obtain ⟨s, hs⟩ := hsub y hy hy0
        exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.symm⟩
    · have hcardD : (Finset.univ.filter fun y : Fin 2 → K => (f.symm y) 1 = 0).card =
          Fintype.card K := card_filter_addEquiv f
      rw [Finset.card_image_of_injective _ (smul_left_injective K hw0), Finset.card_univ,
        hcardD]
  have := Finset.ext_iff.mp hDF y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at this
  rw [this]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem line_affine (hq : Fintype.card K = 2 ^ n)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    {g : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) {b : Fin 2 → K} {f : (Fin 2 → K) ≃+ (Fin 2 → K)}
    (hgf : ∀ x, g x = b + f x) (y : Fin 2 → K) :
    (f.symm y) 1 = 0 ↔ ∃ t : K, y = t • f e1 := by
  by_cases h0 : (g⁻¹ 0) 1 = 0
  · have hginv := inv_apply_of_affine hgf
    have hb : (f.symm b) 1 = 0 := by
      rw [hginv, zero_sub, map_neg, Pi.neg_apply, neg_eq_zero] at h0
      exact h0
    have hL : ∀ x, (g⁻¹ x) 1 = 0 ↔ (f.symm x) 1 = 0 := fun x => by
      rw [hginv, map_sub, Pi.sub_apply, hb, sub_zero]
    have hw0 : f e1 ≠ 0 := fun h => e1_ne_zero (f.injective (h.trans (map_zero f).symm))
    rw [← hL, line_eq_span hq hGL hΓL hFtr hg hw0 h0 ((hL _).mpr (by simp [e1]))]
  · exact line_affine_of_not_mem hq hGL hΓL hFtr hg hgf h0 y

theorem linear_part_smul (hq : Fintype.card K = 2 ^ n)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    {g : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) {b : Fin 2 → K} {f : (Fin 2 → K) ≃+ (Fin 2 → K)}
    (hgf : ∀ x, g x = b + f x) {v : Fin 2 → K} (hv : v ≠ 0) (t : K) :
    ∃ s : K, f (t • v) = s • f v := by
  obtain ⟨M, hM⟩ := exists_mulVec_e1 hv
  let fM : (Fin 2 → K) ≃+ (Fin 2 → K) :=
    { linPerm M with
      map_add' := fun x y => Matrix.mulVec_add (M : Matrix (Fin 2) (Fin 2) K) x y }
  have hfM : ∀ x, fM x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x := fun x => rfl
  have h := line_affine hq hGL hΓL hFtr (mul_mem hg (hGL M)) (b := b) (f := fM.trans f)
    (fun x => by rw [Equiv.Perm.mul_apply, hgf, linPerm_apply, AddEquiv.trans_apply, hfM])
    (f (t • v))
  have e : (fM.trans f).symm (f (t • v)) = t • e1 := by
    rw [AddEquiv.symm_trans_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_eq, hfM,
      Matrix.mulVec_smul, hM]
  obtain ⟨s, hs⟩ := h.mp (by rw [e]; simp [e1])
  exact ⟨s, by rw [hs, AddEquiv.trans_apply, hfM, hM]⟩

omit [Fintype K] [CharP K 2] in
theorem normal_form {h : (Fin 2 → K) →+ (Fin 2 → K)} (h1 : h e1 = e1) (h2 : h e2 = e2)
    (hl : ∀ v : Fin 2 → K, v ≠ 0 → ∀ t : K, ∃ s : K, h (t • v) = s • h v) :
    (∀ x, h x = ![(h (x 0 • e1)) 0, (h (x 1 • e1)) 0]) ∧
      ∀ s t : K, (h ((s * t) • e1)) 0 = (h (s • e1)) 0 * (h (t • e1)) 0 := by
  set σ : K → K := fun t => (h (t • e1)) 0 with hσ
  have hA : ∀ t, h (t • e1) = ![σ t, 0] := by
    intro t
    obtain ⟨s, hs⟩ := hl e1 e1_ne_zero t
    rw [h1] at hs
    refine vec_ext (by simp [hσ]) ?_
    rw [hs]
    simp [e1]
  have he2 : (e2 : Fin 2 → K) ≠ 0 := fun h => by
    have := congrFun h 1
    simp [e2] at this
  set τ : K → K := fun t => (h (t • e2)) 1 with hτ
  have hB : ∀ t, h (t • e2) = ![0, τ t] := by
    intro t
    obtain ⟨s, hs⟩ := hl e2 he2 t
    rw [h2] at hs
    refine vec_ext ?_ (by simp [hτ])
    rw [hs]
    simp [e2]
  have hsplit : ∀ x : Fin 2 → K, x = x 0 • e1 + x 1 • e2 := fun x =>
    vec_ext (by simp [e1, e2]) (by simp [e1, e2])
  have hdiag : ∀ t, τ t = σ t := by
    intro t
    have hv : (e1 + e2 : Fin 2 → K) ≠ 0 := fun h => by
      have := congrFun h 0
      simp [e1, e2] at this
    obtain ⟨s, hs⟩ := hl _ hv t
    rw [smul_add, map_add, map_add, hA, hB, h1, h2] at hs
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    simp [e1, e2] at hs0 hs1
    rw [hs0, hs1]
  have hform : ∀ x, h x = ![σ (x 0), σ (x 1)] := by
    intro x
    conv_lhs => rw [hsplit x]
    rw [map_add, hA, hB, hdiag]
    refine vec_ext ?_ ?_ <;> simp
  refine ⟨hform, fun s t => ?_⟩
  have hσ1 : σ 1 = 1 := by
    change (h ((1 : K) • e1)) 0 = 1
    rw [one_smul, h1]
    simp [e1]
  have hv : (![1, t] : Fin 2 → K) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  obtain ⟨r, hr⟩ := hl _ hv s
  rw [hform, hform] at hr
  have hr0 := congrFun hr 0
  have hr1 := congrFun hr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, hσ1] at hr0 hr1
  change σ (s * t) = σ s * σ t
  rw [hr1, ← hr0]

omit [CharP K 2] in
theorem eq_of_mul {σ σ' : K → K} (hσ : ∀ s t, σ (s * t) = σ s * σ t)
    (hσ' : ∀ s t, σ' (s * t) = σ' s * σ' t) (h1 : σ 1 = 1) (h1' : σ' 1 = 1) (h0 : σ 0 = 0)
    (h0' : σ' 0 = 0) {α : Kˣ} (hα : ∀ x : Kˣ, x ∈ Subgroup.zpowers α) (h : σ α = σ' α) :
    σ = σ' := by
  have hpow : ∀ (σ : K → K), (∀ s t, σ (s * t) = σ s * σ t) → σ 1 = 1 →
      ∀ m : ℕ, σ ((α : K) ^ m) = σ α ^ m := by
    intro σ hσ h1 m
    induction m with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ m ih => rw [pow_succ, hσ, ih, pow_succ]
  funext t
  by_cases ht : t = 0
  · rw [ht, h0, h0']
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr (hα (Units.mk0 t ht)))
  have hm' : (α : K) ^ m = t := by
    have := congrArg Units.val hm
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at this
  rw [← hm', hpow σ hσ h1, hpow σ' hσ' h1', h]

theorem card_le_of_no_translations (hq : Fintype.card K = 2 ^ n)
    (hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    (hnoT : ∀ g ∈ F, ∀ c : Fin 2 → K, (∀ x, g x = x + c) → c = 0) :
    Nat.card F ≤ Nat.card (GL (Fin 2) K) * Fintype.card K := by
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hdata : ∀ g : F, ∃ N : GL (Fin 2) K, ∃ σ : K → K, (∀ s t, σ (s * t) = σ s * σ t) ∧
      σ 1 = 1 ∧ σ 0 = 0 ∧ ∀ x, (g : Equiv.Perm (Fin 2 → K)) x =
        (g : Equiv.Perm (Fin 2 → K)) 0 + (N : Matrix (Fin 2) (Fin 2) K) *ᵥ ![σ (x 0), σ (x 1)] := by
    intro g
    obtain ⟨b, f, hgf⟩ := hFA g g.2
    have hb : b = (g : Equiv.Perm (Fin 2 → K)) 0 := by rw [hgf, map_zero, add_zero]
    have hu1 : f e1 ≠ 0 := fun h => e1_ne_zero (f.injective (h.trans (map_zero f).symm))
    have hu : ¬ ∃ s : K, f e2 = s • f e1 := fun hs => by
      have := (line_affine hq hGL hΓL hFtr g.2 hgf (f e2)).mpr hs
      simp [e2] at this
    obtain ⟨N, hN1, hN2⟩ := exists_mulVec_e1_e2 hu1 hu
    let h : (Fin 2 → K) →+ (Fin 2 → K) :=
      { toFun := fun x => ((N⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ f x
        map_zero' := by rw [map_zero, Matrix.mulVec_zero]
        map_add' := fun x y => by rw [map_add, Matrix.mulVec_add] }
    have hhx : ∀ x, h x = ((N⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ f x :=
      fun x => rfl
    have hNinv : ∀ y, ((N⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        ((N : Matrix (Fin 2) (Fin 2) K) *ᵥ y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hNh : ∀ x, (N : Matrix (Fin 2) (Fin 2) K) *ᵥ h x = f x := fun x => by
      rw [hhx, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have h1 : h e1 = e1 := by rw [hhx, ← hN1, hNinv]
    have h2 : h e2 = e2 := by rw [hhx, ← hN2, hNinv]
    have hl : ∀ v : Fin 2 → K, v ≠ 0 → ∀ t : K, ∃ s : K, h (t • v) = s • h v := by
      intro v hv t
      obtain ⟨s, hs⟩ := linear_part_smul hq hGL hΓL hFtr g.2 hgf hv t
      exact ⟨s, by rw [hhx, hhx, hs, Matrix.mulVec_smul]⟩
    obtain ⟨hform, hmul⟩ := normal_form h1 h2 hl
    refine ⟨N, fun t => (h (t • e1)) 0, hmul, ?_, ?_, fun x => ?_⟩
    · simp only [one_smul, h1]
      simp [e1]
    · simp only [zero_smul, map_zero, Pi.zero_apply]
    · rw [hgf, ← hb, ← hNh x, hform x]
  choose N σ hσmul hσ1 hσ0 hform using hdata
  have hinj : Function.Injective fun g : F => (N g, σ g α) := by
    intro g g' hgg'
    simp only [Prod.mk.injEq] at hgg'
    obtain ⟨hN, hσα⟩ := hgg'
    have hσ : σ g = σ g' :=
      eq_of_mul (hσmul g) (hσmul g') (hσ1 g) (hσ1 g') (hσ0 g) (hσ0 g') hα hσα
    have hT : ∀ x, ((g' : Equiv.Perm (Fin 2 → K)) * (g : Equiv.Perm (Fin 2 → K))⁻¹) x =
        x + ((g' : Equiv.Perm (Fin 2 → K)) 0 - (g : Equiv.Perm (Fin 2 → K)) 0) := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y, (g : Equiv.Perm (Fin 2 → K)) y = x :=
        ⟨(g : Equiv.Perm (Fin 2 → K))⁻¹ x, perm_apply_inv _ _⟩
      rw [Equiv.Perm.mul_apply, perm_inv_apply, hform g' y, hform g y, hN, hσ]
      abel
    have hc := hnoT _ (mul_mem g'.2 (inv_mem g.2)) _ hT
    refine Subtype.ext (Equiv.ext fun x => ?_)
    rw [hform g x, hform g' x, hN, hσ, sub_eq_zero.mp hc]
  calc Nat.card F ≤ Nat.card (GL (Fin 2) K × K) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (GL (Fin 2) K) * Fintype.card K := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := K)]

omit [CharP K 2] in
theorem card_ge (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F) :
    Fintype.card K ^ 2 * Nat.card (GL (Fin 2) K) ≤ Nat.card F := by
  choose a ha hav using fun v : Fin 2 → K => hFtr 0 v
  have hinj : Function.Injective fun p : (Fin 2 → K) × GL (Fin 2) K =>
      (⟨a p.1 * linPerm p.2, mul_mem (ha p.1) (hGL p.2)⟩ : F) := by
    rintro ⟨v, M⟩ ⟨v', M'⟩ h
    simp only [Subtype.mk.injEq] at h
    have hv : v = v' := by
      have := congrArg (fun g : Equiv.Perm (Fin 2 → K) => g 0) h
      simp only [Equiv.Perm.mul_apply, linPerm_apply, Matrix.mulVec_zero, hav] at this
      exact this
    subst hv
    rw [linPerm_injective (mul_left_cancel h)]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2 → K), Fintype.card_fun,
    Fintype.card_fin] at this

theorem translations_le (hn : 2 ≤ n) (hq : Fintype.card K = 2 ^ n)
    (hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y) :
    translations (Fin 2 → K) ≤ F := by
  by_cases hT : ∃ g ∈ F, ∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ x, g x = x + c
  · obtain ⟨g, hg, c, hc, hgc⟩ := hT
    rintro τ ⟨d, hd⟩
    by_cases hd0 : d = 0
    · rw [show τ = 1 from Equiv.ext fun x => by rw [hd, hd0, add_zero, Equiv.Perm.one_apply]]
      exact one_mem _
    obtain ⟨Mc, hMc⟩ := exists_mulVec_e1 hc
    obtain ⟨Md, hMd⟩ := exists_mulVec_e1 hd0
    have hc1 : ((Mc⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ c = e1 := by
      rw [← hMc, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hMcd : ((Md * Mc⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ c = d := by
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hc1, hMd]
    have hτ : τ = linPerm (Md * Mc⁻¹) * g * (linPerm (Md * Mc⁻¹))⁻¹ := by
      refine Equiv.ext fun x => ?_
      rw [hd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgc, linPerm_apply, Matrix.mulVec_add,
        hMcd, ← linPerm_apply, perm_apply_inv]
    rw [hτ]
    exact mul_mem (mul_mem (hGL _) hg) (inv_mem (hGL _))
  · exfalso
    have hnoT : ∀ g ∈ F, ∀ c : Fin 2 → K, (∀ x, g x = x + c) → c = 0 := fun g hg c hgc =>
      by_contra fun hc => hT ⟨g, hg, c, hc, hgc⟩
    have h1 := card_le_of_no_translations hq hFA hGL hΓL hFtr hnoT
    have h2 := card_ge hFtr hGL
    have hGLpos : 0 < Nat.card (GL (Fin 2) K) := Nat.card_pos
    have hq4 : 4 ≤ Fintype.card K := by
      rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : Fintype.card K ^ 2 * Nat.card (GL (Fin 2) K) ≤
        Fintype.card K * Nat.card (GL (Fin 2) K) := by
      rw [mul_comm (Fintype.card K)]
      exact h2.trans h1
    have h4 := Nat.le_of_mul_le_mul_right h3 hGLpos
    nlinarith

omit [Fintype K] [CharP K 2] in
theorem conj_mem_translations
    (hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x)
    {k τ : Equiv.Perm (Fin 2 → K)} (hk : k ∈ F) (hτ : τ ∈ translations (Fin 2 → K)) :
    k * τ * k⁻¹ ∈ translations (Fin 2 → K) := by
  obtain ⟨b, f, hkf⟩ := hFA k hk
  obtain ⟨c, hc⟩ := hτ
  refine ⟨f c, fun x => ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hc, hkf, map_add, ← add_assoc, ← hkf,
    perm_apply_inv]

omit [CharP K 2] in
theorem eq_bot_of_isPGroup (hn : 2 ≤ n) (hq : Fintype.card K = 2 ^ n)
    {R : Subgroup (Equiv.Perm (Fin 2 → K))} (hR : IsPGroup 2 R) (h0 : ∀ r ∈ R, r 0 = 0)
    (hnorm : ∀ M : GL (Fin 2) K, ∀ r ∈ R, linPerm M * r * (linPerm M)⁻¹ ∈ R) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hR.card_modEq_card_fixedPoints (Fin 2 → K)
  have hV : Nat.card (Fin 2 → K) % 2 = 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hq, ← pow_mul]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  obtain ⟨v, hvfix, hv0⟩ : ∃ v ∈ MulAction.fixedPoints R (Fin 2 → K), v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hfix : MulAction.fixedPoints R (Fin 2 → K) = {0} := by
      ext v
      refine ⟨fun hv => hcon v hv, fun hv => ?_⟩
      rw [Set.mem_singleton_iff.mp hv]
      intro r
      exact h0 r r.2
    rw [hfix, Nat.card_coe_set_eq, Set.ncard_singleton, Nat.ModEq, hV] at hmod
    norm_num at hmod
  have hall : ∀ r ∈ R, ∀ w, r w = w := by
    intro r hr w
    by_cases hw : w = 0
    · rw [hw]
      exact h0 r hr
    obtain ⟨Mv, hMv⟩ := exists_mulVec_e1 hv0
    obtain ⟨Mw, hMw⟩ := exists_mulVec_e1 hw
    have hv1 : ((Mv⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = e1 := by
      rw [← hMv, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hM : ((Mw * Mv⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = w := by
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hv1, hMw]
    have hr' : (linPerm (Mw * Mv⁻¹))⁻¹ * r * linPerm (Mw * Mv⁻¹) ∈ R := by
      have := hnorm (Mw * Mv⁻¹)⁻¹ r hr
      rwa [map_inv, inv_inv] at this
    have hfixv := hvfix ⟨_, hr'⟩
    rw [Subgroup.mk_smul, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      linPerm_apply, hM, Equiv.Perm.inv_eq_iff_eq, linPerm_apply, hM] at hfixv
    exact hfixv
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  exact Equiv.ext (hall r hr)

theorem pCoreOf_eq (hn : 2 ≤ n) (hq : Fintype.card K = 2 ^ n)
    (hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x)
    (hGL : ∀ M : GL (Fin 2) K, linPerm M ∈ F) (hTF : translations (Fin 2 → K) ≤ F) :
    CFSG.Assembly.pCoreOf 2 F = translations (Fin 2 → K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' := (translations (Fin 2 → K)).subgroupOf F with hT'
  have hT'n : T'.Normal := (Subgroup.normal_subgroupOf_iff hTF).mpr fun h k hh hk =>
    conj_mem_translations hFA hk hh
  have hT'2 : IsPGroup 2 T' := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext (Equiv.ext fun y => ?_))⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp x.2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_two, Equiv.Perm.mul_apply, hc, hc, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Equiv.Perm.one_apply]
  unfold CFSG.Assembly.pCoreOf
  rw [CFSG.pCore_eq_iSup]
  apply le_antisymm
  · rw [← Subgroup.map_subgroupOf_eq_of_le hTF]
    refine Subgroup.map_mono (iSup_le fun N => iSup_le fun hN => iSup_le fun hN2 => ?_)
    intro m hm
    have := hN
    have := hT'n
    have hQ2 : IsPGroup 2 ↥(N ⊔ T') := IsPGroup.to_sup_of_normal_right hN2 hT'2
    have hQn : (N ⊔ T').Normal := Subgroup.sup_normal N T'
    set R : Subgroup (Equiv.Perm (Fin 2 → K)) := ((N ⊔ T').map F.subtype) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 2 → K)) (0 : Fin 2 → K) with hR
    have hR2 : IsPGroup 2 R := (hQ2.map F.subtype).to_le inf_le_left
    have hR0 : ∀ r ∈ R, r 0 = 0 := fun r hr => by
      have := (Subgroup.mem_inf.mp hr).2
      rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this
    have hRn : ∀ M : GL (Fin 2) K, ∀ r ∈ R, linPerm M * r * (linPerm M)⁻¹ ∈ R := by
      intro M r hr
      obtain ⟨⟨q, hqQ, rfl⟩, -⟩ := Subgroup.mem_inf.mp hr
      have hq0 := hR0 _ hr
      refine Subgroup.mem_inf.mpr ⟨⟨⟨linPerm M, hGL M⟩ * q * ⟨linPerm M, hGL M⟩⁻¹,
        hQn.conj_mem q hqQ _, rfl⟩, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, show (linPerm M)⁻¹ 0 = 0 from
          Equiv.Perm.inv_eq_iff_eq.mpr (by rw [linPerm_apply, Matrix.mulVec_zero]), hq0,
        linPerm_apply, Matrix.mulVec_zero]
    have hRbot := eq_bot_of_isPGroup hn hq hR2 hR0 hRn
    set b := (m : Equiv.Perm (Fin 2 → K)) 0 with hb
    have hτ : Equiv.addRight b ∈ translations (Fin 2 → K) := ⟨b, fun x => rfl⟩
    have hτT' : (⟨Equiv.addRight b, hTF hτ⟩ : F) ∈ T' := Subgroup.mem_subgroupOf.mpr hτ
    have hmem : (((⟨Equiv.addRight b, hTF hτ⟩ : F)⁻¹ * m : F) : Equiv.Perm (Fin 2 → K)) ∈ R := by
      refine Subgroup.mem_inf.mpr ⟨⟨_, mul_mem (Subgroup.mem_sup_right (inv_mem hτT'))
        (Subgroup.mem_sup_left hm), rfl⟩, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      change (Equiv.addRight b)⁻¹ ((m : Equiv.Perm (Fin 2 → K)) 0) = 0
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (zero_add _).symm
    rw [hRbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨Equiv.addRight b, hTF hτ⟩ : F)⁻¹ * m = 1 := Subtype.ext hmem
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hτT'
  · rw [← Subgroup.map_subgroupOf_eq_of_le hTF]
    exact Subgroup.map_mono (le_iSup_of_le T' (le_iSup_of_le hT'n (le_iSup_of_le hT'2 le_rfl)))

omit [Fintype K] [CharP K 2] in
theorem isComplement (hTF : translations (Fin 2 → K) ≤ F) :
    ((translations (Fin 2 → K)).subgroupOf F).IsComplement'
      ((F ⊓ MulAction.stabilizer (Equiv.Perm (Fin 2 → K)) (0 : Fin 2 → K)).subgroupOf F) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxT hx0
    rw [Subgroup.mem_subgroupOf] at hxT hx0
    obtain ⟨c, hc⟩ := hxT
    have h0 : (x : Equiv.Perm (Fin 2 → K)) 0 = 0 := by
      have := (Subgroup.mem_inf.mp hx0).2
      rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this
    rw [hc, zero_add] at h0
    exact Subtype.ext (Equiv.ext fun y => by rw [hc, h0, add_zero]; rfl)
  · ext g
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    set b := (g : Equiv.Perm (Fin 2 → K)) 0 with hb
    have hτ : Equiv.addRight b ∈ translations (Fin 2 → K) := ⟨b, fun x => rfl⟩
    refine ⟨⟨Equiv.addRight b, hTF hτ⟩, Subgroup.mem_subgroupOf.mpr hτ,
      (⟨Equiv.addRight b, hTF hτ⟩ : F)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨((⟨Equiv.addRight b, hTF hτ⟩ : F)⁻¹ * g : F).2, ?_⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    change (Equiv.addRight b)⁻¹ ((g : Equiv.Perm (Fin 2 → K)) 0) = 0
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (zero_add _).symm

omit [Fintype K] [CharP K 2] in
theorem semilinear
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k)
    (hTF : translations (Fin 2 → K) ≤ F) {g : Equiv.Perm (Fin 2 → K)} (hg : g ∈ F) :
    ∃ (b : Fin 2 → K) (M : GL (Fin 2) K), ∃ k < n, ∀ x,
      g x = b + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k := by
  set b := g 0 with hb
  have hτ : Equiv.addRight b ∈ F := hTF ⟨b, fun x => rfl⟩
  obtain ⟨M, k, hk, hM⟩ := hΓL ((Equiv.addRight b)⁻¹ * g) (mul_mem (inv_mem hτ) hg) (by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact (zero_add _).symm)
  refine ⟨b, M, k, hk, fun x => ?_⟩
  have h := hM x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at h
  rw [h, add_comm]
  rfl

end Plane

end BinaryAffinePlane

open BinaryAffinePlane Matrix in
theorem binary_affine_plane_semilinear_stabilizer_normal_translations {K : Type*} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hq : Nat.card K = 2 ^ n)
    (F : Subgroup (Equiv.Perm (Fin 2 → K)))
    (hFA : ∀ g ∈ F, ∃ (b : Fin 2 → K) (f : (Fin 2 → K) ≃+ (Fin 2 → K)), ∀ x, g x = b + f x)
    (hFtr : ∀ x y : Fin 2 → K, ∃ g ∈ F, g x = y)
    (hGL : ∀ M : GL (Fin 2) K, ∃ g ∈ F, ∀ x, g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ x)
    (hΓL : ∀ g ∈ F, g 0 = 0 → ∃ M : GL (Fin 2) K, ∃ k < n, ∀ x,
      g x = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k) :
    translations (Fin 2 → K) ≤ F ∧
    CFSG.Assembly.pCoreOf 2 F = translations (Fin 2 → K) ∧
    ((translations (Fin 2 → K)).subgroupOf F).Normal ∧
    ((translations (Fin 2 → K)).subgroupOf F).IsComplement'
      ((F ⊓ MulAction.stabilizer (Equiv.Perm (Fin 2 → K)) (0 : Fin 2 → K)).subgroupOf F) ∧
    (CFSG.Assembly.IsElemAbelian 2 (translations (Fin 2 → K)) ∧
      Nat.card (translations (Fin 2 → K)) = Nat.card K ^ 2 ∧
      ∀ x y : Fin 2 → K, ∃! τ : Equiv.Perm (Fin 2 → K), τ ∈ translations (Fin 2 → K) ∧ τ x = y) ∧
    ∀ g ∈ F, ∃ (b : Fin 2 → K) (M : GL (Fin 2) K), ∃ k < n, ∀ x,
      g x = b + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => x i ^ 2 ^ k := by
  have := Fintype.ofFinite K
  have hq' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hq]
  have hGL' := linPerm_mem hGL
  have hTF := translations_le hn hq' hFA hGL' hΓL hFtr
  obtain ⟨hEA, hcard, hreg⟩ := translations_props (V := Fin 2 → K) fun v =>
    CharTwo.add_self_eq_zero v
  refine ⟨hTF, pCoreOf_eq hn hq' hFA hGL' hTF,
    (Subgroup.normal_subgroupOf_iff hTF).mpr fun h k hh hk => conj_mem_translations hFA hk hh,
    isComplement hTF, ⟨hEA, ?_, hreg⟩, fun g hg => semilinear hΓL hTF hg⟩
  rw [hcard, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

end CFSG.LocalAnalysis.ComponentInitial
