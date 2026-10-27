module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Std
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfNondeg
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

@[expose] noncomputable def cs {α : Type*} (f : α → ZMod 2) : ℤ := ∑ᶠ a, (-1 : ℤ) ^ (f a).val

theorem cs_eq_sum {α : Type*} [Fintype α] (f : α → ZMod 2) :
    cs f = ∑ a, (-1 : ℤ) ^ (f a).val := finsum_eq_sum_of_fintype _

theorem cs_equiv {α β : Type*} (e : α ≃ β) (f : α → ZMod 2) (g : β → ZMod 2)
    (h : ∀ a, g (e a) = f a) : cs f = cs g := by
  unfold cs
  rw [← finsum_comp_equiv e]
  simp [h]

theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℤ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  revert a b; decide

theorem cs_prod {α β : Type*} [Finite α] [Finite β] (f : α → ZMod 2) (g : β → ZMod 2)
    (h : α × β → ZMod 2) (hh : ∀ x, h x = f x.1 + g x.2) : cs h = cs f * cs g := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [cs_eq_sum, cs_eq_sum, cs_eq_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hh, neg_one_pow_val_add]

theorem cs_hyp : cs (fun x : ZMod 2 × ZMod 2 => x.1 * x.2) = 2 := by
  rw [cs_eq_sum]; decide

theorem cs_aniso : cs (fun x : ZMod 2 × ZMod 2 => x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2) = -2 := by
  rw [cs_eq_sum]; decide


section Coord

variable {K : Type*} [Field K]

@[expose] def Eplus (K : Type*) [Field K] (j : ℕ) :
    ((K × K) × (Fin j ⊕ Fin j → K)) ≃ₗ[K] (Fin (j + 1) ⊕ Fin (j + 1) → K) where
  toFun x := fun s => Sum.elim (fun i => (Fin.cons x.1.1 (fun l => x.2 (.inl l)) : Fin (j+1) → K) i)
    (fun i => (Fin.cons x.1.2 (fun l => x.2 (.inr l)) : Fin (j+1) → K) i) s
  map_add' x y := by
    funext s
    rcases s with i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
  map_smul' c x := by
    funext s
    rcases s with i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
  invFun v := ((v (.inl 0), v (.inr 0)),
    fun s => Sum.elim (fun l => v (.inl l.succ)) (fun l => v (.inr l.succ)) s)
  left_inv x := by
    obtain ⟨⟨a, b⟩, y⟩ := x
    ext s <;> simp
    rcases s with l | l <;> simp
  right_inv v := by
    funext s
    rcases s with i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp

theorem quadPlus_Eplus (j : ℕ) (x : (K × K) × (Fin j ⊕ Fin j → K)) :
    quadPlus (j + 1) K (Eplus K j x) = x.1.1 * x.1.2 + quadPlus j K x.2 := by
  simp [quadPlus_apply, Fin.sum_univ_succ, Eplus]

@[expose] def Eminus (K : Type*) [Field K] (j : ℕ) :
    ((K × K) × (Fin j ⊕ Fin j ⊕ Fin 2 → K)) ≃ₗ[K] (Fin (j + 1) ⊕ Fin (j + 1) ⊕ Fin 2 → K) where
  toFun x := fun s => Sum.elim (fun i => (Fin.cons x.1.1 (fun l => x.2 (.inl l)) : Fin (j+1) → K) i)
    (Sum.elim (fun i => (Fin.cons x.1.2 (fun l => x.2 (.inr (.inl l))) : Fin (j+1) → K) i)
      (fun i => x.2 (.inr (.inr i)))) s
  map_add' x y := by
    funext s
    rcases s with i | i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · simp
  map_smul' c x := by
    funext s
    rcases s with i | i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · simp
  invFun v := ((v (.inl 0), v (.inr (.inl 0))),
    fun s => Sum.elim (fun l => v (.inl l.succ))
      (Sum.elim (fun l => v (.inr (.inl l.succ))) (fun l => v (.inr (.inr l)))) s)
  left_inv x := by
    obtain ⟨⟨a, b⟩, y⟩ := x
    ext s <;> simp
    rcases s with l | l | l <;> simp
  right_inv v := by
    funext s
    rcases s with i | i | i
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · refine Fin.cases ?_ (fun l => ?_) i <;> simp
    · simp

theorem quadMinus_Eminus (j : ℕ) (b c : K) (x : (K × K) × (Fin j ⊕ Fin j ⊕ Fin 2 → K)) :
    quadMinus (j + 2) K b c (Eminus K j x) = x.1.1 * x.1.2 + quadMinus (j + 1) K b c x.2 := by
  rw [quadMinus_apply (j + 2) K b c, quadMinus_apply (j + 1) K b c]
  simp [Fin.sum_univ_succ, Eminus]
  ring

@[expose] def eMinusBase (K : Type*) [Field K] :
    (Fin 0 ⊕ Fin 0 ⊕ Fin 2 → K) ≃ₗ[K] (K × K) where
  toFun v := (v (.inr (.inr 0)), v (.inr (.inr 1)))
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun p := fun s => Sum.elim (fun i => i.elim0) (Sum.elim (fun i => i.elim0) (fun i => ![p.1, p.2] i)) s
  left_inv v := by
    funext s
    rcases s with i | i | i
    · exact i.elim0
    · exact i.elim0
    · fin_cases i <;> rfl
  right_inv p := by simp

theorem quadMinus_one_eMinusBase (b c : K) (v : Fin 0 ⊕ Fin 0 ⊕ Fin 2 → K) :
    quadMinus 1 K b c v =
      (eMinusBase K v).1 ^ 2 + b * (eMinusBase K v).1 * (eMinusBase K v).2
        + c * (eMinusBase K v).2 ^ 2 := by
  rw [quadMinus_apply 1 K b c]
  simp [eMinusBase]


end Coord

theorem cs_quadPlus (m : ℕ) : cs (quadPlus m (ZMod 2)) = 2 ^ m := by
  induction m with
  | zero => rw [cs_eq_sum]; simp [quadPlus_apply]
  | succ j ih =>
    have := cs_equiv (Eplus (ZMod 2) j).toEquiv
      (fun x => x.1.1 * x.1.2 + quadPlus j (ZMod 2) x.2) (quadPlus (j + 1) (ZMod 2))
      (fun x => quadPlus_Eplus j x)
    rw [← this, cs_prod (fun p : ZMod 2 × ZMod 2 => p.1 * p.2) (quadPlus j (ZMod 2)) _
      (fun x => rfl), cs_hyp, ih, pow_succ]
    ring

theorem cs_quadMinus (k : ℕ) : cs (quadMinus (k + 1) (ZMod 2) 1 1) = -2 ^ (k + 1) := by
  induction k with
  | zero =>
    have := cs_equiv (eMinusBase (ZMod 2)).toEquiv
      (quadMinus 1 (ZMod 2) 1 1) (fun x : ZMod 2 × ZMod 2 => x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2)
      (fun v => by rw [quadMinus_one_eMinusBase]; simp)
    rw [this, cs_aniso]; norm_num
  | succ j ih =>
    have := cs_equiv (Eminus (ZMod 2) j).toEquiv
      (fun x => x.1.1 * x.1.2 + quadMinus (j + 1) (ZMod 2) 1 1 x.2)
      (quadMinus (j + 2) (ZMod 2) 1 1) (fun x => quadMinus_Eminus j 1 1 x)
    rw [← this]
    refine (cs_prod (fun p : ZMod 2 × ZMod 2 => p.1 * p.2) (quadMinus (j + 1) (ZMod 2) 1 1) _
      (fun x => rfl)).trans ?_
    rw [cs_hyp, ih, pow_succ]
    ring


section Split

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def hypSplit (P : HypPair Q) : V ≃ₗ[K] (K × K) × P.perp where
  toFun v := ((polar Q v P.f, polar Q v P.e), ⟨P.proj v, P.proj_mem_perp v⟩)
  map_add' x y := by
    ext
    · simp [HypPair.proj, polar_add_left]
    · simp [HypPair.proj, polar_add_left]
    · simp [HypPair.proj, polar_add_left, add_smul]
      abel
  map_smul' c x := by
    ext <;> simp [HypPair.proj, smul_sub, smul_smul]
  invFun p := p.1.1 • P.e + p.1.2 • P.f + (p.2 : V)
  left_inv v := (P.eq_add_proj v).symm
  right_inv p := by
    obtain ⟨⟨a, b⟩, u, hu⟩ := p
    rw [HypPair.mem_perp] at hu
    have h1 : polar Q u P.f = 0 := by rw [polar_comm]; exact hu.2
    have h2 : polar Q u P.e = 0 := by rw [polar_comm]; exact hu.1
    ext
    · simp [polar_add_left, h1, P.polar_ef, P.polar_ff]
    · simp [polar_add_left, h2, P.polar_ee, P.polar_fe]
    · simp [HypPair.proj, polar_add_left, h1, h2, P.polar_ef, P.polar_ee,
        P.polar_ff, P.polar_fe]
      abel

theorem hypSplit_apply (P : HypPair Q) (v : V) :
    hypSplit P v = ((polar Q v P.f, polar Q v P.e), ⟨P.proj v, P.proj_mem_perp v⟩) := rfl

theorem map_eq_hypSplit (P : HypPair Q) (v : V) :
    Q v = (hypSplit P v).1.1 * (hypSplit P v).1.2 + Q (hypSplit P v).2 := by
  rw [hypSplit_apply]
  simp only
  have h := P.proj_mem_perp v
  rw [HypPair.mem_perp] at h
  have h1 : polar Q (P.proj v) P.f = 0 := by rw [polar_comm]; exact h.2
  have h2 : polar Q (P.proj v) P.e = 0 := by rw [polar_comm]; exact h.1
  have h3 : polar Q P.e (P.proj v) = 0 := h.1
  have h4 : polar Q P.f (P.proj v) = 0 := h.2
  conv_lhs => rw [P.eq_add_proj v]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f]
  simp only [polar_add_left, polar_smul_left_eq, polar_smul_right_eq, P.polar_ef, h3, h4]
  ring

end Split


section Perp

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def polarPerp (Q : QuadraticForm K V) (W : Submodule K V) : Submodule K V where
  carrier := {x | ∀ w ∈ W, polar Q w x = 0}
  zero_mem' := fun w _ => polar_zero_right Q w
  add_mem' := fun {x y} hx hy w hw => by rw [polar_add_right, hx w hw, hy w hw, add_zero]
  smul_mem' c x hx w hw := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [polar_smul_right_eq, hx w hw, mul_zero]

theorem mem_polarPerp {W : Submodule K V} {x : V} :
    x ∈ polarPerp Q W ↔ ∀ w ∈ W, polar Q w x = 0 := Iff.rfl

theorem isCompl_polarPerp [FiniteDimensional K V] {W : Submodule K V} (hW : PolarNondegOn Q W) :
    IsCompl W (polarPerp Q W) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxW hxp
    exact hW x hxW fun w hw => by rw [polar_comm]; exact hxp w hw
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hB := nondegenerate_polarBilin_restrict hW
    let ℓ : Module.Dual K W := (polarBilin Q v).comp W.subtype
    set u : W := (LinearMap.BilinForm.toDual (polarBilin (Q.restrict W)) hB).symm ℓ with hu
    have hu' : ∀ w : W, polar Q (u : V) w = polar Q v w := by
      intro w
      have := LinearMap.BilinForm.apply_toDual_symm_apply (B := polarBilin (Q.restrict W))
        (hB := hB) (f := ℓ) (v := w)
      rw [← hu] at this
      have e1 : polarBilin (Q.restrict W) u w = polar Q (u : V) w := by
        rw [polarBilin_apply_apply, polar_restrict]
      have e2 : ℓ w = polar Q v w := by
        simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, polarBilin_apply_apply]
      rw [e1, e2] at this
      exact this
    refine Submodule.mem_sup.mpr ⟨u, u.2, v - u, ?_, by abel⟩
    intro w hw
    rw [polar_sub_right, polar_comm Q w v, polar_comm Q w u, hu' ⟨w, hw⟩, sub_self]

theorem polarNondegOn_polarPerp (hQ : (polarBilin Q).Nondegenerate) [FiniteDimensional K V]
    {W : Submodule K V} (hW : PolarNondegOn Q W) : PolarNondegOn Q (polarPerp Q W) := by
  intro x hx hxx
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp
    ((isCompl_polarPerp hW).sup_eq_top ▸ Submodule.mem_top : z ∈ W ⊔ polarPerp Q W)
  rw [polar_add_right, hxx y hy, add_zero, polar_comm, hx w hw]

@[expose] noncomputable def perpSplit [FiniteDimensional K V] {W : Submodule K V}
    (hW : PolarNondegOn Q W) : V ≃ₗ[K] W × polarPerp Q W :=
  (Submodule.prodEquivOfIsCompl W _ (isCompl_polarPerp hW)).symm

theorem map_eq_perpSplit [FiniteDimensional K V] {W : Submodule K V} (hW : PolarNondegOn Q W)
    (v : V) :
    Q v = Q.restrict W (perpSplit hW v).1 + Q.restrict (polarPerp Q W) (perpSplit hW v).2 := by
  have h := (Submodule.prodEquivOfIsCompl W _ (isCompl_polarPerp hW)).apply_symm_apply v
  rw [Submodule.coe_prodEquivOfIsCompl'] at h
  have hv : v = ((perpSplit hW v).1 : V) + ((perpSplit hW v).2 : V) := h.symm
  set a := (perpSplit hW v).1
  set b := (perpSplit hW v).2
  conv_lhs => rw [hv]
  rw [QuadraticMap.map_add Q]
  have : polar Q (a : V) (b : V) = 0 := b.2 a a.2
  rw [this, add_zero]
  rfl

end Perp

section ZModTwo

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem zero_or_one_zmod : ∀ a : ZMod 2, a = 0 ∨ a = 1 := zmod_two_cases

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem cs_of_isPlusSpace {Q : QuadraticForm (ZMod 2) V} {m : ℕ} (h : IsPlusSpace Q m) :
    cs Q = 2 ^ m := by
  obtain ⟨φ, hφ⟩ := h
  rw [← cs_quadPlus m]
  exact cs_equiv φ.toEquiv _ _ hφ

theorem cs_of_isMinusSpace {Q : QuadraticForm (ZMod 2) V} {m : ℕ} (h : IsMinusSpace Q m)
    (hm : 1 ≤ m) : cs Q = -2 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨φ, hφ⟩ := h
  rw [← cs_quadMinus k]
  exact cs_equiv φ.toEquiv _ _ hφ

theorem cs_of_isStdSpace {Q : QuadraticForm (ZMod 2) V} {ε : Bool} {m : ℕ}
    (h : IsStdSpace ε Q m) (hm : ε = false → 1 ≤ m) :
    cs Q = if ε then 2 ^ m else -2 ^ m := by
  cases ε
  · simpa using cs_of_isMinusSpace h (hm rfl)
  · simpa using cs_of_isPlusSpace h

theorem isPlusSpace_succ_of_perp {Q : QuadraticForm (ZMod 2) V} (P : HypPair Q) {m : ℕ}
    (h : IsPlusSpace (Q.restrict P.perp) m) : IsPlusSpace Q (m + 1) := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(hypSplit P).trans ((LinearEquiv.prodCongr (LinearEquiv.refl _ _) φ).trans
    (Eplus (ZMod 2) m)), fun v => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [quadPlus_Eplus, hφ, map_eq_hypSplit P v]
  rfl

theorem isMinusSpace_succ_of_perp {Q : QuadraticForm (ZMod 2) V} (P : HypPair Q) {m : ℕ}
    (hm : 1 ≤ m) (h : IsMinusSpace (Q.restrict P.perp) m) : IsMinusSpace Q (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(hypSplit P).trans ((LinearEquiv.prodCongr (LinearEquiv.refl _ _) φ).trans
    (Eminus (ZMod 2) k)), fun v => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [quadMinus_Eminus, hφ, map_eq_hypSplit P v]
  rfl

theorem isPlusSpace_zero_of_finrank_eq_zero {Q : QuadraticForm (ZMod 2) V}
    (h : Module.finrank (ZMod 2) V = 0) [FiniteDimensional (ZMod 2) V] : IsPlusSpace Q 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun v => ?_⟩
  rw [Subsingleton.elim v 0, QuadraticMap.map_zero]
  simp [quadPlus_apply]

theorem exists_equiv_prod_of_aniso {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hK : ∀ a : K, a = 0 ∨ a = 1) (Q : QuadraticForm K V)
    (hdim : Module.finrank K V = 2) (hQ : ∀ x : V, x ≠ 0 → Q x ≠ 0) :
    ∃ φ : V ≃ₗ[K] (K × K), ∀ v, (φ v).1 ^ 2 + (φ v).1 * (φ v).2 + (φ v).2 ^ 2 = Q v := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq K V hdim
  have h2 : (1 : K) + 1 = 0 := by
    rcases hK (1 + 1) with h | h
    · exact h
    · exact absurd (add_eq_right.mp h) one_ne_zero
  have hb : ∀ x : V, x ≠ 0 → Q x = 1 := fun x hx => (hK _).resolve_left (hQ x hx)
  have hli := b.linearIndependent
  have h0 : b 0 ≠ 0 := b.ne_zero 0
  have h1 : b 1 ≠ 0 := b.ne_zero 1
  have h01 : b 0 + b 1 ≠ 0 := by
    intro h
    have := Fintype.linearIndependent_iff.mp hli ![1, 1] (by
      simpa [Fin.sum_univ_two] using h)
    simpa using this 0
  have hpol : polar Q (b 0) (b 1) = 1 := by
    rw [polar, hb _ h01, hb _ h0, hb _ h1]
    linear_combination (-1 : K) * h2
  refine ⟨b.equivFun.trans (LinearEquiv.finTwoArrow K K), fun v => ?_⟩
  have hv : v = b.equivFun v 0 • b 0 + b.equivFun v 1 • b 1 := by
    have := b.sum_repr v
    rw [Fin.sum_univ_two] at this
    exact this.symm
  show (b.equivFun v 0) ^ 2 + b.equivFun v 0 * b.equivFun v 1 + b.equivFun v 1 ^ 2 = Q v
  generalize b.equivFun v 0 = x0 at hv ⊢
  generalize b.equivFun v 1 = x1 at hv ⊢
  rw [hv, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hb _ h0, hb _ h1,
    polar_smul_left_eq, polar_smul_right_eq, hpol]
  ring

theorem isMinusSpace_one_of_aniso {Q : QuadraticForm (ZMod 2) V}
    (hdim : Module.finrank (ZMod 2) V = 2) (hQ : ∀ x : V, x ≠ 0 → Q x ≠ 0) :
    IsMinusSpace Q 1 := by
  obtain ⟨φ, hφ⟩ := exists_equiv_prod_of_aniso zmod_two_cases Q hdim hQ
  refine ⟨φ.trans (eMinusBase (ZMod 2)).symm, fun v => ?_⟩
  rw [quadMinus_one_eMinusBase]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  simpa using hφ v

theorem false_of_finrank_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hK : ∀ a : K, a = 0 ∨ a = 1) (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 1) : False := by
  have h2 : (1 : K) + 1 = 0 := by
    rcases hK (1 + 1) with h | h
    · exact h
    · exact absurd (add_eq_right.mp h) one_ne_zero
  have hpos : 0 < Module.finrank K V := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hall := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim
  apply hx
  refine eq_zero_of_polar_eq_zero hQ fun y => ?_
  obtain ⟨c, rfl⟩ := hall y
  rw [polar_smul_right_eq, polar_self_eq_two_mul]
  have : (2 : K) = 0 := by rw [← h2]; norm_num
  rw [this, zero_mul, mul_zero]

theorem exists_isStdSpace [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : PolarNondeg Q) :
    ∃ (ε : Bool) (m : ℕ), IsStdSpace ε Q m ∧ (ε = false → 1 ≤ m) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank (ZMod 2) V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    by_cases h : ∃ x : V, x ≠ 0 ∧ Q x = 0
    · obtain ⟨e, he0, he⟩ := h
      obtain ⟨P, -⟩ := exists_hypPair hQ he he0
      have hperp : PolarNondeg (Q.restrict P.perp) :=
        nondegenerate_polarBilin_restrict (P.polarNondegOn_perp hQ)
      have hlt : Module.finrank (ZMod 2) P.perp < n := by
        rw [← hn]
        apply Submodule.finrank_lt
        intro h
        have hf : P.f ∈ P.perp := h ▸ Submodule.mem_top
        rw [HypPair.mem_perp] at hf
        have := hf.1
        rw [P.polar_ef] at this
        exact one_ne_zero this
      obtain ⟨ε, m, hstd, hm⟩ := ih _ hlt (Q.restrict P.perp) hperp rfl
      cases ε
      · exact ⟨false, m + 1, isMinusSpace_succ_of_perp P (hm rfl) hstd, fun _ => by omega⟩
      · exact ⟨true, m + 1, isPlusSpace_succ_of_perp P hstd, by simp⟩
    · have h : ∀ x : V, x ≠ 0 → Q x ≠ 0 := fun x hx hx0 => h ⟨x, hx, hx0⟩
      have h3 : n < 3 := by
        by_contra h3
        obtain ⟨x, hx, hx0⟩ := exists_ne_zero_map_eq_zero (Q := Q) (by omega)
        exact h x hx hx0
      interval_cases n
      · exact ⟨true, 0, isPlusSpace_zero_of_finrank_eq_zero hn, by simp⟩
      · exact (false_of_finrank_one zero_or_one_zmod Q hQ hn).elim
      · exact ⟨false, 1, isMinusSpace_one_of_aniso hn fun x hx => h x hx, fun _ => le_rfl⟩

theorem cs_sign_inj {ε ε' : Bool} {m m' : ℕ}
    (h : (if ε then (2 : ℤ) ^ m else -2 ^ m) = if ε' then 2 ^ m' else -2 ^ m') :
    ε = ε' ∧ m = m' := by
  have hp : ∀ k : ℕ, (0 : ℤ) < 2 ^ k := fun k => by positivity
  cases ε <;> cases ε' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by exact_mod_cast neg_inj.mp h)⟩
  · linarith [hp m, hp m']
  · linarith [hp m, hp m']
  · exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)⟩

theorem isStdSpace_unique {Q : QuadraticForm (ZMod 2) V} {ε ε' : Bool} {m m' : ℕ}
    (h : IsStdSpace ε Q m) (h' : IsStdSpace ε' Q m') (hm : ε = false → 1 ≤ m)
    (hm' : ε' = false → 1 ≤ m') : ε = ε' ∧ m = m' := by
  refine cs_sign_inj ?_
  rw [← cs_of_isStdSpace h hm, ← cs_of_isStdSpace h' hm']

theorem finrank_of_isStdSpace_arf {Q : QuadraticForm (ZMod 2) V} {ε : Bool} {m : ℕ}
    (h : IsStdSpace ε Q m) (hm : ε = false → 1 ≤ m) : Module.finrank (ZMod 2) V = 2 * m := by
  cases ε
  · obtain ⟨φ, -⟩ := h
    have hm1 := hm rfl
    rw [φ.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · obtain ⟨φ, -⟩ := h
    rw [φ.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

theorem cs_hypSplit [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V) (P : HypPair Q) :
    cs Q = 2 * cs (Q.restrict P.perp) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := cs_equiv (hypSplit P).toEquiv Q
    (fun x : (ZMod 2 × ZMod 2) × P.perp => x.1.1 * x.1.2 + Q.restrict P.perp x.2)
    (fun v => (map_eq_hypSplit P v).symm)
  rw [this, cs_prod (fun p : ZMod 2 × ZMod 2 => p.1 * p.2) (Q.restrict P.perp) _ (fun x => rfl),
    cs_hyp]

theorem cs_perpSplit [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W) :
    cs Q = cs (Q.restrict W) * cs (Q.restrict (polarPerp Q W)) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := cs_equiv (perpSplit hW).toEquiv Q
    (fun x : W × polarPerp Q W => Q.restrict W x.1 + Q.restrict (polarPerp Q W) x.2)
    (fun v => (map_eq_perpSplit hW v).symm)
  rw [this, cs_prod (Q.restrict W) (Q.restrict (polarPerp Q W)) _ (fun x => rfl)]

theorem exists_isStdSpace_perp [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : PolarNondeg Q) {W : Submodule (ZMod 2) V} (hW : PolarNondegOn Q W) :
    ∃ (ε₁ ε₂ : Bool) (m₁ m₂ : ℕ), IsStdSpace ε₁ (Q.restrict W) m₁ ∧ (ε₁ = false → 1 ≤ m₁) ∧
      IsStdSpace ε₂ (Q.restrict (polarPerp Q W)) m₂ ∧ (ε₂ = false → 1 ≤ m₂) ∧
      IsStdSpace (ε₁ == ε₂) Q (m₁ + m₂) := by
  obtain ⟨ε₁, m₁, h₁, hm₁⟩ := exists_isStdSpace (Q.restrict W) (nondegenerate_polarBilin_restrict hW)
  have hW' : PolarNondegOn Q (polarPerp Q W) := polarNondegOn_polarPerp hQ hW
  obtain ⟨ε₂, m₂, h₂, hm₂⟩ :=
    exists_isStdSpace (Q.restrict (polarPerp Q W)) (nondegenerate_polarBilin_restrict hW')
  obtain ⟨ε, m, h, hm⟩ := exists_isStdSpace Q hQ
  have e1 := cs_of_isStdSpace h₁ hm₁
  have e2 := cs_of_isStdSpace h₂ hm₂
  have e := cs_of_isStdSpace h hm
  rw [cs_perpSplit hW, e1, e2] at e
  have hsign : (if ε then (2 : ℤ) ^ m else -2 ^ m) =
      if (ε₁ == ε₂) then 2 ^ (m₁ + m₂) else -2 ^ (m₁ + m₂) := by
    rw [← e]
    cases ε₁ <;> cases ε₂ <;> simp [pow_add]
  obtain ⟨rfl, rfl⟩ := cs_sign_inj hsign.symm
  exact ⟨ε₁, ε₂, m₁, m₂, h₁, hm₁, h₂, hm₂, h⟩

theorem isStdSpace_restrict_perp [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : PolarNondeg Q) (P : HypPair Q) {ε : Bool} {m : ℕ} (h : IsStdSpace ε Q (m + 1)) :
    IsStdSpace ε (Q.restrict P.perp) m := by
  have hperp : PolarNondeg (Q.restrict P.perp) :=
    nondegenerate_polarBilin_restrict (P.polarNondegOn_perp hQ)
  obtain ⟨ε', m', h', hm'⟩ := exists_isStdSpace (Q.restrict P.perp) hperp
  have e := cs_of_isStdSpace h (fun _ => by omega)
  have e' := cs_of_isStdSpace h' hm'
  rw [cs_hypSplit Q P, e'] at e
  have hsign : (if ε then (2 : ℤ) ^ (m + 1) else -2 ^ (m + 1)) =
      if ε' then 2 ^ (m' + 1) else -2 ^ (m' + 1) := by
    rw [← e]
    cases ε' <;> simp [pow_succ] <;> ring
  obtain ⟨rfl, hmm⟩ := cs_sign_inj hsign
  have : m = m' := by omega
  subst this
  exact h'

theorem card_modEq_one_of_free {α : Type*} [Finite α] (f : α → α) {p : ℕ} [Fact p.Prime]
    (hf : f^[p] = id) (x0 : α) (hx0 : f x0 = x0) (hfix : ∀ x, f x = x → x = x0) :
    Nat.card α ≡ 1 [MOD p] := by
  classical
  have := Fintype.ofFinite α
  let g : Function.End α := f
  have h1 : g ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact (hom_coe_pow (fun g : Function.End α ↦ g) rfl (fun g h ↦ rfl) g p).trans hf
  have := Equiv.Perm.card_fixedPoints_modEq (f := g) (p := p) (n := 1) h1
  have hc : Fintype.card (Function.fixedPoints g) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨x0, hx0⟩, fun y => Subtype.ext (hfix y y.2)⟩
  rw [hc] at this
  rwa [Nat.card_eq_fintype_card]

theorem iterate_linearEquiv_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : V ≃ₗ[K] V) (n : ℕ) (v : V) : T^[n] v = (T ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, pow_succ]; rfl

theorem cs_eq_two_mul_card_sub [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    cs Q = 2 * (Finset.univ.filter fun v => Q v = 0).card - Fintype.card V := by
  classical
  have h : ∀ a : ZMod 2, (-1 : ℤ) ^ a.val = if a = 0 then 1 else -1 := by decide
  rw [cs_eq_sum]
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun v => Q v = 0)
  simp only [Finset.card_univ] at this
  have h2 : ((Finset.univ.filter fun v => ¬ Q v = 0).card : ℤ) =
      Fintype.card V - (Finset.univ.filter fun v => Q v = 0).card := by omega
  simp only [nsmul_eq_mul, mul_one, mul_neg, h2]
  ring

theorem int_dvd_aux {p : ℤ} (hp : Prime p) {x s Z : ℤ} (hs : s * s = 1) (h2 : 2 * Z = x ^ 2 + s * x)
    (hZ : p ∣ Z - 1) (hN : p ∣ x ^ 2 - 1) : p ∣ x - s := by
  have h3 : p ∣ (x - s) * (x + 2 * s) := by
    have : (x - s) * (x + 2 * s) = 2 * (Z - 1) := by linear_combination (-1 : ℤ) * h2 - 2 * hs
    rw [this]
    exact dvd_mul_of_dvd_right hZ 2
  rcases hp.dvd_or_dvd h3 with h | h
  · exact h
  · have h4 : p ∣ 3 := by
      have : (3 : ℤ) = (x ^ 2 - 1) - (x + 2 * s) * (x - 2 * s) := by linear_combination (-4 : ℤ) * hs
      rw [this]
      exact dvd_sub hN (dvd_mul_of_dvd_left h _)
    have : x - s = (x + 2 * s) - 3 * s := by ring
    rw [this]
    exact dvd_sub h (dvd_mul_of_dvd_left h4 s)

theorem dvd_of_fpf_of_cs [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {ε : Bool} {m : ℕ} (hfr : Module.finrank (ZMod 2) V = 2 * m)
    (hcs : cs Q = if ε then 2 ^ m else -2 ^ m) {p : ℕ} (hp : p.Prime)
    (T : V ≃ₗ[ZMod 2] V) (hT : ∀ v, Q (T v) = Q v) (hTp : T ^ p = 1)
    (hfix : ∀ v, T v = v → v = 0) :
    p ∣ (if ε then 2 ^ m - 1 else 2 ^ m + 1) := by
  have := Fact.mk hp
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  classical
  have hiter : ∀ v, (⇑T)^[p] v = v := fun v => by
    rw [iterate_linearEquiv_apply, hTp]; rfl
  have hV : Nat.card V ≡ 1 [MOD p] :=
    card_modEq_one_of_free (⇑T) (funext hiter) 0 (map_zero T) hfix
  let f : {v : V // Q v = 0} → {v : V // Q v = 0} := fun x => ⟨T x, by rw [hT]; exact x.2⟩
  have hf : ∀ n x, ((f^[n] x : {v : V // Q v = 0}) : V) = (⇑T)^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact congrArg T (ih x)
  have hZ : Nat.card {v : V // Q v = 0} ≡ 1 [MOD p] := by
    refine card_modEq_one_of_free f (funext fun x => Subtype.ext ?_) ⟨0, QuadraticMap.map_zero Q⟩ ?_ ?_
    · rw [hf]; exact hiter x
    · exact Subtype.ext (map_zero T)
    · intro x hx
      exact Subtype.ext (hfix x (congrArg Subtype.val hx))
  have hN : Fintype.card V = 2 ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), hfr, ZMod.card]
  have hcard : Nat.card V = 2 ^ (2 * m) := by rw [Nat.card_eq_fintype_card]; exact hN
  rw [cs_eq_two_mul_card_sub] at hcs
  have hZ' : Nat.card {v : V // Q v = 0} = (Finset.univ.filter fun v => Q v = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hN] at hcs
  rw [← hZ'] at hcs
  have d1 : (p : ℤ) ∣ (Nat.card {v : V // Q v = 0} : ℤ) - 1 := by
    have := (Nat.modEq_iff_dvd).1 hZ.symm
    simpa using this
  have d2 : (p : ℤ) ∣ ((2 : ℤ) ^ m) ^ 2 - 1 := by
    have := (Nat.modEq_iff_dvd).1 hV.symm
    rw [hcard] at this
    have e : (((2 : ℕ) ^ (2 * m) : ℕ) : ℤ) = ((2 : ℤ) ^ m) ^ 2 := by push_cast; ring
    simpa [e] using this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte] at hcs ⊢
    have := int_dvd_aux hpZ (x := (2 : ℤ) ^ m) (s := -1) (Z := Nat.card {v : V // Q v = 0})
      (by norm_num) (by push_cast at hcs; linear_combination hcs) d1 d2
    have e : (2 : ℤ) ^ m - -1 = ((2 ^ m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at this
    exact_mod_cast this
  · simp only [↓reduceIte] at hcs ⊢
    have := int_dvd_aux hpZ (x := (2 : ℤ) ^ m) (s := 1) (Z := Nat.card {v : V // Q v = 0})
      (by norm_num) (by push_cast at hcs; linear_combination hcs) d1 d2
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have e : (2 : ℤ) ^ m - 1 = ((2 ^ m - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub h1]; ring
    rw [e] at this
    exact_mod_cast this

theorem dvd_of_fpf [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ε : Bool}
    {m : ℕ} (h : IsStdSpace ε Q m) (hm : ε = false → 1 ≤ m) {p : ℕ} (hp : p.Prime)
    (T : V ≃ₗ[ZMod 2] V) (hT : ∀ v, Q (T v) = Q v) (hTp : T ^ p = 1)
    (hfix : ∀ v, T v = v → v = 0) :
    p ∣ (if ε then 2 ^ m - 1 else 2 ^ m + 1) :=
  dvd_of_fpf_of_cs (finrank_of_isStdSpace_arf h hm) (cs_of_isStdSpace h hm) hp T hT hTp hfix

end ZModTwo

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
