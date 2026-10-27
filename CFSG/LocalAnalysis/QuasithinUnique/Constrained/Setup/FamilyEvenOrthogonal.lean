module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthPlane
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix

section Framework

variable {K : Type} [Field K]

@[expose] def isoGroup {V : Type} [AddCommGroup V] [Module K V] (Q : V → K) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {f | ∀ v, Q (f v) = Q v}
  one_mem' := fun v => rfl
  mul_mem' := fun {f g} hf hg v => by
    rw [LinearEquiv.mul_apply, hf, hg]
  inv_mem' := fun {f} hf v => by
    have h := hf (f.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_isoGroup {V : Type} [AddCommGroup V] [Module K V] {Q : V → K} {f : V ≃ₗ[K] V} :
    f ∈ isoGroup Q ↔ ∀ v, Q (f v) = Q v := Iff.rfl

@[expose] def EARank (r : ℕ) (ι : Type) [Fintype ι] {V : Type} [AddCommGroup V] [Module K V]
    (Q : V → K) : Prop :=
  ∃ φ : (ι → Multiplicative (ZMod r)) →* (V ≃ₗ[K] V), Function.Injective φ ∧
    ∀ x, φ x ∈ ⁅isoGroup Q, isoGroup Q⁆

variable {r : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι'] {V V' : Type} [AddCommGroup V]
  [Module K V] [AddCommGroup V'] [Module K V'] {Q : V → K} {Q' : V' → K}

theorem EARank.of_equiv (e : ι ≃ ι') (h : EARank (K := K) r ι Q) : EARank (K := K) r ι' Q := by
  obtain ⟨φ, hinj, hmem⟩ := h
  refine ⟨φ.comp (MulEquiv.arrowCongr e.symm (MulEquiv.refl _)).toMonoidHom, ?_, fun x => hmem _⟩
  exact hinj.comp (MulEquiv.arrowCongr e.symm (MulEquiv.refl _)).injective

theorem EARank.empty [IsEmpty ι] : EARank (K := K) r ι Q :=
  ⟨1, fun x y _ => funext fun i => isEmptyElim i, fun x => by
    rw [MonoidHom.one_apply]
    exact Subgroup.one_mem _⟩

@[expose] def autConj (Θ : V ≃ₗ[K] V') : (V' ≃ₗ[K] V') ≃* (V ≃ₗ[K] V) where
  toFun f := Θ.trans (f.trans Θ.symm)
  invFun f := Θ.symm.trans (f.trans Θ)
  left_inv f := LinearEquiv.ext fun x => by simp
  right_inv f := LinearEquiv.ext fun x => by simp
  map_mul' f g := LinearEquiv.ext fun x => by simp

theorem autConj_apply (Θ : V ≃ₗ[K] V') (f : V' ≃ₗ[K] V') (v : V) :
    autConj Θ f v = Θ.symm (f (Θ v)) := rfl

theorem autConj_mem_iso (Θ : V ≃ₗ[K] V') (hΘ : ∀ v, Q' (Θ v) = Q v) {f : V' ≃ₗ[K] V'}
    (hf : f ∈ isoGroup Q') : autConj Θ f ∈ isoGroup Q := by
  intro v
  rw [autConj_apply, ← hΘ, LinearEquiv.apply_symm_apply, hf, hΘ]

theorem EARank.of_isometry (Θ : V ≃ₗ[K] V') (hΘ : ∀ v, Q' (Θ v) = Q v)
    (h : EARank (K := K) r ι Q') : EARank (K := K) r ι Q := by
  obtain ⟨φ, hinj, hmem⟩ := h
  refine ⟨(autConj Θ).toMonoidHom.comp φ, (autConj Θ).injective.comp hinj, fun x => ?_⟩
  have h1 : ((isoGroup Q').map (autConj Θ).toMonoidHom) ≤ isoGroup Q := by
    rintro _ ⟨f, hf, rfl⟩
    exact autConj_mem_iso Θ hΘ hf
  have h2 : ⁅(isoGroup Q').map (autConj Θ).toMonoidHom, (isoGroup Q').map (autConj Θ).toMonoidHom⁆
      ≤ ⁅isoGroup Q, isoGroup Q⁆ := Subgroup.commutator_mono h1 h1
  rw [← Subgroup.map_commutator] at h2
  exact h2 ⟨φ x, hmem x, rfl⟩

theorem commutator_map_le {G G' : Type*} [Group G] [Group G'] (f : G →* G') {H : Subgroup G}
    {H' : Subgroup G'} (h : H.map f ≤ H') {x : G} (hx : x ∈ ⁅H, H⁆) : f x ∈ ⁅H', H'⁆ := by
  have h2 := Subgroup.commutator_mono h h
  rw [← Subgroup.map_commutator] at h2
  exact h2 ⟨x, hx, rfl⟩

@[expose] def prodAut : (V ≃ₗ[K] V) × (V' ≃ₗ[K] V') →* ((V × V') ≃ₗ[K] (V × V')) where
  toFun fg := LinearEquiv.prodCongr fg.1 fg.2
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem prodAut_apply (f : V ≃ₗ[K] V) (g : V' ≃ₗ[K] V') (p : V × V') :
    prodAut (f, g) p = (f p.1, g p.2) := rfl

theorem prodAut_injective : Function.Injective (prodAut : (V ≃ₗ[K] V) × (V' ≃ₗ[K] V') →* _) := by
  rintro ⟨f, g⟩ ⟨f', g'⟩ h
  refine Prod.ext (LinearEquiv.ext fun v => ?_) (LinearEquiv.ext fun w => ?_)
  · have := congrArg (fun e : (V × V') ≃ₗ[K] (V × V') => (e (v, 0)).1) h
    simpa [prodAut_apply] using this
  · have := congrArg (fun e : (V × V') ≃ₗ[K] (V × V') => (e (0, w)).2) h
    simpa [prodAut_apply] using this

@[expose] def sumArrowMulEquiv (α β G : Type) [Group G] : (α ⊕ β → G) ≃* (α → G) × (β → G) :=
  { Equiv.sumArrowEquivProdArrow α β G with
    map_mul' := fun _ _ => rfl }

theorem EARank.prod {Q₁ : V → K} {Q₂ : V' → K} (h₁ : EARank (K := K) r ι Q₁)
    (h₂ : EARank (K := K) r ι' Q₂) :
    EARank (K := K) r (ι ⊕ ι') (fun p : V × V' => Q₁ p.1 + Q₂ p.2) := by
  obtain ⟨φ₁, hi₁, hm₁⟩ := h₁
  obtain ⟨φ₂, hi₂, hm₂⟩ := h₂
  let e := sumArrowMulEquiv ι ι' (Multiplicative (ZMod r))
  refine ⟨prodAut.comp ((φ₁.prodMap φ₂).comp e.toMonoidHom), ?_, fun x => ?_⟩
  · have hprod : Function.Injective (φ₁.prodMap φ₂) := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (hi₁ h1) (hi₂ h2)
    exact prodAut_injective.comp (hprod.comp e.injective)
  · set Qs : V × V' → K := fun p => Q₁ p.1 + Q₂ p.2 with hQs
    have hl : (isoGroup Q₁).map ((prodAut (K := K) (V := V) (V' := V')).comp
        (MonoidHom.inl _ _)) ≤ isoGroup Qs := by
      rintro _ ⟨f, hf, rfl⟩ p
      show Q₁ (f p.1) + Q₂ p.2 = Q₁ p.1 + Q₂ p.2
      rw [hf]
    have hr : (isoGroup Q₂).map ((prodAut (K := K) (V := V) (V' := V')).comp
        (MonoidHom.inr _ _)) ≤ isoGroup Qs := by
      rintro _ ⟨f, hf, rfl⟩ p
      show Q₁ p.1 + Q₂ (f p.2) = Q₁ p.1 + Q₂ p.2
      rw [hf]
    have hx : (prodAut.comp ((φ₁.prodMap φ₂).comp e.toMonoidHom)) x =
        ((prodAut (K := K) (V := V) (V' := V')).comp (MonoidHom.inl _ _)) (φ₁ (e x).1) *
        ((prodAut (K := K) (V := V) (V' := V')).comp (MonoidHom.inr _ _)) (φ₂ (e x).2) := by
      show prodAut (φ₁ (e x).1, φ₂ (e x).2) = prodAut (φ₁ (e x).1, 1) * prodAut (1, φ₂ (e x).2)
      rw [← map_mul]
      simp
    rw [hx]
    exact Subgroup.mul_mem _ (commutator_map_le _ hl (hm₁ _)) (commutator_map_le _ hr (hm₂ _))

end Framework

section Cyclic

@[expose] def cycHom {G : Type*} [Group G] (g : G) (r : ℕ) [NeZero r] (h : g ^ r = 1) :
    Multiplicative (ZMod r) →* G where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [← pow_add, ZMod.val_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd x).val +
      (Multiplicative.toAdd y).val) r, pow_add, pow_mul, h, one_pow, mul_one]

theorem cycHom_apply {G : Type*} [Group G] (g : G) (r : ℕ) [NeZero r] (h : g ^ r = 1)
    (x : Multiplicative (ZMod r)) : cycHom g r h x = g ^ (Multiplicative.toAdd x).val := rfl

theorem cycHom_injective {G : Type*} [Group G] (g : G) (r : ℕ) [NeZero r] (h : g ^ r = 1)
    (ho : orderOf g = r) : Function.Injective (cycHom g r h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : g ^ (Multiplicative.toAdd x).val = 1 := hx
  have h2 : r ∣ (Multiplicative.toAdd x).val := by
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [ho] at this
  have h3 : (Multiplicative.toAdd x).val < r := ZMod.val_lt _
  have h4 : (Multiplicative.toAdd x).val = 0 := Nat.eq_zero_of_dvd_of_lt h2 h3
  exact toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 h4)

end Cyclic

section GLLin

variable {K : Type} [Field K] {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]

@[expose] noncomputable def glLin : GL ι₀ K ≃* ((ι₀ → K) ≃ₗ[K] (ι₀ → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι₀ → K))

theorem glLin_apply (g : GL ι₀ K) (v : ι₀ → K) :
    glLin g v = (g : Matrix ι₀ ι₀ K) *ᵥ v := rfl

end GLLin

section PlaneRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem glLin_mem_isoGroup_plane (a : K) {g : GL (Fin 2) K} (hg : g ∈ planeIso a) :
    glLin g ∈ isoGroup (planeNrm a) := fun v => by
  rw [glLin_apply]
  exact hg v

theorem odd_of_dvd_card_succ {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K + 1) : Odd r := by
  have : Fintype K := Fintype.ofFinite K
  rcases hr.eq_two_or_odd' with rfl | h
  · exfalso
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 2 n.ne_zero
    exact absurd ((Nat.dvd_add_right h2).1 hrq) (by norm_num)
  · exact h

theorem EARank.plane (a : K) (ha : ∀ z : K, z ^ 2 + z + a ≠ 0) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K + 1) : EARank (K := K) r Unit (planeNrm a) := by
  have hodd : Odd r := odd_of_dvd_card_succ hr hrq
  have : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card (Tgrp a) := by
    rw [card_Tgrp a ha]
    exact hrq
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := Tgrp a) r hdvd
  have hord : orderOf (g₀ : GL (Fin 2) K) = r := by rw [Subgroup.orderOf_coe]; exact hg₀
  have hpow : (g₀ : GL (Fin 2) K) ^ r = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  let cyc := cycHom (g₀ : GL (Fin 2) K) r hpow
  refine ⟨(glLin (K := K) (ι₀ := Fin 2)).toMonoidHom.comp
      (cyc.comp (MulEquiv.funUnique Unit (Multiplicative (ZMod r))).toMonoidHom), ?_, fun x => ?_⟩
  · exact (glLin (K := K) (ι₀ := Fin 2)).injective.comp
      ((cycHom_injective _ r hpow hord).comp (MulEquiv.funUnique Unit _).injective)
  · have hg1 : (cyc ((MulEquiv.funUnique Unit (Multiplicative (ZMod r))) x) : GL (Fin 2) K) ∈
        Tgrp a := by
      show (g₀ : GL (Fin 2) K) ^ _ ∈ Tgrp a
      exact Subgroup.pow_mem _ g₀.2 _
    have hg2 : (cyc ((MulEquiv.funUnique Unit (Multiplicative (ZMod r))) x) : GL (Fin 2) K) ^ r =
        1 := by
      show ((g₀ : GL (Fin 2) K) ^ _) ^ r = 1
      rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
    have hcomm := Tgrp_odd_mem_commutator a hodd hg1 hg2
    exact commutator_map_le (glLin (K := K) (ι₀ := Fin 2)).toMonoidHom
      (fun f ⟨g, hg, hgf⟩ => hgf ▸ glLin_mem_isoGroup_plane a hg) hcomm

end PlaneRank

section Hyperbolic

variable {K : Type} [Field K]

@[expose] def hypPlane (p : K × K) : K := p.1 * p.2

@[expose] def hypForm (n : ℕ) (w : Fin n → K × K) : K := ∑ i, (w i).1 * (w i).2

variable [CharP K 2]

@[expose] def hyp4Equiv (a : K) : ((K × K) × (K × K)) ≃ₗ[K] ((Fin 2 → K) × (Fin 2 → K)) where
  toFun q := (![q.1.1 + a * q.1.2, q.1.2 + q.2.1 + q.2.2],
    ![q.1.1 + a * q.1.2 + q.2.2, q.2.1 + q.2.2])
  invFun P := ((P.1 0 + a * (P.1 1 + P.2 1), P.1 1 + P.2 1), (P.2 1 + P.2 0 + P.1 0, P.2 0 + P.1 0))
  map_add' q q' := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp <;> ring
  map_smul' c q := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp <;> ring
  left_inv q := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    obtain ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩ := q
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linear_combination (a * x₂ + a * y₁ + a * y₂) * h2
    · linear_combination (x₂ + y₂) * h2
    · linear_combination (a * y₁ + x₁ + y₂) * h2
    · linear_combination (a * y₁ + x₁) * h2
  right_inv P := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    obtain ⟨P, P'⟩ := P
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp
    · linear_combination (a * P' 1 + a * P 1) * h2
    · linear_combination (P' 0 + P' 1 + P 0) * h2
    · linear_combination (a * P' 1 + a * P 1 + P 0) * h2
    · linear_combination (P' 0 + P 0) * h2

theorem hyp4Equiv_isometry (a : K) (q : (K × K) × (K × K)) :
    planeNrm a (hyp4Equiv a q).1 + planeNrm a (hyp4Equiv a q).2 = hypPlane q.1 + hypPlane q.2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩ := q
  simp only [hyp4Equiv, planeNrm, hypPlane, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (a ^ 2 * y₁ ^ 2 + 2 * a * x₁ * y₁ + a * x₂ ^ 2 + 2 * a * x₂ * y₁ +
    2 * a * x₂ * y₂ + a * y₁ ^ 2 + 3 * a * y₁ * y₂ + a * y₂ ^ 2 + x₁ ^ 2 + x₁ * x₂ +
    2 * x₁ * y₂ + y₂ ^ 2) * h2

@[expose] def hypSplit (n : ℕ) :
    (Fin (n + 2) → K × K) ≃ₗ[K] ((K × K) × (K × K)) × (Fin n → K × K) where
  toFun w := ((w 0, w 1), fun i => w i.succ.succ)
  invFun p := Fin.cons p.1.1 (Fin.cons p.1.2 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp
  right_inv p := by
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun i => ?_) <;> simp

omit [CharP K 2] in
theorem hypSplit_isometry (n : ℕ) (w : Fin (n + 2) → K × K) :
    (hypPlane (hypSplit n w).1.1 + hypPlane (hypSplit n w).1.2) + hypForm n (hypSplit n w).2 =
      hypForm (n + 2) w := by
  simp [hypSplit, hypForm, hypPlane, Fin.sum_univ_succ, add_assoc]

end Hyperbolic

section HypRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem EARank.hyp4 (a : K) (ha : ∀ z : K, z ^ 2 + z + a ≠ 0) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K + 1) :
    EARank (K := K) r (Unit ⊕ Unit) (fun q : (K × K) × (K × K) => hypPlane q.1 + hypPlane q.2) :=
  EARank.of_isometry (hyp4Equiv a) (hyp4Equiv_isometry a)
    (EARank.prod (EARank.plane a ha hr hrq) (EARank.plane a ha hr hrq))

theorem EARank.hyp (a : K) (ha : ∀ z : K, z ^ 2 + z + a ≠ 0) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K + 1) :
    ∀ n : ℕ, EARank (K := K) r (Fin (2 * (n / 2))) (hypForm n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · have : IsEmpty (Fin (2 * (0 / 2))) := ⟨fun i => by have := i.2; omega⟩
      exact EARank.empty
    · have : IsEmpty (Fin (2 * ((0 + 1) / 2))) := ⟨fun i => by have := i.2; omega⟩
      exact EARank.empty
    · have h1 := ih n (by omega)
      have h2 := EARank.prod (EARank.hyp4 a ha hr hrq) h1
      have h3 := EARank.of_isometry (hypSplit n) (hypSplit_isometry n) h2
      have hc : Fintype.card ((Unit ⊕ Unit) ⊕ Fin (2 * (n / 2))) = 2 * ((n + 2) / 2) := by
        simp
        omega
      exact h3.of_equiv (Fintype.equivFinOfCardEq hc)

end HypRank

section SpecificForms

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.Assembly.LowTwoRank

@[expose] def tailForm (b c : K) (p : Fin 2 → K) : K := p 0 ^ 2 + b * p 0 * p 1 + c * p 1 ^ 2

theorem exists_rootless : ∃ a : K, ∀ z : K, z ^ 2 + z + a ≠ 0 := by
  have hnotsurj : ¬ Function.Surjective (fun z : K => z ^ 2 + z) := by
    intro hs
    have hinj := Finite.injective_iff_surjective.2 hs
    have h01 : (0 : K) ^ 2 + 0 = (1 : K) ^ 2 + 1 := by
      have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
      rw [one_pow, h2]
      simp
    exact zero_ne_one (hinj h01)
  simp only [Function.Surjective, not_forall, not_exists] at hnotsurj
  obtain ⟨a, ha⟩ := hnotsurj
  refine ⟨a, fun z hz => ha z ?_⟩
  have : z ^ 2 + z = -a := eq_neg_of_add_eq_zero_left hz
  rw [this, CharTwo.neg_eq]

theorem rootless_of_minus (b c : K) (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 ∧ ∀ z : K, z ^ 2 + z + c / b ^ 2 ≠ 0 := by
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := exists_sq_K c
    refine h s ?_
    rw [hb0, zero_mul, add_zero, hs, CharTwo.add_self_eq_zero]
  refine ⟨hb, fun z hz => h (b * z) ?_⟩
  have h1 : (b * z) ^ 2 + b * (b * z) + c = b ^ 2 * (z ^ 2 + z + c / b ^ 2) := by
    field_simp
  rw [h1, hz, mul_zero]

@[expose] def tailEquiv (b : K) (hb : b ≠ 0) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun p := ![p 0, b * p 1]
  invFun p := ![p 0, b⁻¹ * p 1]
  map_add' p q := by
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [mul_left_comm]
  left_inv p := by
    ext i
    fin_cases i <;> simp [hb]
  right_inv p := by
    ext i
    fin_cases i <;> simp [hb]

omit [Finite K] [CharP K 2] in
theorem tailEquiv_isometry (b c : K) (hb : b ≠ 0) (p : Fin 2 → K) :
    planeNrm (c / b ^ 2) (tailEquiv b hb p) = tailForm b c p := by
  simp only [tailEquiv, planeNrm, tailForm, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

@[expose] def plusEquiv (n : ℕ) : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n → K × K) where
  toFun v i := (v (Sum.inl i), v (Sum.inr i))
  invFun w := Sum.elim (fun i => (w i).1) (fun i => (w i).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext x
    cases x <;> rfl
  right_inv w := rfl

@[expose] def minusEquiv (m : ℕ) :
    (Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃ₗ[K] (Fin m → K × K) × (Fin 2 → K) where
  toFun v := (fun i => (v (Sum.inl i), v (Sum.inr (Sum.inl i))), fun j => v (Sum.inr (Sum.inr j)))
  invFun p := Sum.elim (fun i => (p.1 i).1) (Sum.elim (fun i => (p.1 i).2) p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext x
    rcases x with x | x | x <;> rfl
  right_inv p := rfl

theorem EARank.quadPlus {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K + 1) (n : ℕ) :
    EARank (K := K) r (Fin (2 * (n / 2))) (StatedQuadPlus n K) := by
  obtain ⟨a, ha⟩ := exists_rootless (K := K)
  exact EARank.of_isometry (plusEquiv n) (fun v => rfl) (EARank.hyp a ha hr hrq n)

theorem EARank.quadMinus {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K + 1) (n : ℕ) (b c : K)
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    EARank (K := K) r (Fin (2 * ((n - 1) / 2)) ⊕ Unit) (StatedQuadMinus n K b c) := by
  obtain ⟨hb, ha⟩ := rootless_of_minus b c h
  have htail : EARank (K := K) r Unit (tailForm b c) :=
    EARank.of_isometry (tailEquiv b hb) (tailEquiv_isometry b c hb)
      (EARank.plane (c / b ^ 2) ha hr hrq)
  have hprod := EARank.prod (EARank.hyp (c / b ^ 2) ha hr hrq (n - 1)) htail
  refine EARank.of_isometry (minusEquiv (n - 1)) (fun v => ?_) hprod
  show (∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i))) +
      (v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        c * v (Sum.inr (Sum.inr 1)) ^ 2) = StatedQuadMinus n K b c v
  unfold StatedQuadMinus
  ring

end SpecificForms

section Projective

variable {K : Type} [Field K] {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]

open CFSG.Assembly.LowTwoRank

@[expose] noncomputable def isoGL (Q : (ι₀ → K) → K) : Subgroup (GL ι₀ K) :=
  (isoGroup Q).comap (glLin (K := K) (ι₀ := ι₀)).toMonoidHom

theorem mem_isoGL {Q : (ι₀ → K) → K} {A : GL ι₀ K} :
    A ∈ isoGL Q ↔ ∀ v, Q ((A : Matrix ι₀ ι₀ K) *ᵥ v) = Q v := Iff.rfl

theorem statedOmega_eq (Q : (ι₀ → K) → K) : StatedOmega Q = ⁅isoGL Q, isoGL Q⁆ := by
  unfold StatedOmega
  have : {A : GL ι₀ K | ∀ v, Q ((A : Matrix ι₀ ι₀ K) *ᵥ v) = Q v} = (isoGL Q : Set (GL ι₀ K)) :=
    rfl
  rw [this, Subgroup.closure_eq]

theorem commutator_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem omega_inf_scalars_eq_bot [CharP K 2] (Q : (ι₀ → K) → K)
    (hQ : ∀ (c : K) (v : ι₀ → K), Q (c • v) = c ^ 2 * Q v) (hne : ∃ v, Q v ≠ 0) :
    StatedOmega Q ⊓ StatedScalars ι₀ K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgΩ, c, rfl⟩
  rw [statedOmega_eq] at hgΩ
  have hg := commutator_le_self _ hgΩ
  obtain ⟨v, hv⟩ := hne
  have h1 : Q (((Matrix.GeneralLinearGroup.scalar ι₀ c : GL ι₀ K) : Matrix ι₀ ι₀ K) *ᵥ v) =
      Q v := hg v
  have h2 : ((Matrix.GeneralLinearGroup.scalar ι₀ c : GL ι₀ K) : Matrix ι₀ ι₀ K) *ᵥ v =
      (c : K) • v := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [h2, hQ] at h1
  have h3 : (c : K) ^ 2 = 1 := by
    have := mul_right_cancel₀ hv (h1.trans (one_mul _).symm)
    exact this
  have h4 : (c : K) = 1 := sq_injective_K _ _ (by rw [h3, one_pow])
  have hc1 : c = 1 := Units.ext h4
  rw [Subgroup.mem_bot, hc1, map_one]

theorem exists_proj_hom {Q : (ι₀ → K) → K} {r : ℕ} {ι : Type} [Fintype ι]
    (h : EARank (K := K) r ι Q) (hC : StatedOmega Q ⊓ StatedScalars ι₀ K = ⊥) :
    ∃ φ : (ι → Multiplicative (ZMod r)) →* StatedProj (StatedOmega Q), Function.Injective φ := by
  obtain ⟨φ, hinj, hmem⟩ := h
  let g := glLin (K := K) (ι₀ := ι₀)
  let φ₁ : (ι → Multiplicative (ZMod r)) →* GL ι₀ K := g.symm.toMonoidHom.comp φ
  have hmem1 : ∀ x, φ₁ x ∈ StatedOmega Q := by
    intro x
    rw [statedOmega_eq]
    refine commutator_map_le g.symm.toMonoidHom ?_ (hmem x)
    rintro _ ⟨f, hf, rfl⟩
    show g (g.symm f) ∈ isoGroup Q
    rw [MulEquiv.apply_symm_apply]
    exact hf
  let φ₂ : (ι → Multiplicative (ZMod r)) →* ↥(StatedOmega Q) :=
    φ₁.codRestrict (StatedOmega Q) hmem1
  refine ⟨(QuotientGroup.mk' ((StatedScalars ι₀ K).subgroupOf (StatedOmega Q))).comp φ₂, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx
  have h1 : φ₁ x ∈ StatedOmega Q ⊓ StatedScalars ι₀ K := ⟨hmem1 x, hx⟩
  rw [hC, Subgroup.mem_bot] at h1
  have h2 : φ x = 1 := by
    have h3 : g.symm (φ x) = 1 := h1
    exact g.symm.injective (by rw [h3, map_one])
  exact hinj (by rw [h2, map_one])

end Projective

section Counting

theorem card_pi_cyclic (ι : Type) [Fintype ι] (r : ℕ) [NeZero r] :
    Nat.card (ι → Multiplicative (ZMod r)) = r ^ Fintype.card ι := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem pow_r_domain (ι : Type) (r : ℕ) [NeZero r] (a : ι → Multiplicative (ZMod r)) :
    a ^ r = 1 := by
  funext i
  show (a i) ^ r = 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_one]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end Counting

section MainLemmas

variable {K : Type} [Field K]

open CFSG.Assembly.LowTwoRank

theorem quadPlus_smul (n : ℕ) (c : K) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K (c • v) = c ^ 2 * StatedQuadPlus n K v := by
  unfold StatedQuadPlus
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem quadPlus_ne (n : ℕ) (hn : 1 ≤ n) : ∃ v : Fin n ⊕ Fin n → K, StatedQuadPlus n K v ≠ 0 := by
  refine ⟨Sum.elim (fun i => if i = ⟨0, hn⟩ then 1 else 0)
    (fun i => if i = ⟨0, hn⟩ then 1 else 0), ?_⟩
  unfold StatedQuadPlus
  simp

theorem quadMinus_smul (n : ℕ) (b c t : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (t • v) = t ^ 2 * StatedQuadMinus n K b c v := by
  unfold StatedQuadMinus
  have h : ∑ i, (t • v) (Sum.inl i) * (t • v) (Sum.inr (Sum.inl i)) =
      t ^ 2 * ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem quadMinus_ne (n : ℕ) (b c : K) :
    ∃ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K, StatedQuadMinus n K b c v ≠ 0 := by
  refine ⟨Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun j => if j = 0 then 1 else 0)), ?_⟩
  unfold StatedQuadMinus
  simp

theorem exists_elementary_abelian_proj {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀]
    {Q : (ι₀ → K) → K} {r : ℕ} [NeZero r] {ι : Type} [Fintype ι] (h : EARank (K := K) r ι Q)
    (hC : StatedOmega Q ⊓ StatedScalars ι₀ K = ⊥) :
    ∃ E : Subgroup (StatedProj (StatedOmega Q)), CFSG.IsElementaryAbelian r ↥E ∧
      Nat.card ↥E = r ^ Fintype.card ι := by
  obtain ⟨φ, hφ⟩ := exists_proj_hom h hC
  refine ⟨φ.range, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_ }
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      exact Subtype.ext (by
        show φ a * φ b = φ b * φ a
        rw [← map_mul, ← map_mul, mul_comm])
    · obtain ⟨_, a, rfl⟩ := x
      exact Subtype.ext (by
        show (φ a) ^ r = 1
        rw [← map_pow, pow_r_domain, map_one])
  · rw [← card_pi_cyclic ι r]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem charP_two_of_card [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

end MainLemmas

section Main

variable {K : Type} [Field K] [Finite K]

open CFSG.Assembly.LowTwoRank

theorem even_orthogonal_plus {f : ℕ} (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K + 1) {n : ℕ} (hn : 1 ≤ n) :
    StatedOmega (StatedQuadPlus n K) ⊓ StatedScalars (Fin n ⊕ Fin n) K = ⊥ ∧
      ∃ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))),
        CFSG.IsElementaryAbelian r ↥E ∧ Nat.card ↥E = r ^ (2 * (n / 2)) := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero r := ⟨hr.ne_zero⟩
  have hC : StatedOmega (StatedQuadPlus n K) ⊓ StatedScalars (Fin n ⊕ Fin n) K = ⊥ :=
    omega_inf_scalars_eq_bot _ (quadPlus_smul n) (quadPlus_ne n hn)
  refine ⟨hC, ?_⟩
  obtain ⟨E, hE, hcard⟩ := exists_elementary_abelian_proj (EARank.quadPlus hr hrq n) hC
  exact ⟨E, hE, by rw [hcard, Fintype.card_fin]⟩

theorem even_orthogonal_minus {f : ℕ} (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : r.Prime)
    (hrq : r ∣ Nat.card K + 1) {n : ℕ} (b c : K) (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus n K b c) ⊓
        StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K = ⊥ ∧
      ∃ E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))),
        CFSG.IsElementaryAbelian r ↥E ∧ Nat.card ↥E = r ^ (1 + 2 * ((n - 1) / 2)) := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero r := ⟨hr.ne_zero⟩
  have hC : StatedOmega (StatedQuadMinus n K b c) ⊓
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K = ⊥ :=
    omega_inf_scalars_eq_bot _ (quadMinus_smul n b c) (quadMinus_ne n b c)
  refine ⟨hC, ?_⟩
  obtain ⟨E, hE, hcard⟩ := exists_elementary_abelian_proj (EARank.quadMinus hr hrq n b c h) hC
  refine ⟨E, hE, ?_⟩
  rw [hcard, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, add_comm]

theorem not_sqt_of_elementary_abelian {G : Type} [Group G] [Finite G] {r k : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hk : 2 < k) (E : Subgroup G) (hE : CFSG.IsElementaryAbelian r ↥E)
    (hcard : Nat.card ↥E = r ^ k) : ¬ CFSG.IsStronglyQuasithin G := by
  intro hsqt
  have := hE
  have hrank := CFSG.SectionRank.le_pRank_of_injective (p := r) hr.one_lt
    (fun a b => hE.toIsMulCommutative.is_comm.comm a b)
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p r ↥E) a)
    hcard E.subtype E.subtype_injective (H := ⊤) le_top
  have hle := (CFSG.SectionRank.isStronglyQuasithin_iff.1 hsqt) r hr hr2
  omega

theorem exists_prime_dvd_card_succ {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card K + 1 ∧ r ≠ 2 := by
  have : CharP K 2 := charP_two_of_card hK
  have h1 : Nat.card K + 1 ≠ 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd h1
  refine ⟨r, hr, hrq, ?_⟩
  have := odd_of_dvd_card_succ hr hrq
  intro h2
  rw [h2] at this
  exact absurd this (by decide)

theorem even_orthogonal_plus_not_sqt {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ} (hn : 4 ≤ n) :
    ¬ CFSG.IsStronglyQuasithin (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  obtain ⟨r, hr, hrq, hr2⟩ := exists_prime_dvd_card_succ hK
  obtain ⟨-, E, hE, hcard⟩ := even_orthogonal_plus hK hr hrq (n := n) (by omega)
  exact not_sqt_of_elementary_abelian hr hr2 (by omega) E hE hcard

theorem even_orthogonal_minus_not_sqt {f : ℕ} (hK : Nat.card K = 2 ^ f) {n : ℕ} (hn : 4 ≤ n)
    (b c : K) (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ CFSG.IsStronglyQuasithin (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  obtain ⟨r, hr, hrq, hr2⟩ := exists_prime_dvd_card_succ hK
  obtain ⟨-, E, hE, hcard⟩ := even_orthogonal_minus hK hr hrq (n := n) b c h
  exact not_sqt_of_elementary_abelian hr hr2 (by omega) E hE hcard

end Main

end CFSG.QuasithinUnique.Setup.Family
