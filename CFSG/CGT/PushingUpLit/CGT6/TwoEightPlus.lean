module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightGlue
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightIndex
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightAct
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightCard
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightNat
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOmega

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open CFSG.SL2MinimalFaithful Matrix CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6

section Plus

variable (n : ℕ)

@[expose] noncomputable def plusB : LinearMap.BilinForm (Fq n) (Fq n × Fq n) :=
  LinearMap.mk₂ (Fq n) (fun x y => x.1 * y.2 + x.2 * y.1)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem plusB_apply (x y : Fq n × Fq n) : plusB n x y = x.1 * y.2 + x.2 * y.1 := rfl

@[expose] noncomputable def plusData : Data (Fq n) (Fq n × Fq n) where
  B := plusB n
  Q x := x.1 * x.2
  alt x := by
    rw [plusB_apply, mul_comm x.2 x.1]
    exact F_add_self _
  nondeg := ⟨fun x hx => by
    have h1 := hx (0, 1)
    have h2 := hx (1, 0)
    simp [plusB_apply] at h1 h2
    exact Prod.ext h1 h2, fun y hy => by
    have h1 := hy (0, 1)
    have h2 := hy (1, 0)
    simp [plusB_apply] at h1 h2
    exact Prod.ext h1 h2⟩
  Q_smul c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  Q_add x y := by
    simp only [Prod.fst_add, Prod.snd_add, plusB_apply]
    ring

@[expose] noncomputable def plusCoord : Matrix (Fin 2) (Fin 2) (Fq n) ≃+ Wd (Fq n) (Fq n × Fq n) where
  toFun m := (m 0 0, (m 0 1, m 1 0), m 1 1)
  invFun w := !![w.1, w.2.1.1; w.2.1.2, w.2.2]
  left_inv m := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv w := rfl
  map_add' _ _ := rfl

theorem plusCoord_apply (m : Matrix (Fin 2) (Fin 2) (Fq n)) :
    plusCoord n m = (m 0 0, (m 0 1, m 1 0), m 1 1) := rfl

@[expose] noncomputable def plusMat (g : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (m : Matrix (Fin 2) (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n) :=
  (g.1 : Matrix (Fin 2) (Fin 2) (Fq n)) * m * (g.2 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ

theorem plusMat_one (m : Matrix (Fin 2) (Fin 2) (Fq n)) : plusMat n 1 m = m := by
  simp [plusMat]

theorem plusMat_mul (g h : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (m : Matrix (Fin 2) (Fin 2) (Fq n)) : plusMat n (g * h) m = plusMat n g (plusMat n h m) := by
  simp [plusMat, Matrix.transpose_mul, Matrix.mul_assoc]

@[expose] noncomputable def plusHom :
    SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n) →*
      Equiv.Perm (Wd (Fq n) (Fq n × Fq n)) :=
  actPerm (plusMat n) (plusMat_one n) (plusMat_mul n) (plusCoord n).toEquiv

theorem plusHom_apply (g : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (m : Matrix (Fin 2) (Fin 2) (Fq n)) :
    plusHom n g (plusCoord n m) = plusCoord n (plusMat n g m) :=
  actPerm_apply (plusMat n) (plusMat_one n) (plusMat_mul n) (plusCoord n).toEquiv g m

@[expose] noncomputable def lowerUni (t : Fq n) : SpecialLinearGroup (Fin 2) (Fq n) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerUni (t : Fq n) :
    ((lowerUni n t : SpecialLinearGroup (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)) =
      !![1, 0; t, 1] := rfl

theorem plusHom_unip (x : Fq n × Fq n) :
    plusHom n (unipotent x.1, unipotent x.2) = sigPerm (plusData n) x := by
  ext w : 1
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  rw [plusHom_apply]
  show plusCoord n (plusMat n _ m) = sigFun (plusData n) x (plusCoord n m)
  refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    simp only [plusMat, plusCoord_apply, coe_unipotent, sigFun, plusData, plusB_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem plusHom_lower (x : Fq n × Fq n) :
    plusHom n (lowerUni n x.2, lowerUni n x.1) = lamPerm (plusData n) x := by
  ext w : 1
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  rw [plusHom_apply]
  show plusCoord n (plusMat n _ m) = lamFun (plusData n) x (plusCoord n m)
  refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    simp only [plusMat, plusCoord_apply, coe_lowerUni, lamFun, plusData, plusB_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

theorem plusQt (m : Matrix (Fin 2) (Fin 2) (Fq n)) :
    Qt (plusData n) (plusCoord n m) = m.det := by
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add]
  rfl

theorem plusHom_Q (g : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n))
    (w : Wd (Fq n) (Fq n × Fq n)) : Qt (plusData n) (plusHom n g w) = Qt (plusData n) w := by
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  rw [plusHom_apply, plusQt, plusQt, plusMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    g.1.2, g.2.2, one_mul, mul_one]

theorem plusHom_isAdd (g : SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n)) :
    IsAddPerm (plusHom n g) := by
  intro w w'
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  obtain ⟨m', rfl⟩ := (plusCoord n).surjective w'
  rw [← map_add, plusHom_apply, plusHom_apply, plusHom_apply, ← map_add]
  congr 1
  simp [plusMat, Matrix.mul_add, Matrix.add_mul]

theorem plusHom_injective : Function.Injective (plusHom n) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : ∀ m, plusMat n g m = m := by
    intro m
    have := congrArg (fun τ : Equiv.Perm (Wd (Fq n) (Fq n × Fq n)) => τ (plusCoord n m)) hg
    simp only [Equiv.Perm.coe_one, id] at this
    rw [plusHom_apply] at this
    exact (plusCoord n).injective this
  set A : Matrix (Fin 2) (Fin 2) (Fq n) := (g.1 : Matrix (Fin 2) (Fin 2) (Fq n)) with hA
  set B : Matrix (Fin 2) (Fin 2) (Fq n) := (g.2 : Matrix (Fin 2) (Fin 2) (Fq n)) with hB
  have h1 : A * Bᵀ = 1 := by
    have := h 1
    simpa [plusMat, hA, hB] using this
  have h2 : Bᵀ * A = 1 := mul_eq_one_comm.mp h1
  have hcomm : ∀ m : Matrix (Fin 2) (Fin 2) (Fq n), A * m = m * A := by
    intro m
    have e := h m
    simp only [plusMat, ← hA, ← hB] at e
    calc A * m = A * m * (Bᵀ * A) := by rw [h2, Matrix.mul_one]
      _ = (A * m * Bᵀ) * A := by simp only [Matrix.mul_assoc]
      _ = m * A := by rw [e]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := A)
    (fun i j _ => (hcomm (Matrix.single i j 1)).symm)
  have hdet : c ^ 2 = 1 := by
    have := g.1.2
    rw [← hA, ← hc] at this
    simpa using this
  have hc1 : c = 1 := by
    have hcc : c * c = 1 := by rw [← sq]; exact hdet
    rcases mul_self_eq_one_iff.mp hcc with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  have hA1 : A = 1 := by
    rw [← hc, hc1]
    simp
  have hB1 : B = 1 := by
    have : Bᵀ = 1 := by simpa [hA1] using h1
    simpa using congrArg Matrix.transpose this
  refine Prod.ext (Subtype.ext hA1) (Subtype.ext hB1)

theorem sigPerm_mem_inl (x : Fq n × Fq n) (hx : x.2 = 0) :
    sigPerm (plusData n) x ∈
      ((MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))).range).map
        (plusHom n) := by
  refine ⟨(unipotent x.1, unipotent x.2), ⟨unipotent x.1, ?_⟩, plusHom_unip n x⟩
  rw [hx, unipotent_zero]
  rfl

theorem sigPerm_mem_inr (x : Fq n × Fq n) (hx : x.1 = 0) :
    sigPerm (plusData n) x ∈
      ((MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))).range).map
        (plusHom n) := by
  refine ⟨(unipotent x.1, unipotent x.2), ⟨unipotent x.2, ?_⟩, plusHom_unip n x⟩
  rw [hx, unipotent_zero]
  rfl

theorem alphaOf_snd_eq_zero {a : Equiv.Perm (Wd (Fq n) (Fq n × Fq n))}
    (hn₁ : ∀ g ∈ ((MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n),
      a * g * a⁻¹ ∈ ((MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n))
    (hS : ∀ x, ∃ x', a * sigPerm (plusData n) x * a⁻¹ = sigPerm (plusData n) x')
    (x : Fq n × Fq n) (hx : x.2 = 0) : (alphaOf (plusData n) a x).2 = 0 := by
  have h1 := hn₁ _ (sigPerm_mem_inl n x hx)
  rw [alphaOf_spec (plusData n) (hS x)] at h1
  obtain ⟨s, ⟨y, hy⟩, hs⟩ := h1
  have h2 : plusHom n s = plusHom n (unipotent (alphaOf (plusData n) a x).1,
      unipotent (alphaOf (plusData n) a x).2) := by
    rw [plusHom_unip, hs]
  have h3 := plusHom_injective n h2
  rw [← hy] at h3
  have h4 := congrArg Prod.snd h3
  simp only [MonoidHom.inl_apply] at h4
  have h5 : unipotent (alphaOf (plusData n) a x).2 = unipotent (0 : Fq n) := by
    rw [unipotent_zero]
    exact h4.symm
  exact unipotent_injective h5

theorem alphaOf_fst_eq_zero {a : Equiv.Perm (Wd (Fq n) (Fq n × Fq n))}
    (hn₂ : ∀ g ∈ ((MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n),
      a * g * a⁻¹ ∈ ((MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n))
    (hS : ∀ x, ∃ x', a * sigPerm (plusData n) x * a⁻¹ = sigPerm (plusData n) x')
    (x : Fq n × Fq n) (hx : x.1 = 0) : (alphaOf (plusData n) a x).1 = 0 := by
  have h1 := hn₂ _ (sigPerm_mem_inr n x hx)
  rw [alphaOf_spec (plusData n) (hS x)] at h1
  obtain ⟨s, ⟨y, hy⟩, hs⟩ := h1
  have h2 : plusHom n s = plusHom n (unipotent (alphaOf (plusData n) a x).1,
      unipotent (alphaOf (plusData n) a x).2) := by
    rw [plusHom_unip, hs]
  have h3 := plusHom_injective n h2
  rw [← hy] at h3
  have h4 := congrArg Prod.fst h3
  simp only [MonoidHom.inr_apply] at h4
  have h5 : unipotent (alphaOf (plusData n) a x).1 = unipotent (0 : Fq n) := by
    rw [unipotent_zero]
    exact h4.symm
  exact unipotent_injective h5

theorem plus_hidx (Ā' : Subgroup (Equiv.Perm (Wd (Fq n) (Fq n × Fq n))))
    (hadd : ∀ a ∈ Ā', IsAddPerm a) (hsq : ∀ a ∈ Ā', a * a = 1)
    (hn₁ : ∀ a ∈ Ā', ∀ g ∈ ((MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n),
      a * g * a⁻¹ ∈ ((MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n))
    (hn₂ : ∀ a ∈ Ā', ∀ g ∈ ((MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n),
      a * g * a⁻¹ ∈ ((MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n))
      (SpecialLinearGroup (Fin 2) (Fq n))).range).map (plusHom n))
    (hS : ∀ a ∈ Ā', ∀ x, ∃ x', a * sigPerm (plusData n) x * a⁻¹ = sigPerm (plusData n) x') :
    Nat.card Ā' ≤ 2 * Nat.card ↥(Ā' ⊓ Subgroup.centralizer
      (S0 (plusData n) : Set (Equiv.Perm (Wd (Fq n) (Fq n × Fq n))))) := by
  have hx₁ : ((1 : Fq n), (0 : Fq n)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
  refine card_le_two_mul_inf_of_semilinear (plusData n) (K := Fq n) hadd hsq hS hx₁ ?_ ?_
  · intro a ha
    obtain ⟨g, hg⟩ := (normAdd_alphaOf (plusData n) (hadd a ha) (hsq a ha) (hS a ha)).exists_g hx₁
    exact ⟨g, hg⟩
  · intro a ha hlin
    have hNA := normAdd_alphaOf (plusData n) (hadd a ha) (hsq a ha) (hS a ha)
    have hαα := alphaOf_alphaOf (plusData n) (hsq a ha) (hS a ha)
    have e1 : (alphaOf (plusData n) a (1, 0)).2 = 0 :=
      alphaOf_snd_eq_zero n (hn₁ a ha) (hS a ha) _ rfl
    have e2 : (alphaOf (plusData n) a (0, 1)).1 = 0 :=
      alphaOf_fst_eq_zero n (hn₂ a ha) (hS a ha) _ rfl
    obtain ⟨u₁, hu₁⟩ : ∃ u₁, alphaOf (plusData n) a (1, 0) = (u₁, 0) :=
      ⟨_, Prod.ext rfl e1⟩
    obtain ⟨u₂, hu₂⟩ : ∃ u₂, alphaOf (plusData n) a (0, 1) = (0, u₂) :=
      ⟨_, Prod.ext e2 rfl⟩
    have hu₁1 : u₁ = 1 := by
      have h1 : alphaOf (plusData n) a (u₁, 0) = (u₁ * u₁, 0) := by
        have : ((u₁, 0) : Fq n × Fq n) = u₁ • (1, 0) := by simp
        rw [this, hlin, hu₁]
        simp
      have h2 := hαα (1, 0)
      rw [hu₁, h1] at h2
      have h3 : u₁ * u₁ = 1 := congrArg Prod.fst h2
      rcases mul_self_eq_one_iff.mp h3 with h4 | h4
      · exact h4
      · rw [h4, CharTwo.neg_eq]
    have hu₂1 : u₂ = 1 := by
      have h1 : alphaOf (plusData n) a (0, u₂) = (0, u₂ * u₂) := by
        have : ((0, u₂) : Fq n × Fq n) = u₂ • (0, 1) := by simp
        rw [this, hlin, hu₂]
        simp
      have h2 := hαα (0, 1)
      rw [hu₂, h1] at h2
      have h3 : u₂ * u₂ = 1 := congrArg Prod.snd h2
      rcases mul_self_eq_one_iff.mp h3 with h4 | h4
      · exact h4
      · rw [h4, CharTwo.neg_eq]
    have hα : ∀ x, alphaOf (plusData n) a x = x := by
      intro x
      have hx : x = x.1 • ((1 : Fq n), (0 : Fq n)) + x.2 • ((0 : Fq n), (1 : Fq n)) := by
        ext <;> simp
      rw [hx, hNA.alpha_add, hlin, hlin, hu₁, hu₂, hu₁1, hu₂1]
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h1 := alphaOf_spec (plusData n) (hS a ha x)
    rw [hα x] at h1
    calc sigPerm (plusData n) x * a = (a * sigPerm (plusData n) x * a⁻¹) * a := by rw [h1]
      _ = a * sigPerm (plusData n) x := by group

theorem twoEight_plus {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {E A : Subgroup (MulAut V)} (hn : 2 ≤ n)
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) (hoff : IsOff A)
    (hnat : IsNatSectionBy (omegaPlusAct n) E (commV E) (commV E ⊓ fixV E))
    (hZ : commV E ⊓ fixV E = ⊥) : ⁅E, A⁆ = ⊥ := by
  classical
  rw [hZ] at hnat
  obtain ⟨hPE, θ, β, hβact⟩ := natSection_equiv hnat
  let φ : ↥(commV E) ≃ Wd (Fq n) (Fq n × Fq n) :=
    β.toEquiv.trans (Multiplicative.toAdd.trans (plusCoord n).toEquiv)
  have hφ : ∀ p q : ↥(commV E), φ (p * q) = φ p + φ q := fun p q => by
    show plusCoord n (Multiplicative.toAdd (β (p * q))) =
      plusCoord n (Multiplicative.toAdd (β p)) + plusCoord n (Multiplicative.toAdd (β q))
    rw [map_mul, toAdd_mul, map_add]
  have hAE : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E := fun a ha e he =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) e).mp he
  have hPA : ∀ a ∈ A, ∀ p ∈ commV E, a p ∈ commV E := fun a ha p hp =>
    G6.apply_mem_commV (fun x hx => hAE a ha x hx) hp
  have hF : 3 ≤ Nat.card (Fq n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hequiv : ∀ (e : ↥E) (p : ↥(commV E)) (hp : (e : MulAut V) p ∈ commV E),
      φ ⟨(e : MulAut V) p, hp⟩ = plusHom n (θ e) (φ p) := by
    intro e p hp
    show plusCoord n (Multiplicative.toAdd (β ⟨(e : MulAut V) p, hp⟩)) =
      plusHom n (θ e) (plusCoord n (Multiplicative.toAdd (β p)))
    rw [hβact e p hp, plusHom_apply]
    rfl
  have hx₁ : ((1 : Fq n), (0 : Fq n)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
  have hSmax : ∀ T : Subgroup (SpecialLinearGroup (Fin 2) (Fq n) × SpecialLinearGroup (Fin 2) (Fq n)),
      IsPGroup 2 T → Nat.card T ≤ Nat.card (Fq n × Fq n) := fun T hT => by
    rw [Nat.card_prod, ← sq]
    exact card_le_of_isPGroup_sl2_prod T hT
  have := normal_range_inl (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))
  have := normal_range_inr (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))
  have hq := isQuasisimple_special_linear_two (F := Fq n) (exists_finset_card_four hn)
  have h1 := offender_le_normalizer_of_isComponentOf hV2 hoff hAN
    (isComponentOf_map_range_inl Subgroup.le_normalizer (isSubnormal_normalizer E) θ hq)
  have h2 := offender_le_normalizer_of_isComponentOf hV2 hoff hAN
    (isComponentOf_map_range_inr Subgroup.le_normalizer (isSubnormal_normalizer E) θ hq)
  refine twoEight_of_model (commV E) (plusData n) φ hφ hoff hAE hPE hPA hF θ (plusHom n) hequiv
    (fun x => ⟨(unipotent x.1, unipotent x.2), plusHom_unip n x⟩) hx₁
    ⟨(lowerUni n 0, lowerUni n 1), plusHom_lower n (1, 0)⟩ (plusHom_Q n) (plusHom_isAdd n)
    (plusHom_injective n) hSmax
    (MonoidHom.inl (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))).range
    (MonoidHom.inr (SpecialLinearGroup (Fin 2) (Fq n)) (SpecialLinearGroup (Fin 2) (Fq n))).range
    (transfer_normalizer θ _ h1) (transfer_normalizer θ _ h2) ?_
  intro Ā' hadd hsq _ hn₁ hn₂ hS
  exact plus_hidx n Ā' hadd hsq hn₁ hn₂ hS

end Plus

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
