module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def diagGen (a : Fin 3 → Kˣ) : GL (Fin 6) K :=
  ⟨Matrix.diagonal ![(a 0 : K), (a 1 : K), (a 2 : K), ((a 0)⁻¹ : Kˣ), ((a 1)⁻¹ : Kˣ), ((a 2)⁻¹ : Kˣ)],
    Matrix.diagonal ![((a 0)⁻¹ : Kˣ), ((a 1)⁻¹ : Kˣ), ((a 2)⁻¹ : Kˣ), (a 0 : K), (a 1 : K), (a 2 : K)],
    by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext i
      fin_cases i <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext i
      fin_cases i <;> simp⟩

theorem diagGen_val (a : Fin 3 → Kˣ) :
    ((diagGen a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal ![(a 0 : K), (a 1 : K), (a 2 : K), ((a 0)⁻¹ : Kˣ), ((a 1)⁻¹ : Kˣ),
        ((a 2)⁻¹ : Kˣ)] := rfl

@[expose] noncomputable def diagGenHom : (Fin 3 → Kˣ) →* GL (Fin 6) K where
  toFun := diagGen
  map_one' := by
    apply Units.ext
    rw [diagGen_val, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  map_mul' x y := by
    apply Units.ext
    rw [Units.val_mul, diagGen_val, diagGen_val, diagGen_val, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem diagGenHom_apply (a : Fin 3 → Kˣ) : diagGenHom a = diagGen a := rfl

theorem diagGen_injective : Function.Injective (diagGenHom (K := K)) := by
  intro a b h
  have h0 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) 0 0) h
  have h1 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) 1 1) h
  have h2 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K)) 2 2) h
  simp only [diagGenHom_apply, diagGen_val, Matrix.diagonal_apply_eq] at h0 h1 h2
  funext k
  fin_cases k
  · exact Units.ext (by simpa using h0)
  · exact Units.ext (by simpa using h1)
  · exact Units.ext (by simpa using h2)

theorem diagU_eq_diagGen (a c : Kˣ) : diagU (K := K) a c = diagGen ![a, a, c] := by
  apply Units.ext
  rw [diagU_val, diagGen_val]
  simp

@[expose] def Dhom (K : Type) [Field K] : (Fin 3 → mu3U K) →* (Fin 3 → Kˣ) :=
  MonoidHom.pi (fun k => (mu3U K).subtype.comp (Pi.evalMonoidHom (fun _ : Fin 3 => mu3U K) k))

theorem Dhom_injective (K : Type) [Field K] : Function.Injective (Dhom K) := by
  intro x y hxy
  funext k
  apply Subtype.ext
  have := congrFun hxy k
  simpa [Dhom] using this

@[expose] noncomputable def Dfull (K : Type) [Field K] : Subgroup (GL (Fin 6) K) :=
  (diagGenHom.comp (Dhom K)).range

@[expose] noncomputable def diagGL3g (a : Fin 3 → Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a 0 : K), (a 1 : K), (a 2 : K)])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp)

theorem diagGL3g_val (a : Fin 3 → Kˣ) :
    ((diagGL3g a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a 0 : K), (a 1 : K), (a 2 : K)] := rfl

theorem diagGL3g_inv_val (a : Fin 3 → Kˣ) :
    (((diagGL3g a)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun k : Fin 3 => (((a k)⁻¹ : Kˣ) : K)) := by
  rw [Matrix.coe_units_inv, diagGL3g_val]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem lowBlk_diagGL3g (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (a : Fin 3 → Kˣ) (ha : ∀ k, a k ^ 3 = 1) :
    lowBlk h (diagGL3g a) = Matrix.diagonal (fun k : Fin 3 => (((a k)⁻¹ : Kˣ) : K)) := by
  unfold lowBlk
  rw [diagGL3g_inv_val, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
  congr 1
  funext k
  have hk : (((a k)⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, ha k, inv_one, Units.val_one]
  exact hbar _ hk

theorem diagGen_eq_Mh (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (a : Fin 3 → Kˣ) (ha : ∀ k, a k ^ 3 = 1) :
    diagGen a = Mh h (diagGL3g a) := by
  apply Units.ext
  rw [diagGen_val, Mh_val, diagGL3g_val, diag_blk, lowBlk_diagGL3g h hbar a ha]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

theorem diagGL3g_det_bar (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (a : Fin 3 → Kˣ) (ha : ∀ k, a k ^ 3 = 1) :
    h.bar ((diagGL3g a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((diagGL3g a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
  rw [diagGL3g_val, Matrix.det_diagonal, Fin.prod_univ_three, map_mul, map_mul]
  have hk : ∀ k, h.bar ((a k : Kˣ) : K) = ((a k : Kˣ) : K) := fun k =>
    hbar _ (by rw [← Units.val_pow_eq_pow_val, ha k, Units.val_one])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [hk 0, hk 1, hk 2]

theorem diagGen_mem (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (a : Fin 3 → Kˣ) (ha : ∀ k, a k ^ 3 = 1) :
    diagGen a ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rw [diagGen_eq_Mh h hbar a ha]
  exact Mh_mem_of_bar h _ (diagGL3g_det_bar h hbar a ha)

theorem hypJ_ie0_jf0 : (hypJ : Matrix (Fin 6) (Fin 6) K) (ie 0) (jf 0) = 1 := by
  unfold hypJ
  rw [blk_lr]
  simp

theorem scalar_mul_hypJ (x : K) : Matrix.scalar (Fin 6) x * (hypJ : Matrix (Fin 6) (Fin 6) K) =
    x • (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem hypJ_mul_scalar (y : K) : (hypJ : Matrix (Fin 6) (Fin 6) K) * Matrix.scalar (Fin 6) y =
    y • (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

theorem bar_mul_eq_one_of_scalar (h : UnitaryFieldData p f K) {g : GL (Fin 6) K}
    (hg : g ∈ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) {c : K}
    (hc : (g : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) c) : h.bar c * c = 1 := by
  have hiso := (mem_gramSU.mp hg).1
  rw [hc] at hiso
  have hm : (Matrix.scalar (Fin 6) c).map h.bar = Matrix.scalar (Fin 6) (h.bar c) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar)]
  have ht : ∀ x : K, (Matrix.scalar (Fin 6) x)ᵀ = Matrix.scalar (Fin 6) x := fun x => by
    rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [hm, ht] at hiso
  have e : Matrix.scalar (Fin 6) (h.bar c) * (hypJ : Matrix (Fin 6) (Fin 6) K) *
      Matrix.scalar (Fin 6) c = (c * h.bar c) • (hypJ : Matrix (Fin 6) (Fin 6) K) := by
    rw [mul_assoc, hypJ_mul_scalar, Matrix.mul_smul, scalar_mul_hypJ, smul_smul]
  rw [e] at hiso
  have := congrFun (congrFun hiso (ie 0)) (jf 0)
  rw [Matrix.smul_apply, hypJ_ie0_jf0, smul_eq_mul, mul_one] at this
  rw [mul_comm]
  exact this

theorem Psi_ie2_ie2 (h : UnitaryFieldData p f K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((Psi h X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) (ie 2) (ie 2) = 1 := by
  rw [Psi_apply, PsiGL_apply, Mh_val, blk_ll, emb3GL_val]
  simp [emb3]

theorem Psi_scalar_one (h : UnitaryFieldData p f K) (X : Matrix.SpecialLinearGroup (Fin 2) K)
    {c : K} (hc : ((Psi h X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) c) :
    c = 1 := by
  have e := congrFun (congrFun hc (ie 2)) (ie 2)
  rw [Psi_ie2_ie2] at e
  simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using e.symm

@[expose] noncomputable def PsiJ (h : UnitaryFieldData p f K) :
    Matrix.SpecialLinearGroup (Fin 2) K →* gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) :=
  MonoidHom.codRestrict (Psi h) _ (fun X => Psi_mem h X)

theorem PsiJ_coe (h : UnitaryFieldData p f K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((PsiJ h X : gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) : GL (Fin 6) K) = Psi h X := rfl

abbrev PSUJ (h : UnitaryFieldData p f K) : Type :=
  StatedProj (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))

@[expose] noncomputable def piJ (h : UnitaryFieldData p f K) :
    gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) →* PSUJ h :=
  QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)))

theorem piJ_eq_one_iff (h : UnitaryFieldData p f K) (x : gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) :
    piJ h x = 1 ↔ ∃ c : K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) c := by
  unfold piJ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨(u : K), ?_⟩
    rw [← Matrix.GeneralLinearGroup.coe_scalar] at *
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hu
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this.symm
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro h0
      have hd := det_ne_zero_of_GL (x : GL (Fin 6) K)
      rw [hc, h0] at hd
      simp at hd
    exact MonoidHom.mem_range.mpr ⟨Units.mk0 c hc0, Units.ext (by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hc])⟩

theorem comm_of_lift (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (x f : gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)) (hf3 : f ^ 3 = 1)
    (hc : piJ h x * piJ h f = piJ h f * piJ h x) : x * f = f * x := by
  set w : gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := x * f * x⁻¹ * f⁻¹ with hw
  have hw1 : piJ h w = 1 := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv]
    have : piJ h x * piJ h f * (piJ h x)⁻¹ * (piJ h f)⁻¹ = 1 := by
      rw [hc]
      group
    exact this
  obtain ⟨c, hcw⟩ := (piJ_eq_one_iff h w).mp hw1
  have hwf : w * f = x * f * x⁻¹ := by rw [hw]; group
  have hcomm : w * f = f * w := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    show ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * ((f : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((f : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [hcw]
    exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq
  have hxf3 : (x * f * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hf3, mul_one, mul_inv_cancel]
  have hw3 : w ^ 3 = 1 := by
    have h1 : (w * f) ^ 3 = w ^ 3 * f ^ 3 := Commute.mul_pow hcomm 3
    rw [hf3, mul_one, hwf, hxf3] at h1
    exact h1.symm
  have hc3 : c ^ 3 = 1 := by
    have h2 : (((w : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
      have := congrArg (fun g : gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) =>
        ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hw3
      simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
    rw [hcw, Matrix.scalar_apply, Matrix.diagonal_pow] at h2
    simpa [Matrix.diagonal_apply_eq] using congrFun (congrFun h2 0) 0
  have hcc : h.bar c * c = 1 := bar_mul_eq_one_of_scalar h w.2 hcw
  have hc1 : c = 1 := by
    have hb := hbar c hc3
    rw [hb] at hcc
    have h3 : c ^ 3 = c := by
      rw [show c ^ 3 = c * (c * c) by ring, hcc, mul_one]
    rw [← h3, hc3]
  have hw_one : w = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_one, Units.val_one, hcw, hc1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  have key : x * f * x⁻¹ * f⁻¹ = 1 := by
    rw [← hw, hw_one]
  calc x * f = (x * f * x⁻¹ * f⁻¹) * (f * x) := by group
    _ = f * x := by rw [key, one_mul]

theorem Dfull_card (K : Type) [Field K] (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3) :
    Nat.card (Dfull K) = 27 := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hinj : Function.Injective (diagGenHom.comp (Dhom K) : (Fin 3 → mu3U K) →* GL (Fin 6) K) :=
    diagGen_injective.comp (Dhom_injective K)
  unfold Dfull
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_pi]
  have hμ : Nat.card (mu3U K) = 3 := card_mu3 K hζ
  simp only [hμ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem Dfull_le (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x) :
    Dfull K ≤ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) := by
  rintro g ⟨a, rfl⟩
  apply diagGen_mem h hbar
  intro k
  exact (mem_rootsOfUnity 3 _).mp (a k).2

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
