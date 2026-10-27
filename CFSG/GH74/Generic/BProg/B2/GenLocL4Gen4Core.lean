module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4Red

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

open CFSG CFSG.GH74 Subgroup Matrix

section Stab

variable {F : Type*} [Field F]

theorem stab_mul_rel {g h y : Matrix (Fin 2) (Fin 2) F} {c d : F} (hc : g * y = c • (y * g))
    (hd : h * y = d • (y * h)) : g * h * y = (d * c) • (y * (g * h)) := by
  rw [Matrix.mul_assoc, hd, Matrix.mul_smul, ← Matrix.mul_assoc, hc, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc]

theorem stab_unique {g y : GL (Fin 2) F} {c c' : Fˣ}
    (h : (g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)))
    (h' : (g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (c' : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))) : c = c' := by
  have h1 : (c : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) =
      (c' : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := h.symm.trans h'
  have hM : ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
      (((y * g)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := Units.mul_inv (y * g)
    rwa [Units.val_mul] at this
  have h2 := congrArg (fun M => M * (((y * g)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h1
  simp only [Matrix.smul_mul, hM] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
  exact Units.ext h3

def Stab (y : GL (Fin 2) F) : Subgroup (GL (Fin 2) F) where
  carrier := {g | ∃ c : Fˣ, (g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
    (c : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [Units.val_mul]; exact stab_mul_rel hc hd⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have h1 : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h3 : (y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        ((c⁻¹ : Fˣ) : F) • ((g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F)) := by
      rw [hc, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero, one_smul]
    calc ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F)
        = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) *
            ((g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [h1, Matrix.mul_one]
      _ = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          simp only [Matrix.mul_assoc]
      _ = ((c⁻¹ : Fˣ) : F) • ((y : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [h3, Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

noncomputable def lam (y : GL (Fin 2) F) : Stab y →* Fˣ where
  toFun g := g.2.choose
  map_one' := stab_unique (Classical.choose_spec (1 : Stab y).2) (by simp)
  map_mul' g h := by
    apply stab_unique (Classical.choose_spec (g * h : Stab y).2)
    rw [mul_comm, Units.val_mul]
    exact stab_mul_rel (Classical.choose_spec g.2) (Classical.choose_spec h.2)

theorem lam_eq {y : GL (Fin 2) F} (g : Stab y) {c : Fˣ}
    (h : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • ((y : Matrix (Fin 2) (Fin 2) F) * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) :
    lam y g = c :=
  stab_unique (Classical.choose_spec g.2) h

open scoped Classical in
noncomputable def lamf (y g : GL (Fin 2) F) : Fˣ := if h : g ∈ Stab y then lam y ⟨g, h⟩ else 1

theorem lamf_eq {y g : GL (Fin 2) F} {c : Fˣ}
    (h : (g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • ((y : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))) : lamf y g = c := by
  have hg : g ∈ Stab y := ⟨c, h⟩
  simp only [lamf, hg, ↓reduceDIte]
  exact lam_eq ⟨g, hg⟩ h

theorem lamf_one {y : GL (Fin 2) F} : lamf y 1 = 1 := lamf_eq (by simp)

theorem lamf_mul {y g h : GL (Fin 2) F} (hg : g ∈ Stab y) (hh : h ∈ Stab y) :
    lamf y (g * h) = lamf y g * lamf y h := by
  simp only [lamf, hg, hh, mul_mem hg hh, ↓reduceDIte]
  exact map_mul (lam y) (⟨g, hg⟩ : Stab y) ⟨h, hh⟩

end Stab

section Core

variable {F : Type*} [Field F]

@[expose] def mkGL (M N : Matrix (Fin 2) (Fin 2) F) (h1 : M * N = 1) (h2 : N * M = 1) : GL (Fin 2) F :=
  ⟨M, N, h1, h2⟩

@[simp] theorem val_mkGL (M N : Matrix (Fin 2) (Fin 2) F) (h1 : M * N = 1) (h2 : N * M = 1) :
    (mkGL M N h1 h2 : Matrix (Fin 2) (Fin 2) F) = M := rfl

variable (i : F) (hi : i * i = -1)

@[expose] def gX : GL (Fin 2) F := mkGL !![0, 1; 1, 0] !![0, 1; 1, 0]
  (by ext a b; fin_cases a <;> fin_cases b <;> simp)
  (by ext a b; fin_cases a <;> fin_cases b <;> simp)

@[expose] def gZ : GL (Fin 2) F := mkGL !![1, 0; 0, -1] !![1, 0; 0, -1]
  (by ext a b; fin_cases a <;> fin_cases b <;> simp)
  (by ext a b; fin_cases a <;> fin_cases b <;> simp)

include hi in
@[expose] def gZR : GL (Fin 2) F := mkGL !![i, 0; 0, -i] !![-i, 0; 0, i]
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)

include hi in
@[expose] def gXR : GL (Fin 2) F := mkGL !![0, i; i, 0] !![0, -i; -i, 0]
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)

include hi in
@[expose] def gR : GL (Fin 2) F := mkGL !![i, 0; 0, i] !![-i, 0; 0, -i]
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)
  (by ext a b; fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : F) * hi)

theorem relX_ZR : ((gZR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gX : GL (Fin 2) F) =
    ((-1 : Fˣ) : F) • ((gX : GL (Fin 2) F) * (gZR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gZR, gX, Matrix.mul_apply, Fin.sum_univ_two]

theorem relX_XR : ((gXR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gX : GL (Fin 2) F) =
    ((1 : Fˣ) : F) • ((gX : GL (Fin 2) F) * (gXR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gXR, gX, Matrix.mul_apply, Fin.sum_univ_two]

theorem relX_R : ((gR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gX : GL (Fin 2) F) =
    ((1 : Fˣ) : F) • ((gX : GL (Fin 2) F) * (gR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gR, gX, Matrix.mul_apply, Fin.sum_univ_two]

theorem relZ_ZR : ((gZR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gZ : GL (Fin 2) F) =
    ((1 : Fˣ) : F) • ((gZ : GL (Fin 2) F) * (gZR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gZR, gZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem relZ_XR : ((gXR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gZ : GL (Fin 2) F) =
    ((-1 : Fˣ) : F) • ((gZ : GL (Fin 2) F) * (gXR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gXR, gZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem relZ_R : ((gR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gZ : GL (Fin 2) F) =
    ((1 : Fˣ) : F) • ((gZ : GL (Fin 2) F) * (gR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gR, gZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_gZR : (gZR i hi : GL (Fin 2) F).val.det = 1 := by
  simp [gZR, Matrix.det_fin_two]; linear_combination (-1 : F) * hi

theorem det_gXR : (gXR i hi : GL (Fin 2) F).val.det = 1 := by
  simp [gXR, Matrix.det_fin_two]; linear_combination (-1 : F) * hi

theorem det_gR : (gR i hi : GL (Fin 2) F).val.det = -1 := by
  simp [gR, Matrix.det_fin_two]; exact hi

@[expose] def gens : Set (GL (Fin 2) F × GL (Fin 2) F) :=
  {(gZR i hi, 1), (gXR i hi, 1), (1, gZR i hi), (1, gXR i hi), (gR i hi, 1)}

@[expose] def K₀ : Subgroup (GL (Fin 2) F × GL (Fin 2) F) := closure (gens i hi)

theorem gZR_mem : gZR i hi ∈ (Stab gX ⊓ Stab gZ : Subgroup (GL (Fin 2) F)) :=
  ⟨⟨-1, relX_ZR i hi⟩, ⟨1, relZ_ZR i hi⟩⟩

theorem gXR_mem : gXR i hi ∈ (Stab gX ⊓ Stab gZ : Subgroup (GL (Fin 2) F)) :=
  ⟨⟨1, relX_XR i hi⟩, ⟨-1, relZ_XR i hi⟩⟩

theorem gR_mem : gR i hi ∈ (Stab gX ⊓ Stab gZ : Subgroup (GL (Fin 2) F)) :=
  ⟨⟨1, relX_R i hi⟩, ⟨1, relZ_R i hi⟩⟩

theorem K₀_le : K₀ i hi ≤ (Stab gX ⊓ Stab gZ : Subgroup (GL (Fin 2) F)).prod
    (Stab gX ⊓ Stab gZ : Subgroup (GL (Fin 2) F)) := by
  rw [K₀, closure_le]
  intro x hx
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
  · exact gZR_mem i hi
  · exact one_mem _
  · exact gXR_mem i hi
  · exact one_mem _
  · exact one_mem _
  · exact gZR_mem i hi
  · exact one_mem _
  · exact gXR_mem i hi
  · exact gR_mem i hi
  · exact one_mem _

noncomputable def psi : K₀ i hi →* (Fin 5 → Fˣ) where
  toFun k := ![lamf gX k.1.1, lamf gZ k.1.1, lamf gX k.1.2, lamf gZ k.1.2,
    Matrix.GeneralLinearGroup.det k.1.1 * Matrix.GeneralLinearGroup.det k.1.2]
  map_one' := by
    funext l
    fin_cases l <;> simp [lamf_one]
  map_mul' k k' := by
    have h := Subgroup.mem_prod.1 (K₀_le i hi k.2)
    have h' := Subgroup.mem_prod.1 (K₀_le i hi k'.2)
    funext l
    fin_cases l
    · exact lamf_mul h.1.1 h'.1.1
    · exact lamf_mul h.1.2 h'.1.2
    · exact lamf_mul h.2.1 h'.2.1
    · exact lamf_mul h.2.2 h'.2.2
    · show (_ : Fˣ) * _ = ((_ : Fˣ) * _) * ((_ : Fˣ) * _)
      simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
      exact mul_mul_mul_comm _ _ _ _

theorem det_eq_of {g : GL (Fin 2) F} {c : Fˣ} (h : (g : Matrix (Fin 2) (Fin 2) F).det = c) :
    (Matrix.GeneralLinearGroup.det g : Fˣ) = c := Units.ext (by simpa using h)

def kZR1 : K₀ i hi := ⟨(gZR i hi, 1), subset_closure (by simp [gens])⟩
def kXR1 : K₀ i hi := ⟨(gXR i hi, 1), subset_closure (by simp [gens])⟩
def kZR2 : K₀ i hi := ⟨(1, gZR i hi), subset_closure (by simp [gens])⟩
def kXR2 : K₀ i hi := ⟨(1, gXR i hi), subset_closure (by simp [gens])⟩
def kR1 : K₀ i hi := ⟨(gR i hi, 1), subset_closure (by simp [gens])⟩

theorem psi_kZR1 : psi i hi (kZR1 i hi) = ![-1, 1, 1, 1, 1] := by
  funext l
  fin_cases l
  · exact lamf_eq (relX_ZR i hi)
  · exact lamf_eq (relZ_ZR i hi)
  · exact lamf_one
  · exact lamf_one
  · show Matrix.GeneralLinearGroup.det (gZR i hi) * Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) F) = 1
    rw [map_one, mul_one]
    exact det_eq_of (det_gZR i hi)

theorem psi_kXR1 : psi i hi (kXR1 i hi) = ![1, -1, 1, 1, 1] := by
  funext l
  fin_cases l
  · exact lamf_eq (relX_XR i hi)
  · exact lamf_eq (relZ_XR i hi)
  · exact lamf_one
  · exact lamf_one
  · show Matrix.GeneralLinearGroup.det (gXR i hi) * Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) F) = 1
    rw [map_one, mul_one]
    exact det_eq_of (det_gXR i hi)

theorem psi_kZR2 : psi i hi (kZR2 i hi) = ![1, 1, -1, 1, 1] := by
  funext l
  fin_cases l
  · exact lamf_one
  · exact lamf_one
  · exact lamf_eq (relX_ZR i hi)
  · exact lamf_eq (relZ_ZR i hi)
  · show Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) F) * Matrix.GeneralLinearGroup.det (gZR i hi) = 1
    rw [map_one, one_mul]
    exact det_eq_of (det_gZR i hi)

theorem psi_kXR2 : psi i hi (kXR2 i hi) = ![1, 1, 1, -1, 1] := by
  funext l
  fin_cases l
  · exact lamf_one
  · exact lamf_one
  · exact lamf_eq (relX_XR i hi)
  · exact lamf_eq (relZ_XR i hi)
  · show Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) F) * Matrix.GeneralLinearGroup.det (gXR i hi) = 1
    rw [map_one, one_mul]
    exact det_eq_of (det_gXR i hi)

theorem psi_kR1 : psi i hi (kR1 i hi) = ![1, 1, 1, 1, -1] := by
  funext l
  fin_cases l
  · exact lamf_eq (relX_R i hi)
  · exact lamf_eq (relZ_R i hi)
  · exact lamf_one
  · exact lamf_one
  · show Matrix.GeneralLinearGroup.det (gR i hi) * Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) F) = -1
    rw [map_one, mul_one]
    exact det_eq_of (det_gR i hi)

theorem psi_sq (k : K₀ i hi) : psi i hi k ^ 2 = 1 := by
  have key : ∀ v : Fin 5 → Fˣ, (∀ l, v l = 1 ∨ v l = -1) → v ^ 2 = 1 := by
    intro v hv
    funext l
    rcases hv l with h | h <;> simp [h]
  refine Subgroup.closure_induction (p := fun x hx => psi i hi ⟨x, hx⟩ ^ 2 = 1) ?_ ?_ ?_ ?_ k.2
  · intro x hx
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · show psi i hi (kZR1 i hi) ^ 2 = 1
      rw [psi_kZR1]
      exact key _ (fun l => by fin_cases l <;> simp)
    · show psi i hi (kXR1 i hi) ^ 2 = 1
      rw [psi_kXR1]
      exact key _ (fun l => by fin_cases l <;> simp)
    · show psi i hi (kZR2 i hi) ^ 2 = 1
      rw [psi_kZR2]
      exact key _ (fun l => by fin_cases l <;> simp)
    · show psi i hi (kXR2 i hi) ^ 2 = 1
      rw [psi_kXR2]
      exact key _ (fun l => by fin_cases l <;> simp)
    · show psi i hi (kR1 i hi) ^ 2 = 1
      rw [psi_kR1]
      exact key _ (fun l => by fin_cases l <;> simp)
  · show psi i hi 1 ^ 2 = 1
    rw [map_one, one_pow]
  · intro x y hx hy ihx ihy
    show psi i hi (⟨x, hx⟩ * ⟨y, hy⟩) ^ 2 = 1
    rw [map_mul, mul_pow, ihx, ihy, one_mul]
  · intro x hx ihx
    show psi i hi (⟨x, hx⟩ : K₀ i hi)⁻¹ ^ 2 = 1
    rw [map_inv, inv_pow, ihx, inv_one]

@[expose] def blk (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

theorem blk_mul (A B A' B' : Matrix (Fin 2) (Fin 2) F) :
    blk A B * blk A' B' = blk (A * A') (B * B') := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blk]

theorem det_blk (A B : Matrix (Fin 2) (Fin 2) F) : (blk A B).det = A.det * B.det := by
  simp [blk, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem blk_eq_scalar {A B : Matrix (Fin 2) (Fin 2) F} {c : F}
    (h : blk A B = Matrix.scalar (Fin 4) c) : A = c • 1 ∧ B = c • 1 := by
  have h' := fun a b => congrFun (congrFun h a) b
  constructor
  · ext a b
    fin_cases a <;> fin_cases b
    · simpa [blk] using h' 0 0
    · simpa [blk] using h' 0 1
    · simpa [blk] using h' 1 0
    · simpa [blk] using h' 1 1
  · ext a b
    fin_cases a <;> fin_cases b
    · simpa [blk] using h' 2 2
    · simpa [blk] using h' 2 3
    · simpa [blk] using h' 3 2
    · simpa [blk] using h' 3 3

@[expose] def Θ : GL (Fin 2) F × GL (Fin 2) F →* GL (Fin 4) F where
  toFun p := ⟨blk (p.1 : Matrix (Fin 2) (Fin 2) F) p.2, blk ((p.1⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      ((p.2⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
    by rw [blk_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, mul_inv_cancel, Units.val_one,
      blk_one],
    by rw [blk_mul, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel, Units.val_one,
      blk_one]⟩
  map_one' := Units.ext (by simpa using blk_one)
  map_mul' p q := Units.ext (by
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul]
    exact (blk_mul _ _ _ _).symm)

theorem Θ_val (p : GL (Fin 2) F × GL (Fin 2) F) :
    ((Θ p : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk (p.1 : Matrix (Fin 2) (Fin 2) F) p.2 := rfl

theorem card_range_psi [Finite F] (hne : (-1 : F) ≠ 1) : 2 ^ 5 ≤ Nat.card (psi i hi).range := by
  have hne' : (-1 : Fˣ) ≠ 1 := fun h => hne (by simpa using congrArg Units.val h)
  refine two_pow_le_card_of_mulSingle_mem hne' _ fun l => ?_
  fin_cases l
  · refine ⟨kZR1 i hi, ?_⟩
    rw [psi_kZR1]
    funext j
    fin_cases j <;> simp
  · refine ⟨kXR1 i hi, ?_⟩
    rw [psi_kXR1]
    funext j
    fin_cases j <;> simp
  · refine ⟨kZR2 i hi, ?_⟩
    rw [psi_kZR2]
    funext j
    fin_cases j <;> simp
  · refine ⟨kXR2 i hi, ?_⟩
    rw [psi_kXR2]
    funext j
    fin_cases j <;> simp
  · refine ⟨kR1 i hi, ?_⟩
    rw [psi_kR1]
    funext j
    fin_cases j <;> simp

theorem det_Θ_sq (k : K₀ i hi) :
    (((Θ (k : GL (Fin 2) F × GL (Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det) ^ 2 = 1 := by
  have h2 : (Matrix.GeneralLinearGroup.det k.1.1 * Matrix.GeneralLinearGroup.det k.1.2) ^ 2 = 1 :=
    congrFun (psi_sq i hi k) 4
  have h3 := congrArg Units.val h2
  rw [Θ_val, det_blk]
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using h3

theorem det_Θ_eq (k : K₀ i hi) :
    (((Θ (k : GL (Fin 2) F × GL (Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det) = 1 ∨
    (((Θ (k : GL (Fin 2) F × GL (Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det) = -1 :=
  mul_self_eq_one_iff.1 (by rw [← sq]; exact det_Θ_sq i hi k)

theorem psi_eq_one_of_scalar (k : K₀ i hi) (c : Fˣ)
    (h : Θ (k : GL (Fin 2) F × GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 4) c)
    (hc : (c : F) ^ 4 ≠ -1) : psi i hi k = 1 := by
  have hb : blk (k.1.1 : Matrix (Fin 2) (Fin 2) F) (k.1.2 : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 4) (c : F) := by
    have := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h
    simpa [Θ_val, Matrix.GeneralLinearGroup.coe_scalar] using this
  obtain ⟨hA, hB⟩ := blk_eq_scalar hb
  have hcomm : ∀ (y g : GL (Fin 2) F), (g : Matrix (Fin 2) (Fin 2) F) = (c : F) • 1 → lamf y g = 1 := by
    intro y g hg
    refine lamf_eq ?_
    rw [hg]
    simp
  have hdet : ((Θ (k : GL (Fin 2) F × GL (Fin 2) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (c : F) ^ 4 := by
    rw [h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    simp
  have h4 : (c : F) ^ 4 = 1 := by
    have h1 := det_Θ_eq i hi k
    rw [hdet] at h1
    exact h1.resolve_right hc
  funext l
  fin_cases l
  · exact hcomm _ _ hA
  · exact hcomm _ _ hA
  · exact hcomm _ _ hB
  · exact hcomm _ _ hB
  · show Matrix.GeneralLinearGroup.det k.1.1 * Matrix.GeneralLinearGroup.det k.1.2 = 1
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      ← det_blk, hb, Matrix.scalar_apply, Matrix.det_diagonal]
    simpa using h4

theorem pow_four_ne_neg_one {m : ℕ} (hm : m % 8 = 4) (hne : (-1 : F) ≠ 1) {c : F} (hc : c ^ m = 1) :
    c ^ 4 ≠ -1 := by
  intro h
  obtain ⟨j, rfl⟩ : ∃ j, m = 4 * (2 * j + 1) := ⟨m / 8, by omega⟩
  rw [pow_mul, h, Odd.neg_one_pow (by simp)] at hc
  exact hne hc

end Core

@[expose] def refl4 (F : Type*) [Field F] : GL (Fin 4) F :=
  ⟨Matrix.diagonal ![-1, 1, 1, 1], Matrix.diagonal ![-1, 1, 1, 1],
    by rw [Matrix.diagonal_mul_diagonal]; ext a b; fin_cases a <;> fin_cases b <;> simp,
    by rw [Matrix.diagonal_mul_diagonal]; ext a b; fin_cases a <;> fin_cases b <;> simp⟩

theorem coe_refl4 (F : Type*) [Field F] :
    ((refl4 F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![-1, 1, 1, 1] := rfl

end CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4
