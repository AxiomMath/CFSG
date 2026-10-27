module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

abbrev Block (ℓ : ι → ℕ) (x : ℕ) : Type _ := {a // ℓ a = x}

@[expose] noncomputable def blockMatHom (ℓ : ι → ℕ) (x : ℕ) :
    stdP (K := K) ℓ →* Matrix (Block ℓ x) (Block ℓ x) K where
  toFun g := ((g : SpecialLinearGroup ι K) : Matrix ι ι K).submatrix Subtype.val Subtype.val
  map_one' := by
    ext c a
    change (((1 : stdP (K := K) ℓ) : SpecialLinearGroup ι K) : Matrix ι ι K) c.1 a.1 =
      (1 : Matrix (Block ℓ x) (Block ℓ x) K) c a
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Matrix.one_apply]
    by_cases h : c = a
    · subst h; simp
    · have h' : c.1 ≠ a.1 := fun e => h (Subtype.ext e)
      simp [h, h']
  map_mul' g h := by
    ext c a
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.submatrix_apply,
      Matrix.mul_apply]
    rw [← Fintype.sum_subset (s := Finset.univ.filter fun b => ℓ b = x)
      (f := fun b => ((g : SpecialLinearGroup ι K) : Matrix ι ι K) c.1 b *
        ((h : SpecialLinearGroup ι K) : Matrix ι ι K) b a.1)]
    · exact Finset.sum_subtype _ (by simp) _
    · intro b hb
      by_contra hbx
      have hbx' : ℓ b ≠ x := fun h => hbx (by simp [h])
      apply hb
      rcases Nat.lt_or_gt_of_ne hbx' with hlt | hlt
      · rw [stdP_apply_eq_zero g.2 (by rwa [c.2]), zero_mul]
      · rw [stdP_apply_eq_zero h.2 (by rwa [a.2]), mul_zero]

@[expose] noncomputable def blockHom (ℓ : ι → ℕ) (x : ℕ) : stdP (K := K) ℓ →* GL (Block ℓ x) K :=
  (blockMatHom ℓ x).toHomUnits

theorem coe_blockHom (ℓ : ι → ℕ) (x : ℕ) (g : stdP (K := K) ℓ) :
    ((blockHom ℓ x g : GL (Block ℓ x) K) : Matrix (Block ℓ x) (Block ℓ x) K) =
      ((g : SpecialLinearGroup ι K) : Matrix ι ι K).submatrix Subtype.val Subtype.val :=
  rfl

theorem mem_stdP_of_apply_eq_zero [Finite K] {ℓ : ι → ℕ} {g : SpecialLinearGroup ι K}
    (h : ∀ c a, ℓ a < ℓ c → (g : Matrix ι ι K) c a = 0) : g ∈ stdP ℓ := by
  refine mem_flagStab_of_forall (H := SpecialLinearGroup ι K) slRep ?_
  intro k v hv
  rw [mem_stdFlag]
  intro c hc
  simp only [slRep_apply, mulVec]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hlt : ℓ a < ℓ c
  · simp only [h c a hlt, zero_mul]
  · simp only [hv a (hc.trans (le_of_not_gt hlt)), mul_zero]

theorem stdU_le_stdP (ℓ : ι → ℕ) : stdU (K := K) ℓ ≤ stdP ℓ := by
  simpa [stdU, stdP] using flagKernel_le_flagStab (slRep (ι := ι) (K := K)) (stdFlag ℓ)

theorem mem_stdU_iff_blockHom_eq_one [Finite K] {ℓ : ι → ℕ} (g : stdP (K := K) ℓ) :
    (g : SpecialLinearGroup ι K) ∈ stdU ℓ ↔ ∀ x, blockHom ℓ x g = 1 := by
  constructor
  · intro hU x
    apply Units.ext
    ext c a
    rw [coe_blockHom, Matrix.submatrix_apply]
    have h := (mem_stdU_iff.mp hU) c.1 a.1 (by rw [c.2, a.2]; exact not_lt_of_ge le_rfl)
    rw [h, Matrix.one_apply, Units.val_one, Matrix.one_apply]
    by_cases hca : c = a
    · subst hca; simp
    · have hca' : c.1 ≠ a.1 := fun e => hca (Subtype.ext e)
      simp [hca, hca']
  · intro h
    rw [mem_stdU_iff]
    intro c a hca
    by_cases hlt : ℓ a < ℓ c
    · rw [stdP_apply_eq_zero g.2 hlt, Matrix.one_apply]
      have hne : c ≠ a := fun e => by subst e; exact lt_irrefl _ hlt
      simp [hne]
    · have hlev : ℓ a = ℓ c := le_antisymm (not_lt.mp hca) (not_lt.mp hlt)
      have hblock := congrArg (fun u : GL (Block ℓ (ℓ c)) K =>
        (u : Matrix (Block ℓ (ℓ c)) (Block ℓ (ℓ c)) K) ⟨c, rfl⟩ ⟨a, hlev⟩) (h (ℓ c))
      rw [coe_blockHom, Matrix.submatrix_apply, Units.val_one] at hblock
      rw [hblock, Matrix.one_apply, Matrix.one_apply]
      by_cases hca' : c = a
      · subst hca'; simp
      · have hne : ¬ (⟨c, rfl⟩ : Block ℓ (ℓ c)) = ⟨a, hlev⟩ :=
          fun e => hca' (congrArg Subtype.val e)
        simp [hca', hne]

theorem center_le_stdP [Finite K] (ℓ : ι → ℕ) :
    Subgroup.center (SpecialLinearGroup ι K) ≤ stdP (K := K) ℓ := by
  intro g hg
  refine mem_stdP_of_apply_eq_zero fun c a h => ?_
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [← hr, Matrix.scalar_apply]
  have hne : c ≠ a := fun e => by subst e; exact lt_irrefl _ h
  exact Matrix.diagonal_apply_ne _ hne

theorem blockHom_mem_center {ℓ : ι → ℕ} (x : ℕ) (g : stdP (K := K) ℓ)
    (hg : (g : SpecialLinearGroup ι K) ∈ Subgroup.center (SpecialLinearGroup ι K)) :
    blockHom ℓ x g ∈ Subgroup.center (GL (Block ℓ x) K) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  refine ⟨r, ?_⟩
  ext c a
  rw [coe_blockHom, Matrix.submatrix_apply, ← hr, Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hca : c = a
  · subst hca; simp
  · have hca' : c.1 ≠ a.1 := fun e => hca (Subtype.ext e)
    rw [Matrix.diagonal_apply_ne _ hca, Matrix.diagonal_apply_ne _ hca']

@[expose] noncomputable def blockEmbedFun (ℓ : ι → ℕ) (x : ℕ) :
    SpecialLinearGroup (Block ℓ x) K → SpecialLinearGroup ι K := fun A =>
  ⟨CFSG.AGLEmbedding.LeviBlock.extendMat (φ := Subtype.val) Subtype.val_injective
      (A : Matrix (Block ℓ x) (Block ℓ x) K), by
    rw [CFSG.AGLEmbedding.LeviBlock.det_extendMat (φ := Subtype.val) Subtype.val_injective]
    exact A.2⟩

theorem blockEmbedFun_apply (ℓ : ι → ℕ) (x : ℕ) (A : SpecialLinearGroup (Block ℓ x) K) :
    (blockEmbedFun ℓ x A : Matrix ι ι K) =
      CFSG.AGLEmbedding.LeviBlock.extendMat (φ := Subtype.val) Subtype.val_injective
        (A : Matrix (Block ℓ x) (Block ℓ x) K) :=
  rfl

theorem blockEmbedFun_mul (ℓ : ι → ℕ) (x : ℕ)
    (A B : SpecialLinearGroup (Block ℓ x) K) :
    blockEmbedFun ℓ x (A * B) = blockEmbedFun ℓ x A * blockEmbedFun ℓ x B := by
  apply Subtype.ext
  rw [blockEmbedFun_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    blockEmbedFun_apply, blockEmbedFun_apply]
  exact CFSG.AGLEmbedding.LeviBlock.extendMat_mul (φ := Subtype.val) Subtype.val_injective _ _

@[expose] noncomputable def blockEmbed (ℓ : ι → ℕ) (x : ℕ) :
    SpecialLinearGroup (Block ℓ x) K →* SpecialLinearGroup ι K :=
  MonoidHom.mk' (blockEmbedFun ℓ x) (blockEmbedFun_mul ℓ x)

theorem blockEmbed_apply (ℓ : ι → ℕ) (x : ℕ) (A : SpecialLinearGroup (Block ℓ x) K) (c a : ι) :
    (blockEmbed ℓ x A : Matrix ι ι K) c a =
      if hc : ℓ c = x then
        (if ha : ℓ a = x then
          (A : Matrix (Block ℓ x) (Block ℓ x) K) ⟨c, hc⟩ ⟨a, ha⟩ else 0)
      else (if ℓ a = x then 0 else (1 : Matrix ι ι K) c a) := by
  change (blockEmbedFun ℓ x A : Matrix ι ι K) c a = _
  rw [blockEmbedFun_apply]
  by_cases hc : ℓ c = x
  · rw [dif_pos hc]
    by_cases ha : ℓ a = x
    · rw [dif_pos ha]
      exact CFSG.AGLEmbedding.LeviBlock.extendMat_apply_map
        (φ := (Subtype.val : Block ℓ x → ι)) Subtype.val_injective
        (A : Matrix (Block ℓ x) (Block ℓ x) K) ⟨c, hc⟩ ⟨a, ha⟩
    · rw [dif_neg ha]
      have hca : c ≠ a := fun e => ha (e ▸ hc)
      rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem
        (φ := (Subtype.val : Block ℓ x → ι)) Subtype.val_injective
        (A : Matrix (Block ℓ x) (Block ℓ x) K) (Or.inr ?_)]
      · exact Matrix.one_apply_ne hca
      · rintro ⟨b, hb⟩
        exact ha (hb ▸ b.2)
  · rw [dif_neg hc]
    by_cases ha : ℓ a = x
    · rw [if_pos ha]
      have hca : c ≠ a := fun e => hc (e ▸ ha)
      rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem
        (φ := (Subtype.val : Block ℓ x → ι)) Subtype.val_injective
        (A : Matrix (Block ℓ x) (Block ℓ x) K) (Or.inl ?_)]
      · exact Matrix.one_apply_ne hca
      · rintro ⟨b, hb⟩
        exact hc (hb ▸ b.2)
    · rw [if_neg ha]
      rw [CFSG.AGLEmbedding.LeviBlock.extendMat_apply_of_not_mem
        (φ := (Subtype.val : Block ℓ x → ι)) Subtype.val_injective
        (A : Matrix (Block ℓ x) (Block ℓ x) K) (Or.inl ?_)]
      · rintro ⟨b, hb⟩
        exact hc (hb ▸ b.2)

theorem blockEmbed_mem_stdP [Finite K] (ℓ : ι → ℕ) (x : ℕ) (A : SpecialLinearGroup (Block ℓ x) K) :
    blockEmbed ℓ x A ∈ stdP (K := K) ℓ := by
  refine mem_stdP_of_apply_eq_zero fun c a hlt => ?_
  rw [blockEmbed_apply]
  have hne : c ≠ a := fun e => by subst e; exact lt_irrefl _ hlt
  by_cases hc : ℓ c = x
  · by_cases ha : ℓ a = x
    · exfalso; omega
    · simp [hc, ha]
  · by_cases ha : ℓ a = x
    · simp [hc, ha]
    · simp [hc, ha, Matrix.one_apply_ne hne]

theorem blockHom_blockEmbed [Finite K] (ℓ : ι → ℕ) (x : ℕ) (A : SpecialLinearGroup (Block ℓ x) K) :
    blockHom ℓ x ⟨blockEmbed ℓ x A, blockEmbed_mem_stdP ℓ x A⟩ = SpecialLinearGroup.toGL A := by
  apply Units.ext
  ext c a
  change (blockEmbedFun ℓ x A : Matrix ι ι K) c.1 a.1 =
    ((SpecialLinearGroup.toGL A : GL (Block ℓ x) K) : Matrix (Block ℓ x) (Block ℓ x) K) c a
  rw [blockEmbedFun_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  exact CFSG.AGLEmbedding.LeviBlock.extendMat_apply_map
    (φ := (Subtype.val : Block ℓ x → ι)) Subtype.val_injective
    (A : Matrix (Block ℓ x) (Block ℓ x) K) c a

end CFSG.LieType.BorelTits.RadicalLinear
