module

public import CFSG.LieType.Multipliers.Sz8Field
public import CFSG.Models
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LieType.Multipliers.Sz8

open Matrix TauCeti

local notation "GF" => GaloisField 2 (2 * 1 + 1)

section Ring

variable {K L : Type*} [CommRing K] [CommRing L]

@[expose] def rootMat (a b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; a, 1, 0, 0; a * a ^ 4 + b, a ^ 4, 1, 0; a ^ 2 * a ^ 4 + a * b + b ^ 4, b, a, 1]

@[expose] def weylMat : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem map_rootMat (f : K →+* L) (a b : K) : (rootMat a b).map f = rootMat (f a) (f b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem map_weylMat (f : K →+* L) : (weylMat : Matrix (Fin 4) (Fin 4) K).map f = weylMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat]

end Ring

theorem rootMat_eq_unipotentMatrix (a b : GF) : rootMat a b = Suzuki.unipotentMatrix 1 a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem weylMat_eq_weylMatrix : (weylMat : Matrix (Fin 4) (Fin 4) GF) = Suzuki.weylMatrix 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat]

@[expose] def alpha : F8 := ⟨1, 1, 0⟩

@[expose] def bMat : Matrix (Fin 4) (Fin 4) F8 := rootMat alpha 0

@[expose] def bInvMat : Matrix (Fin 4) (Fin 4) F8 := rootMat alpha ⟨0, 1, 0⟩

theorem weylMat_mul_self : (weylMat : Matrix (Fin 4) (Fin 4) F8) * weylMat = 1 := by
  decide +kernel

theorem bMat_mul_bInvMat : bMat * bInvMat = 1 := by decide +kernel

theorem bInvMat_mul_bMat : bInvMat * bMat = 1 := by decide +kernel

@[expose] def genGL : Fin 2 → GL (Fin 4) F8 :=
  ![⟨weylMat, weylMat, weylMat_mul_self, weylMat_mul_self⟩,
    ⟨bMat, bInvMat, bMat_mul_bInvMat, bInvMat_mul_bMat⟩]

@[expose] def letterMat : Fin 2 × Bool → Matrix (Fin 4) (Fin 4) F8
  | (0, _) => weylMat
  | (1, true) => bMat
  | (1, false) => bInvMat

@[expose] def toMat (A : Array F8) : Matrix (Fin 4) (Fin 4) F8 :=
  Matrix.of fun i j => A[4 * i.val + j.val]!

@[expose] def ofMat (M : Matrix (Fin 4) (Fin 4) F8) : Array F8 :=
  #[M 0 0, M 0 1, M 0 2, M 0 3,
    M 1 0, M 1 1, M 1 2, M 1 3,
    M 2 0, M 2 1, M 2 2, M 2 3,
    M 3 0, M 3 1, M 3 2, M 3 3]

@[expose] def mulArr (A B : Array F8) : Array F8 :=
  let e := fun i j : ℕ => A[4 * i]! * B[j]! + A[4 * i + 1]! * B[4 + j]! +
    A[4 * i + 2]! * B[8 + j]! + A[4 * i + 3]! * B[12 + j]!
  #[e 0 0, e 0 1, e 0 2, e 0 3,
    e 1 0, e 1 1, e 1 2, e 1 3,
    e 2 0, e 2 1, e 2 2, e 2 3,
    e 3 0, e 3 1, e 3 2, e 3 3]

theorem toMat_ofMat (M : Matrix (Fin 4) (Fin 4) F8) : toMat (ofMat M) = M :=
  Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem toMat_mulArr (A B : Array F8) : toMat (mulArr A B) = toMat A * toMat B :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> (simp only [Matrix.mul_apply, Fin.sum_univ_four]; rfl)

@[expose] def wordArr (w : List (Fin 2 × Bool)) : Array F8 :=
  w.foldr (fun l A => mulArr (ofMat (letterMat l)) A) (ofMat 1)

@[expose] def wordMat (w : List (Fin 2 × Bool)) : Matrix (Fin 4) (Fin 4) F8 := toMat (wordArr w)

private theorem val_letter (l : Fin 2 × Bool) :
    ((cond l.2 (genGL l.1) (genGL l.1)⁻¹ : GL (Fin 4) F8) : Matrix (Fin 4) (Fin 4) F8) =
      letterMat l := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s <;> rfl

theorem val_lift_genGL (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift genGL (FreeGroup.mk w) : GL (Fin 4) F8) : Matrix (Fin 4) (Fin 4) F8) =
      wordMat w := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => exact (toMat_ofMat 1).symm
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, val_letter]
    change _ = toMat (mulArr (ofMat (letterMat l)) (wordArr w))
    rw [toMat_mulArr, toMat_ofMat]
    rfl

noncomputable abbrev toGL : GL (Fin 4) F8 →* GL (Fin 4) GF :=
  Matrix.GeneralLinearGroup.map F8.toGaloisField

theorem toGL_injective : Function.Injective toGL := by
  intro x y h
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact F8.toGaloisField_injective (by
    simpa using congrArg (fun g : GL (Fin 4) GF => (g : Matrix (Fin 4) (Fin 4) GF) i j) h)

theorem val_toGL (x : GL (Fin 4) F8) :
    ((toGL x : GL (Fin 4) GF) : Matrix (Fin 4) (Fin 4) GF) =
      (x : Matrix (Fin 4) (Fin 4) F8).map F8.toGaloisField :=
  rfl

theorem toGL_genGL_zero : toGL (genGL 0) = Suzuki.weyl 1 := by
  ext1
  rw [val_toGL, Suzuki.coe_weyl, ← weylMat_eq_weylMatrix]
  exact map_weylMat _

theorem toGL_genGL_one :
    toGL (genGL 1) = Suzuki.unipotent 1 (F8.toGaloisField alpha) (F8.toGaloisField 0) := by
  ext1
  rw [val_toGL, Suzuki.coe_unipotent, ← rootMat_eq_unipotentMatrix]
  exact map_rootMat _ _ _

theorem toGL_genGL_mem (i : Fin 2) : toGL (genGL i) ∈ suzukiGroup 1 := by
  fin_cases i
  · exact toGL_genGL_zero ▸ Suzuki.weyl_mem_suzukiGroup
  · exact toGL_genGL_one ▸ Suzuki.unipotent_mem_suzukiGroup _ _

noncomputable def genSz (i : Fin 2) : suzukiGroup 1 := ⟨toGL (genGL i), toGL_genGL_mem i⟩

theorem val_lift_genSz (x : FreeGroup (Fin 2)) :
    ((FreeGroup.lift genSz x : suzukiGroup 1) : GL (Fin 4) GF) = toGL (FreeGroup.lift genGL x) := by
  have h : (suzukiGroup 1).subtype.comp (FreeGroup.lift genSz) = toGL.comp (FreeGroup.lift genGL) :=
    FreeGroup.ext_hom _ _ fun i => by simp [genSz]
  exact DFunLike.congr_fun h x

theorem lift_genSz_eq_one {w : List (Fin 2 × Bool)} (h : wordMat w = 1) :
    FreeGroup.lift genSz (FreeGroup.mk w) = 1 := by
  apply Subtype.ext
  rw [val_lift_genSz, OneMemClass.coe_one]
  have : FreeGroup.lift genGL (FreeGroup.mk w) = 1 := Units.ext (by rw [val_lift_genGL, h]; rfl)
  rw [this, map_one]

theorem closure_range_genSz {word : F8 → F8 → List (Fin 2 × Bool)}
    (h : ∀ c d, rootMat c d = wordMat (word c d)) : Subgroup.closure (Set.range genSz) = ⊤ := by
  have hmem : ∀ x : FreeGroup (Fin 2), toGL (FreeGroup.lift genGL x) ∈
      Subgroup.closure (Set.range fun i => toGL (genGL i)) := fun x => by
    have hc : toGL.comp (FreeGroup.lift genGL) = FreeGroup.lift fun i => toGL (genGL i) :=
      FreeGroup.ext_hom _ _ fun i => by simp
    rw [← MonoidHom.comp_apply, hc, ← FreeGroup.range_lift_eq_closure]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hle : suzukiGroup 1 ≤ Subgroup.closure (Set.range fun i => toGL (genGL i)) := by
    refine Suzuki.suzukiGroup_le_iff.mpr ⟨fun a b => ?_, ?_⟩
    · obtain ⟨c, rfl⟩ := F8.toGaloisField_surjective a
      obtain ⟨d, rfl⟩ := F8.toGaloisField_surjective b
      have e : Suzuki.unipotent 1 (F8.toGaloisField c) (F8.toGaloisField d) =
          toGL (FreeGroup.lift genGL (FreeGroup.mk (word c d))) := by
        ext1
        rw [val_toGL, val_lift_genGL, ← h, map_rootMat, Suzuki.coe_unipotent,
          rootMat_eq_unipotentMatrix]
      rw [e]
      exact hmem _
    · rw [← toGL_genGL_zero]
      exact Subgroup.subset_closure ⟨0, rfl⟩
  rw [eq_top_iff]
  rintro x -
  have hx := hle x.2
  have hmap : (Subgroup.closure (Set.range genSz)).map (suzukiGroup 1).subtype =
      Subgroup.closure (Set.range fun i => toGL (genGL i)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← hmap] at hx
  exact (Subgroup.mem_map_iff_mem (suzukiGroup 1).subtype_injective).mp hx

theorem card_suzukiGroup : Nat.card (suzukiGroup 1) = 29120 := by
  have hK : Nat.card GF = 2 ^ (2 * 1 + 1) := GaloisField.card 2 (2 * 1 + 1) (by omega)
  rw [Nat.card_congr (BenderSuzuki.Catalog.suzukiGroupEquiv 1).toEquiv,
    ← Nat.card_congr (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
      hK).toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  norm_num

theorem nonempty_mulEquiv_suzukiGroup {X : Type} [Group X]
    (h : CFSG.Models.LieModel X .twistedB2 0 2 3) : Nonempty (X ≃* suzukiGroup 1) := by
  obtain ⟨-, hc | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := h
  · exact hc.2.elim
  cases d <;> simp only [CFSG.Models.NamesTag] at hd
  obtain ⟨-, hm⟩ := hd
  rename_i m
  obtain rfl : m = 1 := by omega
  exact ⟨(e.trans (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
    (BenderSuzuki.Catalog.suzukiGroupEquiv 1).symm⟩

theorem nonempty_mulEquiv_suzukiGroup_of_blueprint {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 3) : Nonempty (X ≃* suzukiGroup 1) := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact absurd hrt (by decide)
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hsz
  obtain rfl : a = 1 := by omega
  exact ⟨(e.trans (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (BenderSuzuki.Catalog.suzukiGroupEquiv 1).symm⟩

end CFSG.LieType.Multipliers.Sz8
