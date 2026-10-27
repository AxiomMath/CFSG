module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Eig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix CFSG.Open

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem mem_SU_iff (hF : Nat.card F = (2 ^ 2) ^ 2) (A : GL (Fin 6) F) :
    A ∈ StatedSU 6 (2 ^ 2) F ↔ (A : Matrix (Fin 6) (Fin 6) F).det = 1 ∧
      (((A : Matrix (Fin 6) (Fin 6) F)).map (iterateFrobenius F 2 2 : F →+* F))ᵀ *
        (A : Matrix (Fin 6) (Fin 6) F) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 6) (by norm_num)).1
  exact Set.ext_iff.1 h A

@[expose] def blkU (d : Fin 6 → F) (l : F) (g : GL (Fin 6) F) : GL (Fin 6) F :=
  if hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g then
    Units.mk (blkM d l g) (blkM d l ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))
      (by rw [← blkM_mul d l hg (inv_comm_of g hg), Units.mul_inv, blkM_one])
      (by rw [← blkM_mul d l (inv_comm_of g hg) hg, Units.inv_mul, blkM_one])
  else 1

theorem blkU_val {d : Fin 6 → F} {l : F} {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g) :
    ((blkU d l g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = blkM d l g := by
  unfold blkU
  rw [dif_pos hg]

theorem commute_mul_of {d : Fin 6 → F} {l : F} {g k : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g)
    (hk : (k : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * k) :
    ((g * k : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l =
      eigP d l * ((g * k : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  rw [Units.val_mul, mul_assoc, hk, ← mul_assoc, hg, mul_assoc]

theorem blkU_mul {d : Fin 6 → F} {l : F} {g k : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g)
    (hk : (k : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * k) :
    blkU d l (g * k) = blkU d l g * blkU d l k := by
  apply Units.ext
  rw [blkU_val (commute_mul_of hg hk), Units.val_mul, Units.val_mul, blkU_val hg, blkU_val hk]
  exact blkM_mul d l hg hk

theorem blkU_one (d : Fin 6 → F) (l : F) : blkU d l 1 = 1 := by
  have h1 : ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l =
      eigP d l * ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [Units.val_one, one_mul, mul_one]
  apply Units.ext
  rw [blkU_val h1, Units.val_one]
  exact blkM_one d l

theorem blkU_inv {d : Fin 6 → F} {l : F} {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g) :
    blkU d l g⁻¹ = (blkU d l g)⁻¹ := by
  have hgi := inv_comm_of g hg
  have h := blkU_mul hg (show ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l =
      eigP d l * ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) from hgi)
  rw [mul_inv_cancel, blkU_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem blkU_mem_SU {d : Fin 6 → F} {l : F} (hF : Nat.card F = (2 ^ 2) ^ 2) {g : GL (Fin 6) F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * g)
    (hgSU : g ∈ StatedSU 6 (2 ^ 2) F)
    (hdet : (blkU d l g : GL (Fin 6) F).val.det = 1) :
    blkU d l g ∈ StatedSU 6 (2 ^ 2) F := by
  rw [mem_SU_iff hF]
  refine ⟨hdet, ?_⟩
  rw [blkU_val hg]
  exact blkM_unitary d l (hx := hg) ((mem_SU_iff hF g).1 hgSU).2

@[expose] def Cg (d : Fin 6 → F) : Subgroup ↥(StatedSU 6 (2 ^ 2) F) where
  carrier := {x | ∀ l : F, (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * x.1}
  mul_mem' := fun {a b} ha hb l => by
    show ((a.1 * b.1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l =
      eigP d l * ((a.1 * b.1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    rw [Units.val_mul, mul_assoc, hb l, ← mul_assoc, ha l, mul_assoc]
  one_mem' := fun l => by
    show ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d l =
      eigP d l * ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    rw [Units.val_one, one_mul, mul_one]
  inv_mem' := fun {a} ha l => inv_comm_of a.1 (ha l)

@[expose] def Ng (d : Fin 6 → F) : Subgroup ↥(StatedSU 6 (2 ^ 2) F) where
  carrier := {x | (∀ l : F, (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * x.1) ∧
    ∀ l : F, Matrix.GeneralLinearGroup.det (blkU d l x.1) = 1}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨(Cg d).mul_mem (show a ∈ Cg d from ha.1) (show b ∈ Cg d from hb.1), fun l => ?_⟩
    show Matrix.GeneralLinearGroup.det (blkU d l (a.1 * b.1)) = 1
    rw [blkU_mul (ha.1 l) (hb.1 l), map_mul, ha.2 l, hb.2 l, one_mul]
  one_mem' := ⟨fun l => by simp, fun l => by
    show Matrix.GeneralLinearGroup.det (blkU d l 1) = 1
    rw [blkU_one, map_one]⟩
  inv_mem' := fun {a} ha => ⟨(Cg d).inv_mem (show a ∈ Cg d from ha.1), fun l => by
    show Matrix.GeneralLinearGroup.det (blkU d l a.1⁻¹) = 1
    rw [blkU_inv (ha.1 l), map_inv, ha.2 l, inv_one]⟩

@[expose] def Ug (d : Fin 6 → F) (l : F) : Subgroup ↥(StatedSU 6 (2 ^ 2) F) where
  carrier := {x | (∀ m : F, (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d m = eigP d m * x.1) ∧
    (x.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) = 1 - eigP d l}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨fun m => ?_, ?_⟩
    · show ((a.1 * b.1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d m =
        eigP d m * ((a.1 * b.1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
      rw [Units.val_mul, mul_assoc, hb.1 m, ← mul_assoc, ha.1 m, mul_assoc]
    · show ((a.1 * b.1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) =
        1 - eigP d l
      rw [Units.val_mul, mul_assoc, hb.2, ha.2]
  one_mem' := ⟨fun m => by simp, by simp⟩
  inv_mem' := fun {a} ha => ⟨fun m => inv_comm_of a.1 (ha.1 m), by
    show ((a.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) = 1 - eigP d l
    calc ((a.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l)
        = ((a.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
            ((a.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l)) := by rw [ha.2]
      _ = 1 - eigP d l := Units.inv_mul_cancel_left _ _⟩

theorem Ng_det {d : Fin 6 → F} {x : ↥(StatedSU 6 (2 ^ 2) F)} (hx : x ∈ Ng d) (l : F) :
    (blkU d l x.1 : GL (Fin 6) F).val.det = 1 := by
  have h := congrArg Units.val (hx.2 l)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
  exact h

open Classical in
@[expose] noncomputable def psiG (d : Fin 6 → F) (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F)
    (x : ↥(StatedSU 6 (2 ^ 2) F)) : ↥(StatedSU 6 (2 ^ 2) F) :=
  if hx : x ∈ Ng d then ⟨blkU d l x.1, blkU_mem_SU hF (hx.1 l) x.2 (Ng_det hx l)⟩ else 1

theorem psiG_val {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F)
    {x : ↥(StatedSU 6 (2 ^ 2) F)} (hx : x ∈ Ng d) :
    (psiG d hF l x).1 = blkU d l x.1 := by
  unfold psiG
  rw [dif_pos hx]

theorem blkU_eq_self {d : Fin 6 → F} {l : F} {g : GL (Fin 6) F}
    (hc : ∀ m : F, (g : Matrix (Fin 6) (Fin 6) F) * eigP d m = eigP d m * g)
    (hq : (g : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) = 1 - eigP d l) :
    blkU d l g = g := by
  apply Units.ext
  rw [blkU_val (hc l)]
  exact blkM_eq_self d l (hc l) hq

theorem Ug_le_Ng {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F) : Ug d l ≤ Ng d := by
  intro x hx
  refine ⟨hx.1, fun m => ?_⟩
  by_cases hml : m = l
  · rw [hml]
    rw [blkU_eq_self hx.1 hx.2]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact ((mem_SU_iff hF x.1).1 x.2).1
  · have h1 : blkU d m x.1 = 1 := by
      apply Units.ext
      rw [blkU_val (hx.1 m), Units.val_one]
      exact blkM_eq_one d hml (hx.1 m) hx.2
    rw [h1, map_one]

theorem psiG_mem {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F)
    {x : ↥(StatedSU 6 (2 ^ 2) F)} (hx : x ∈ Ng d) : psiG d hF l x ∈ Ug d l := by
  have hv := psiG_val hF l hx
  refine ⟨fun m => ?_, ?_⟩
  · show ((psiG d hF l x).1 : Matrix (Fin 6) (Fin 6) F) * eigP d m =
      eigP d m * ((psiG d hF l x).1 : Matrix (Fin 6) (Fin 6) F)
    rw [hv, blkU_val (hx.1 l)]
    exact blkM_comm_eigP d l (fun m' => hx.1 m') m
  · show ((psiG d hF l x).1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) = 1 - eigP d l
    rw [hv, blkU_val (hx.1 l)]
    exact blkM_mul_one_sub d l _

theorem psiG_mul {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F)
    {x y : ↥(StatedSU 6 (2 ^ 2) F)} (hx : x ∈ Ng d) (hy : y ∈ Ng d) :
    psiG d hF l (x * y) = psiG d hF l x * psiG d hF l y := by
  have hxy : x * y ∈ Ng d := (Ng d).mul_mem hx hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, psiG_val hF l hxy, psiG_val hF l hx, psiG_val hF l hy]
  show blkU d l (x.1 * y.1) = blkU d l x.1 * blkU d l y.1
  exact blkU_mul (hx.1 l) (hy.1 l)

theorem psiG_id {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) (l : F)
    {u : ↥(StatedSU 6 (2 ^ 2) F)} (hu : u ∈ Ug d l) : psiG d hF l u = u := by
  have hN : u ∈ Ng d := Ug_le_Ng hF l hu
  apply Subtype.ext
  rw [psiG_val hF l hN]
  exact blkU_eq_self hu.1 hu.2

theorem psiG_zero {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2) {l m : F} (hlm : l ≠ m)
    {u : ↥(StatedSU 6 (2 ^ 2) F)} (hu : u ∈ Ug d m) : psiG d hF l u = 1 := by
  have hN : u ∈ Ng d := Ug_le_Ng hF m hu
  apply Subtype.ext
  rw [psiG_val hF l hN]
  show blkU d l u.1 = 1
  apply Units.ext
  rw [blkU_val (hu.1 l), Units.val_one]
  exact blkM_eq_one d hlm (hu.1 l) hu.2

theorem Ng_eq_one_of_psi {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2)
    {x : ↥(StatedSU 6 (2 ^ 2) F)} (hx : x ∈ Ng d) (h : ∀ l, psiG d hF l x = 1) : x = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (x.1 : Matrix (Fin 6) (Fin 6) F) = 1
  apply eq_one_of_eigP_fix d
  intro k
  have hk : blkU d (d k) x.1 = 1 := by
    have h1 := congrArg Subtype.val (h (d k))
    rw [psiG_val hF (d k) hx] at h1
    exact h1
  have hk2 : blkM d (d k) (x.1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [← blkU_val (hx.1 (d k)), hk, Units.val_one]
  rw [blkM_of_comm d (d k) (hx.1 (d k))] at hk2
  have hxP : (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d (d k) = 1 - (1 - eigP d (d k)) :=
    eq_sub_of_add_eq hk2
  rw [sub_sub_cancel] at hxP
  exact hxP

theorem Ug_conj {d : Fin 6 → F} (l : F) {c : ↥(StatedSU 6 (2 ^ 2) F)} (hc : c ∈ Cg d)
    {u : ↥(StatedSU 6 (2 ^ 2) F)} (hu : u ∈ Ug d l) : c * u * c⁻¹ ∈ Ug d l := by
  have hc' : ∀ m : F, (c.1 : Matrix (Fin 6) (Fin 6) F) * eigP d m = eigP d m * c.1 := hc
  have hu' := hu
  refine ⟨fun m => ?_, ?_⟩
  · show ((c.1 * u.1 * c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * eigP d m =
      eigP d m * ((c.1 * u.1 * c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    rw [Units.val_mul, Units.val_mul]
    calc (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          eigP d m
        = (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * (((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          eigP d m) := by simp only [mul_assoc]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * (eigP d m *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := by
            rw [inv_comm_of c.1 (hc' m)]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * (u.1 * eigP d m) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by simp only [mul_assoc]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * (eigP d m * u.1) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by rw [hu'.1 m]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * eigP d m * u.1 *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by simp only [mul_assoc]
      _ = eigP d m * (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by rw [hc' m]
      _ = eigP d m * ((c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := by simp only [mul_assoc]
  · show ((c.1 * u.1 * c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) =
      1 - eigP d l
    have hcQ : (c.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) =
        (1 - eigP d l) * (c.1 : Matrix (Fin 6) (Fin 6) F) := by
      rw [mul_sub, sub_mul, mul_one, one_mul, hc' l]
    have hcQi := inv_comm_of c.1 hcQ
    rw [Units.val_mul, Units.val_mul]
    calc (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          (1 - eigP d l)
        = (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * (((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          (1 - eigP d l)) := by simp only [mul_assoc]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * u.1 * ((1 - eigP d l) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := by rw [hcQi]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * (u.1 * (1 - eigP d l)) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by simp only [mul_assoc]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by rw [hu'.2]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * ((1 - eigP d l) *
          ((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) := by simp only [mul_assoc]
      _ = (c.1 : Matrix (Fin 6) (Fin 6) F) * (((c.1⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          (1 - eigP d l)) := by rw [← hcQi]
      _ = (1 - eigP d l) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]

theorem J_le_Ng {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2)
    {J : Subgroup ↥(StatedSU 6 (2 ^ 2) F)} (hJq : CFSG.Open.IsQuasisimple J) (hJC : J ≤ Cg d) :
    J ≤ Ng d := by
  intro j hj
  refine ⟨hJC hj, fun l => ?_⟩
  have key := eq_one_of_commutator_eq_top (K := ↥J) hJq.1
    (fun y : ↥J => Matrix.GeneralLinearGroup.det (blkU d l (y : ↥(StatedSU 6 (2 ^ 2) F)).1))
    (fun x y => by
      show Matrix.GeneralLinearGroup.det (blkU d l ((x * y : ↥J) : ↥(StatedSU 6 (2 ^ 2) F)).1) =
        Matrix.GeneralLinearGroup.det (blkU d l (x : ↥(StatedSU 6 (2 ^ 2) F)).1) *
          Matrix.GeneralLinearGroup.det (blkU d l (y : ↥(StatedSU 6 (2 ^ 2) F)).1)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, blkU_mul ((hJC x.2) l) ((hJC y.2) l), map_mul])
    (fun x y => mul_comm _ _) ⟨j, hj⟩
  exact key

theorem exists_block {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2)
    {J : Subgroup ↥(StatedSU 6 (2 ^ 2) F)} (hJq : CFSG.Open.IsQuasisimple J) (hJC : J ≤ Cg d)
    (hnorm : ∀ c ∈ Cg d, ∀ j ∈ J, c * j * c⁻¹ ∈ J) :
    ∃ l0 : F, J ≤ Ug d l0 :=
  block_mem_of_block (C := Cg d) (N := Ng d) (U := Ug d) (ψ := psiG d hF) hJq
    (J_le_Ng hF hJq hJC) (fun x hx => hx.1) hnorm
    (fun l => Ug_le_Ng hF l)
    (fun l c hc u hu => Ug_conj l hc hu)
    (fun l x hx y hy => psiG_mul hF l hx hy)
    (fun l x hx => psiG_mem hF l hx)
    (fun l u hu => psiG_id hF l hu)
    (fun l m hlm u hu => psiG_zero hF hlm hu)
    (fun x hx h => Ng_eq_one_of_psi hF hx h)

theorem commute_diag_iff (d : Fin 6 → F) (X : Matrix (Fin 6) (Fin 6) F) :
    Matrix.diagonal d * X = X * Matrix.diagonal d ↔ ∀ l : F, X * eigP d l = eigP d l * X := by
  constructor
  · intro h l
    ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, eigP, Matrix.diagonal_mul,
      Matrix.mul_diagonal] at h1 ⊢
    by_cases hX : X i j = 0
    · simp [hX]
    · have hdij : d i = d j := by
        have : (d i - d j) * X i j = 0 := by linear_combination h1
        rcases mul_eq_zero.1 this with h2 | h2
        · exact sub_eq_zero.1 h2
        · exact absurd h2 hX
      simp [hdij]
  · intro h
    ext i j
    have h1 := congrFun (congrFun (h (d j)) i) j
    simp only [eigP, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1 ⊢
    by_cases hX : X i j = 0
    · simp [hX]
    · have hdij : d i = d j := by
        by_contra hne
        simp [hne] at h1
        exact hX h1
      simp [hdij, mul_comm]

theorem centralizer_eq_Cg {g : ↥(StatedSU 6 (2 ^ 2) F)} {d : Fin 6 → F}
    (hg : (g : GL (Fin 6) F).val = Matrix.diagonal d) :
    Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)) = Cg d := by
  ext x
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hgx : g * x = x * g := h g (Set.mem_singleton g)
    show ∀ l : F, (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * x.1
    rw [← commute_diag_iff]
    have h2 : (g * x).1 = (x * g).1 := congrArg Subtype.val hgx
    have h3 := congrArg Units.val h2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg] at h3
    exact h3
  · intro h k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have h' : ∀ l : F, (x.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l = eigP d l * x.1 := h
    rw [← commute_diag_iff] at h'
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hg]
    exact h'

end CFSG.LocalAnalysis.GLTheoremA.SFM12


