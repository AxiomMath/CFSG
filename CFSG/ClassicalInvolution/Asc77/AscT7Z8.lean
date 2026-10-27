module

public import CFSG.ClassicalInvolution.Asc77.AscT7L21

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (r0 coe_r0)
open scoped Matrix MatrixGroups

namespace T7Z

variable {F : Type} [Field F]

@[expose] def Di (i : F) (hi : i * i = -1) : SL(2, F) :=
  ⟨!![i, 0; 0, -i], by simp [Matrix.det_fin_two, hi]⟩

theorem coe_Di (i : F) (hi : i * i = -1) :
    ((Di i hi : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![i, 0; 0, -i] := rfl

theorem exists_conj_r0_Di (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    ∃ A : SL(2, F), A * r0 * A⁻¹ = Di i hi := by
  have h2' : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  let A : SL(2, F) := ⟨!![(2 : F)⁻¹, -(i * (2 : F)⁻¹); -i, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-(2 : F)⁻¹) * hi + h2'⟩
  refine ⟨A, ?_⟩
  have hA : A * r0 = Di i hi * A := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_r0, coe_Di]
    show (!![(2 : F)⁻¹, -(i * (2 : F)⁻¹); -i, 1] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] =
      !![i, 0; 0, -i] * !![(2 : F)⁻¹, -(i * (2 : F)⁻¹); -i, 1]
    simp only [Matrix.mul_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
    · linear_combination (2 : F)⁻¹ * hi
    · linear_combination -hi
  calc A * r0 * A⁻¹ = (Di i hi * A) * A⁻¹ := by rw [hA]
    _ = Di i hi := by group


theorem blk_Di_comm_short (i : F) (hi : i * i = -1) (A' : SL(2, F)) :
    shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) A' * blk F (Di i hi) (Di i hi) =
      blk F (Di i hi) (Di i hi) * shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) A' := by
  apply mat_injective
  rw [map_mul, map_mul, mat_shortBlock, mat_blk]
  have h1 : (Matrix.diagonal ![(Di i hi : Matrix (Fin 2) (Fin 2) F) 0 0,
      (Di i hi : Matrix (Fin 2) (Fin 2) F) 0 0] : Matrix (Fin 2) (Fin 2) F) =
      i • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.smul_one_eq_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_Di]
  have h2 : (Matrix.diagonal ![(Di i hi : Matrix (Fin 2) (Fin 2) F) 1 1,
      (Di i hi : Matrix (Fin 2) (Fin 2) F) 1 1] : Matrix (Fin 2) (Fin 2) F) =
      (-i) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.smul_one_eq_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_Di]
  have h3 : (Matrix.diagonal ![(Di i hi : Matrix (Fin 2) (Fin 2) F) 0 1,
      (Di i hi : Matrix (Fin 2) (Fin 2) F) 0 1] : Matrix (Fin 2) (Fin 2) F) = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_Di]
  have h4 : (Matrix.diagonal ![(Di i hi : Matrix (Fin 2) (Fin 2) F) 1 0,
      (Di i hi : Matrix (Fin 2) (Fin 2) F) 1 0] : Matrix (Fin 2) (Fin 2) F) = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_Di]
  rw [h1, h2, h3, h4]
  simp [Matrix.fromBlocks_multiply]


theorem R0'_map_conj_blk (A B : SL(2, F)) :
    (R0' F).map (MulAut.conj (blk F A B)).toMonoidHom = R0' F := by
  have key : ∀ (A B : SL(2, F)) (x : StatedSp 2 F), x ∈ R0' F →
      blk F A B * x * (blk F A B)⁻¹ ∈ R0' F := by
    intro A B x hx
    obtain ⟨y, rfl⟩ := hx
    have h : blk F A B * longBlock F 2 1 y * (blk F A B)⁻¹ = longBlock F 2 1 (B * y * B⁻¹) := by
      unfold blk
      have hc : longBlock F 2 0 A * longBlock F 2 1 B * longBlock F 2 1 y *
          (longBlock F 2 0 A * longBlock F 2 1 B)⁻¹ =
          longBlock F 2 0 A * (longBlock F 2 1 (B * y * B⁻¹)) * (longBlock F 2 0 A)⁻¹ := by
        simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
      rw [hc]
      calc longBlock F 2 0 A * longBlock F 2 1 (B * y * B⁻¹) * (longBlock F 2 0 A)⁻¹
          = longBlock F 2 1 (B * y * B⁻¹) * longBlock F 2 0 A * (longBlock F 2 0 A)⁻¹ := by
            rw [longBlock_comm A (B * y * B⁻¹)]
        _ = longBlock F 2 1 (B * y * B⁻¹) := by group
    rw [h]
    exact ⟨_, rfl⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key A B y hy
  · intro hx
    refine ⟨(blk F A B)⁻¹ * x * ((blk F A B)⁻¹)⁻¹, ?_, ?_⟩
    · have := key A⁻¹ B⁻¹ x hx
      rwa [← blk_inv] at this
    · show blk F A B * ((blk F A B)⁻¹ * x * ((blk F A B)⁻¹)⁻¹) * (blk F A B)⁻¹ = x
      group


theorem sp4_adapted_core (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {c e : StatedSp 2 F}
    {Rp : Subgroup (StatedSp 2 F)} (hRp : Rp = (R0' F).map (MulAut.conj c).toMonoidHom)
    (he : e = c * u0 F * c⁻¹) :
    ∃ c' : StatedSp 2 F, Rp = (longBlock F 2 1).range.map (MulAut.conj c'⁻¹).toMonoidHom ∧
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (MulAut.conj c'⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({e} : Set (StatedSp 2 F)) := by
  obtain ⟨A, hA⟩ := exists_conj_r0_Di h2 hi
  refine ⟨blk F A A * c⁻¹, ?_, ?_⟩
  · have hmap : (longBlock F 2 1).range.map (MulAut.conj (blk F A A * c⁻¹)⁻¹).toMonoidHom =
        (R0' F).map (MulAut.conj c).toMonoidHom := by
      have h1 : (blk F A A * c⁻¹)⁻¹ = c * (blk F A A)⁻¹ := by group
      rw [h1]
      have h2' : (MulAut.conj (c * (blk F A A)⁻¹)).toMonoidHom =
          (MulAut.conj c).toMonoidHom.comp (MulAut.conj (blk F A A)⁻¹).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [h2', ← Subgroup.map_map]
      show ((R0' F).map (MulAut.conj (blk F A A)⁻¹).toMonoidHom).map _ = _
      rw [blk_inv, R0'_map_conj_blk]
    rw [hRp, hmap]
  · rintro _ ⟨_, ⟨A', rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set d : StatedSp 2 F := blk F A A with hd
    set s : StatedSp 2 F := shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) A' with hs
    set u' : StatedSp 2 F := blk F (Di i hi) (Di i hi) with hu'
    have hdu : d * u0 F * d⁻¹ = u' := by
      rw [hd, hu', u0_eq_blk, blk_inv, blk_mul, blk_mul, ← hA]
    have h1 : d * u0 F = u' * d := by rw [← hdu]; group
    have h2 : d⁻¹ * u' = u0 F * d⁻¹ := by rw [← hdu]; group
    have hcs : s * u' = u' * s := blk_Di_comm_short i hi A'
    have hy : (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom s = c * d⁻¹ * s * d * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hy, he]
    calc c * d⁻¹ * s * d * c⁻¹ * (c * u0 F * c⁻¹)
        = c * d⁻¹ * s * (d * u0 F) * c⁻¹ := by group
      _ = c * d⁻¹ * s * (u' * d) * c⁻¹ := by rw [h1]
      _ = c * d⁻¹ * (s * u') * d * c⁻¹ := by group
      _ = c * d⁻¹ * (u' * s) * d * c⁻¹ := by rw [hcs]
      _ = c * (d⁻¹ * u') * s * d * c⁻¹ := by group
      _ = c * (u0 F * d⁻¹) * s * d * c⁻¹ := by rw [h2]
      _ = c * u0 F * c⁻¹ * (c * d⁻¹ * s * d * c⁻¹) := by group



theorem twin_plane1_eq (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    {g c x x' : StatedSp 2 F} (hRg : R = (R0 F).map (MulAut.conj g).toMonoidHom)
    (hR'g : R' = (R0' F).map (MulAut.conj g).toMonoidHom) (hxR : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hxc : x = c * x0 F * c⁻¹) : R' = (R0' F).map (MulAut.conj c).toMonoidHom := by
  have hxg : x = g * x0 F * g⁻¹ := T7L.eq_conj_longInv h2 (k := 0) (hRg ▸ hxR) hx2 hx1
  have hx'g : x' = g * longInv F 2 1 * g⁻¹ :=
    T7L.eq_conj_longInv h2 (k := 1) (hR'g ▸ hx'R') hx'2 hx'1
  have hz : ∀ y : StatedSp 2 F, y * zneg F = zneg F * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  have hx' : x' = zneg F * x := by
    rw [hx'g, ← zneg_mul_x0_eq_longInv, hxg]
    calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F) * x0 F * g⁻¹ := by group
      _ = (zneg F * g) * x0 F * g⁻¹ := by rw [hz g]
      _ = zneg F * (g * x0 F * g⁻¹) := by group
  have hinv : c * longInv F 2 1 * c⁻¹ = x' := by
    rw [hx', ← zneg_mul_x0_eq_longInv, hxc]
    calc c * (zneg F * x0 F) * c⁻¹ = (c * zneg F) * x0 F * c⁻¹ := by group
      _ = (zneg F * c) * x0 F * c⁻¹ := by rw [hz c]
      _ = zneg F * (c * x0 F * c⁻¹) := by group
  have hIs : IsLongRootSp2 R' x' := ⟨1, g, hR'g, hx'g⟩
  have hIs' : IsLongRootSp2 ((R0' F).map (MulAut.conj c).toMonoidHom) x' :=
    hinv ▸ (isLongRootSp2_standard (K := F) (n := 2) 1).conj c
  rw [hIs.eq_longRootGroup h2, hIs'.eq_longRootGroup h2]

variable [Finite F]

theorem sp4_adapted (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    {a b : StatedSp 2 F} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x')
    (hab : a * b = b * a) :
    ∃ (c : StatedSp 2 F) (Rp : Subgroup (StatedSp 2 F)), (Rp = R ∨ Rp = R') ∧
      Rp = (longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom ∧
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
        (MulAut.conj c⁻¹).toMonoidHom ≤ Subgroup.centralizer ({a * b} : Set (StatedSp 2 F)) := by
  obtain ⟨g, k, hRg, hR'g⟩ := ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hR hR' hne hxR hx2 hx1
    hx'R' hx'2 hx'1 hc
  fin_cases k
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 ha haa
      hb hbb
    have hp := twin_plane1_eq h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 hxc
    obtain ⟨c', h1, h2'⟩ := sp4_adapted_core h2 hi hp habc
    exact ⟨c', R', Or.inr rfl, h1, h2'⟩
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hb hbb
      ha haa
    have hp := twin_plane1_eq h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hxc
    obtain ⟨c', h1, h2'⟩ := sp4_adapted_core h2 hi hp (hab ▸ habc)
    exact ⟨c', R, Or.inl rfl, h1, h2'⟩

end T7Z

end CFSG.ClassicalInvolution.Asc77
