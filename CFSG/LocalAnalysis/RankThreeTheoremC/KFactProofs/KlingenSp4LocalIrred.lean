module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalLevi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.AGLEmbedding.KlingenSpFour

section Siegel

variable (p : ℕ) [Fact p.Prime] {W : Subgroup (PSp4 p)} {a b c a' b' c' : ZMod p}

theorem irr_mem_congr (h : (xS p).x a b c ∈ W) (ha : a = a') (hb : b = b') (hc : c = c') :
    (xS p).x a' b' c' ∈ W := by
  subst ha hb hc
  exact h

theorem irr_mem_sub (h : (xS p).x a b c ∈ W) (h' : (xS p).x a' b' c' ∈ W) :
    (xS p).x (a - a') (b - b') (c - c') ∈ W := by
  have := W.mul_mem h (W.inv_mem h')
  rw [XData.x_inv, XData.x_mul] at this
  exact irr_mem_congr p this (sub_eq_add_neg _ _).symm (sub_eq_add_neg _ _).symm
    (sub_eq_add_neg _ _).symm

theorem irr_mem_smul (t : ZMod p) (h : (xS p).x a b c ∈ W) :
    (xS p).x (t * a) (t * b) (t * c) ∈ W := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective t
  rw [← XData.x_pow]
  exact W.pow_mem h n

theorem irr_mem_gA
    (hN : Subgroup.normalizer ((xS p).U : Set (PSp4 p)) ≤ Subgroup.normalizer (W : Set (PSp4 p)))
    (s : ZMod p) (h : (xS p).x a b c ∈ W) :
    (xS p).x (a + 2 * s * b + s ^ 2 * c) (b + s * c) c ∈ W := by
  rw [← levG_conj_xS_gA]
  exact (Subgroup.mem_normalizer_iff.mp (hN (levG_mem_normalizer p (gA s))) _).mp h

theorem irr_mem_gL
    (hN : Subgroup.normalizer ((xS p).U : Set (PSp4 p)) ≤ Subgroup.normalizer (W : Set (PSp4 p)))
    (s : ZMod p) (h : (xS p).x a b c ∈ W) :
    (xS p).x a (b + s * a) (c + 2 * s * b + s ^ 2 * a) ∈ W := by
  rw [← levG_conj_xS_gL]
  exact (Subgroup.mem_normalizer_iff.mp (hN (levG_mem_normalizer p (gL s))) _).mp h

theorem irr_x100_mem (hp2 : p ≠ 2)
    (hN : Subgroup.normalizer ((xS p).U : Set (PSp4 p)) ≤ Subgroup.normalizer (W : Set (PSp4 p)))
    (h : (xS p).x a b c ∈ W) (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) : (xS p).x 1 0 0 ∈ W := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  have h1 : (xS p).x (2 * b + c) c 0 ∈ W :=
    irr_mem_congr p (irr_mem_sub p (irr_mem_gA p hN 1 h) h) (by ring) (by ring) (by ring)
  have h3 : (xS p).x (2 * c) 0 0 ∈ W :=
    irr_mem_congr p (irr_mem_sub p (irr_mem_gA p hN 1 h1) h1) (by ring) (by ring) (by ring)
  have key : ∃ t : ZMod p, t ≠ 0 ∧ (xS p).x t 0 0 ∈ W := by
    by_cases hc : c = 0
    · subst hc
      by_cases hb : b = 0
      · subst hb
        exact ⟨a, fun ha => hne ⟨ha, rfl, rfl⟩, h⟩
      · exact ⟨2 * b, mul_ne_zero h2 hb, irr_mem_congr p h1 (by ring) rfl rfl⟩
    · exact ⟨2 * c, mul_ne_zero h2 hc, h3⟩
  obtain ⟨t, ht, hxt⟩ := key
  have := irr_mem_smul p t⁻¹ hxt
  rwa [inv_mul_cancel₀ ht, mul_zero] at this

theorem irred_xS (hp2 : p ≠ 2) (W : Subgroup (PSp4 p)) (hWU : W ≤ (xS p).U)
    (hN : Subgroup.normalizer ((xS p).U : Set (PSp4 p)) ≤ Subgroup.normalizer (W : Set (PSp4 p))) :
    W = ⊥ ∨ W = (xS p).U := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨a, b, c, rfl⟩ := hWU hwW
  have hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hw1 (Subtype.ext (xS p).x_zero)
  have h100 : (xS p).x 1 0 0 ∈ W := irr_x100_mem p hp2 hN hwW hne
  have h111 : (xS p).x 1 1 1 ∈ W :=
    irr_mem_congr p (irr_mem_gL p hN 1 h100) rfl (by ring) (by ring)
  have h124 : (xS p).x 1 2 4 ∈ W :=
    irr_mem_congr p (irr_mem_gL p hN 2 h100) rfl (by ring) (by ring)
  have h013 : (xS p).x 0 1 3 ∈ W :=
    irr_mem_congr p (irr_mem_sub p h124 h111) (by ring) (by ring) (by ring)
  have h011 : (xS p).x 0 1 1 ∈ W :=
    irr_mem_congr p (irr_mem_sub p h111 h100) (by ring) (by ring) (by ring)
  have h002 : (xS p).x 0 0 2 ∈ W :=
    irr_mem_congr p (irr_mem_sub p h013 h011) (by ring) (by ring) (by ring)
  have h001 : (xS p).x 0 0 1 ∈ W :=
    irr_mem_congr p (irr_mem_smul p (2 : ZMod p)⁻¹ h002) (by ring) (by ring)
      (inv_mul_cancel₀ h2)
  have h010 : (xS p).x 0 1 0 ∈ W :=
    irr_mem_congr p (irr_mem_sub p h011 h001) (by ring) (by ring) (by ring)
  refine le_antisymm hWU ?_
  rintro _ ⟨a, b, c, rfl⟩
  have := W.mul_mem (W.mul_mem (irr_mem_smul p a h100) (irr_mem_smul p b h010))
    (irr_mem_smul p c h001)
  rw [XData.x_mul, XData.x_mul] at this
  exact irr_mem_congr p this (by ring) (by ring) (by ring)

end Siegel

section Entry

variable {F : Type} [Field F]

theorem irr_entry_proj_mem_projUnipotent {r : ℕ} {g : StatedSp r F}
    (hg : proj r F g ∈ projUnipotent r F) {i j : Fin r} (hij : j < i) :
    ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
      (Sum.inl i) (Sum.inl j) = 0 := by
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp hg
  obtain ⟨A, C, hA, -, huA⟩ := mem_unipotent.mp hu
  have hker : u⁻¹ * g ∈ (proj r F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hug, inv_mul_cancel]
  rw [show (proj r F).ker = (StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F) from
    QuotientGroup.ker_mk' _, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hker
  obtain ⟨c, hc⟩ := hker
  have hgu : (g : GL (Fin r ⊕ Fin r) F) =
      (u : GL (Fin r ⊕ Fin r) F) * Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have hgm := congrArg (fun x : GL (Fin r ⊕ Fin r) F =>
    (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) (Sum.inl i) (Sum.inl j)) hgu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, huA, blockMat, fromBlocks_apply₁₁] at hgm
  rw [hgm, hA.1 hij, zero_mul]

end Entry

section Conj

variable {F : Type} [Field F]

theorem irr_gL_inv (s : F) : (gL s)⁻¹ = gL (-s) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_gL, coe_gL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L2, Matrix.mul_apply, Fin.sum_univ_two]

theorem irr_conj_entry (s : F) :
    (((leviSp (gL s) * eEl 1 0 0 * (leviSp (gL s))⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 1) (Sum.inl 0) = -s ^ 2 := by
  rw [← map_inv, irr_gL_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_leviSp, coe_leviSp, coe_eEl, irr_gL_inv, irr_gL_inv, neg_neg, coe_gL, coe_gL]
  simp only [blockMat, fromBlocks_multiply, fromBlocks_apply₁₁]
  simp [L2, A2, C2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Conj

section NotNormalizer

variable (p : ℕ) [Fact p.Prime]

theorem not_normalizer_xS_le_normalizer_projUnipotent (_hp2 : p ≠ 2) (T : Subgroup (PSp4 p))
    (hT : T = projUnipotent 2 (ZMod p)) :
    ¬ Subgroup.normalizer ((xS p).U : Set (PSp4 p)) ≤ Subgroup.normalizer (T : Set (PSp4 p)) := by
  intro hN
  have hmem : proj 2 (ZMod p) (eEl 1 0 0) ∈ T := by
    rw [hT]
    exact Subgroup.mem_map_of_mem _ (eEl_mem_unipotent 1 0 0)
  have h := (Subgroup.mem_normalizer_iff.mp (hN (levG_mem_normalizer p (gL 1))) _).mp hmem
  rw [hT] at h
  have h' : proj 2 (ZMod p) (leviSp (gL 1) * eEl 1 0 0 * (leviSp (gL 1))⁻¹) ∈
      projUnipotent 2 (ZMod p) := by
    rw [map_mul, map_mul, map_inv]
    exact h
  have h0 := irr_entry_proj_mem_projUnipotent h' (i := 1) (j := 0) (by decide)
  rw [irr_conj_entry] at h0
  exact pow_ne_zero 2 one_ne_zero (neg_eq_zero.mp h0)

end NotNormalizer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
