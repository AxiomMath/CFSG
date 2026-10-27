module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ORadD

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply polar_quadMinus)

section ParA

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem RadHyp.f_apply {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h) (x : OW F)
    (i : Fin (3 - 1)) : gv h x (Sum.inr (Sum.inl i)) = x (Sum.inr (Sum.inl i)) := by
  have := hh.trivV x i
  simp only [Pi.sub_apply] at this
  exact sub_eq_zero.mp this

theorem RadHyp.n_apply {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h) (z : OW F)
    (hz : ∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) (j : Fin 2) :
    gv h z (Sum.inr (Sum.inr j)) = z (Sum.inr (Sum.inr j)) := by
  have := hh.trivZ z hz j
  simp only [Pi.sub_apply] at this
  exact sub_eq_zero.mp this

theorem radHyp_one : RadHyp b c (1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) where
  iso v := by rw [gv_one]
  fixE i := gv_one _
  trivV x i := by rw [gv_one, sub_self]; rfl
  trivZ z _ j := by rw [gv_one, sub_self]; rfl

theorem radHyp_mul {g h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hg : RadHyp b c g)
    (hh : RadHyp b c h) : RadHyp b c (g * h) where
  iso v := by rw [gv_mul, hg.iso, hh.iso]
  fixE i := by rw [gv_mul, hh.fixE, hg.fixE]
  trivV x i := by
    simp only [Pi.sub_apply, gv_mul, hg.f_apply, hh.f_apply, sub_self]
  trivZ z hz j := by
    have hz' : ∀ i : Fin (3 - 1), gv h z (Sum.inr (Sum.inl i)) = 0 := fun i => by
      rw [hh.f_apply, hz i]
    have h1 := hg.trivZ (gv h z) hz' j
    have h2 := hh.trivZ z hz j
    simp only [Pi.sub_apply] at h1 h2 ⊢
    rw [gv_mul]
    linear_combination h1 + h2

theorem radHyp_inv {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hg : RadHyp b c g) :
    RadHyp b c g⁻¹ where
  iso v := by
    have := hg.iso (gv g⁻¹ v)
    rw [gv_gv_inv] at this
    exact this.symm
  fixE i := by
    have := congrArg (gv g⁻¹) (hg.fixE i)
    rw [gv_inv_gv] at this
    exact this.symm
  trivV x i := by
    have h1 := hg.f_apply (gv g⁻¹ x) i
    rw [gv_gv_inv] at h1
    simp only [Pi.sub_apply]
    rw [← h1]
    exact sub_self _
  trivZ z hz j := by
    have hz' : ∀ i : Fin (3 - 1), gv g⁻¹ z (Sum.inr (Sum.inl i)) = 0 := fun i => by
      have h1 := hg.f_apply (gv g⁻¹ z) i
      rw [gv_gv_inv] at h1
      rw [← h1]
      exact hz i
    have h1 := hg.n_apply (gv g⁻¹ z) hz' j
    rw [gv_gv_inv] at h1
    simp only [Pi.sub_apply]
    rw [← h1]
    exact sub_self _

@[expose] def RadGrp (b c : F) : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) where
  carrier := {g | RadHyp b c g}
  mul_mem' := fun {_ _} hg hh => radHyp_mul hg hh
  one_mem' := radHyp_one
  inv_mem' := fun {_} hg => radHyp_inv hg

theorem mem_RadGrp {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} :
    g ∈ RadGrp b c ↔ RadHyp b c g := Iff.rfl

theorem RadHyp.fix_of_inY {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h)
    {y : OW F} (hf : ∀ i : Fin (3 - 1), y (Sum.inr (Sum.inl i)) = 0)
    (hn : ∀ j : Fin 2, y (Sum.inr (Sum.inr j)) = 0) : gv h y = y := by
  conv_lhs => rw [vec_decomp y]
  rw [hf idx0, hf idx1, hn 0, hn 1]
  simp only [zero_smul, add_zero, gv_add, gv_smul, hh.fixE]
  conv_rhs => rw [vec_decomp y]
  rw [hf idx0, hf idx1, hn 0, hn 1]
  simp only [zero_smul, add_zero]

theorem rad_pow_four {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hg : RadHyp b c g) :
    g * g * g * g = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdbl : ∀ y : OW F, y + y = 0 := fun y => by rw [← two_smul F y, h2, zero_smul]
  refine gl_ext fun x => ?_
  rw [gv_one]
  simp only [gv_mul]
  set a : OW F := gv g x - x with ha
  have haf : ∀ i : Fin (3 - 1), a (Sum.inr (Sum.inl i)) = 0 := fun i => hg.trivV x i
  set b' : OW F := gv g a - a with hb'
  have hbf : ∀ i : Fin (3 - 1), b' (Sum.inr (Sum.inl i)) = 0 := fun i => hg.trivV a i
  have hbn : ∀ j : Fin 2, b' (Sum.inr (Sum.inr j)) = 0 := fun j => hg.trivZ a haf j
  have hgb : gv g b' = b' := hg.fix_of_inY hbf hbn
  have e1 : gv g x = x + a := by rw [ha]; abel
  have e2 : gv g a = a + b' := by rw [hb']; abel
  have e3 : gv g (gv g x) = x + b' := by
    rw [e1, gv_add, e1, e2]
    calc x + a + (a + b') = x + (a + a) + b' := by abel
      _ = x + b' := by rw [hdbl a, add_zero]
  have e4 : gv g (gv g (x + b')) = x := by
    rw [gv_add, gv_add, e3, hgb, hgb]
    calc x + b' + b' = x + (b' + b') := by abel
      _ = x := by rw [hdbl b', add_zero]
  rw [e3, e4]

theorem RadGrp_isPGroup : IsPGroup 2 ↥(RadGrp b c) := fun q => ⟨2, Subtype.ext (by
  have h4 : (q : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ^ (2 ^ 2) = q * q * q * q := by
    norm_num [pow_succ, mul_assoc]
  show (q : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) ^ (2 ^ 2) = 1
  rw [h4]
  exact rad_pow_four q.2)⟩

theorem iso_preserves_Z {ξ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hξ : ∀ v : OW F, quadMinus 3 F b c (gv ξ v) = quadMinus 3 F b c v)
    (hY' : ∀ i : Fin (3 - 1), ∃ s t : F, gv ξ⁻¹ (eV F i) = s • eV F idx0 + t • eV F idx1)
    {z : OW F} (hz : ∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) (i : Fin (3 - 1)) :
    gv ξ z (Sum.inr (Sum.inl i)) = 0 := by
  obtain ⟨s, t, hst⟩ := hY' i
  have h1 := polar_gv hξ z (gv ξ⁻¹ (eV F i))
  rw [gv_gv_inv] at h1
  rw [polar_e_right] at h1
  rw [h1, hst, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_e_right,
    polar_e_right, hz idx0, hz idx1]
  ring

theorem iso_preserves_Y {ξ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hY : ∀ i : Fin (3 - 1), ∃ s t : F, gv ξ (eV F i) = s • eV F idx0 + t • eV F idx1)
    {y : OW F} (hf : ∀ i : Fin (3 - 1), y (Sum.inr (Sum.inl i)) = 0)
    (hn : ∀ j : Fin 2, y (Sum.inr (Sum.inr j)) = 0) :
    (∀ i : Fin (3 - 1), gv ξ y (Sum.inr (Sum.inl i)) = 0) ∧
      ∀ j : Fin 2, gv ξ y (Sum.inr (Sum.inr j)) = 0 := by
  have hne01 : idx0 ≠ idx1 := by decide
  have hy : y = y (Sum.inl idx0) • eV F idx0 + y (Sum.inl idx1) • eV F idx1 := by
    conv_lhs => rw [vec_decomp y]
    rw [hf idx0, hf idx1, hn 0, hn 1]
    simp only [zero_smul, add_zero]
  obtain ⟨s0, t0, h0⟩ := hY idx0
  obtain ⟨s1, t1, h1⟩ := hY idx1
  have hξy : gv ξ y = y (Sum.inl idx0) • (s0 • eV F idx0 + t0 • eV F idx1) +
      y (Sum.inl idx1) • (s1 • eV F idx0 + t1 • eV F idx1) := by
    conv_lhs => rw [hy]
    rw [gv_add, gv_smul, gv_smul, h0, h1]
  rw [hξy]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eV_inr, mul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eV_inr, mul_zero, add_zero]

theorem rad_conj_mem {ξ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hξ : ∀ v : OW F, quadMinus 3 F b c (gv ξ v) = quadMinus 3 F b c v)
    (hY : ∀ i : Fin (3 - 1), ∃ s t : F, gv ξ (eV F i) = s • eV F idx0 + t • eV F idx1)
    (hY' : ∀ i : Fin (3 - 1), ∃ s t : F, gv ξ⁻¹ (eV F i) = s • eV F idx0 + t • eV F idx1)
    (hg : RadHyp b c g) : RadHyp b c (ξ * g * ξ⁻¹) where
  iso v := by
    rw [gv_mul, gv_mul, hξ, hg.iso]
    have := hξ (gv ξ⁻¹ v)
    rw [gv_gv_inv] at this
    exact this.symm
  fixE i := by
    obtain ⟨s, t, hst⟩ := hY' i
    rw [gv_mul, gv_mul, hst, gv_add, gv_smul, gv_smul, hg.fixE, hg.fixE, ← hst]
    exact gv_gv_inv ξ _
  trivV x i := by
    have hZ : ∀ i : Fin (3 - 1), (gv g (gv ξ⁻¹ x) - gv ξ⁻¹ x) (Sum.inr (Sum.inl i)) = 0 :=
      fun i => hg.trivV _ i
    have h1 := iso_preserves_Z hξ hY' (z := gv g (gv ξ⁻¹ x) - gv ξ⁻¹ x) hZ i
    rw [gv_sub, gv_gv_inv] at h1
    simp only [Pi.sub_apply] at h1 ⊢
    rw [gv_mul, gv_mul]
    exact h1
  trivZ z hz j := by
    have hinvξ : ∀ i : Fin (3 - 1), ∃ s t : F, gv (ξ⁻¹)⁻¹ (eV F i) = s • eV F idx0 + t • eV F idx1 := by
      rw [inv_inv]; exact hY
    have hξi : ∀ v : OW F, quadMinus 3 F b c (gv ξ⁻¹ v) = quadMinus 3 F b c v := by
      intro v
      have := hξ (gv ξ⁻¹ v)
      rw [gv_gv_inv] at this
      exact this.symm
    have hy : ∀ i : Fin (3 - 1), gv ξ⁻¹ z (Sum.inr (Sum.inl i)) = 0 :=
      fun i => iso_preserves_Z hξi hinvξ hz i
    have hu1 : ∀ i : Fin (3 - 1), (gv g (gv ξ⁻¹ z) - gv ξ⁻¹ z) (Sum.inr (Sum.inl i)) = 0 :=
      fun i => hg.trivV _ i
    have hu2 : ∀ j : Fin 2, (gv g (gv ξ⁻¹ z) - gv ξ⁻¹ z) (Sum.inr (Sum.inr j)) = 0 :=
      fun j => hg.trivZ _ hy j
    have h3 := (iso_preserves_Y hY hu1 hu2).2 j
    rw [gv_sub, gv_gv_inv] at h3
    simp only [Pi.sub_apply] at h3 ⊢
    rw [gv_mul, gv_mul]
    exact h3

theorem rad_of_involution (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hgΩ : g ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (hg2 : g * g = 1) (hfix : ∀ i : Fin (3 - 1), gv g (eV F i) = eV F i) : RadHyp b c g := by
  have hiso : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v :=
    fun v => quadMinus_mulVec_of_mem_statedOmega hgΩ v
  refine ⟨hiso, hfix, fun x i => ?_, fun z hz j => rho_trivial hirr hgΩ hg2 hfix z hz j⟩
  have h1 := polar_gv hiso x (eV F i)
  rw [hfix, polar_e_right, polar_e_right] at h1
  simp only [Pi.sub_apply]
  rw [h1]
  exact sub_self _

end ParA

end CFSG.LocalAnalysis.RankThreeUC
