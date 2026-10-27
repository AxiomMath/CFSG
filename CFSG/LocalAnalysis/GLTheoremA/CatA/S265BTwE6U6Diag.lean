module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStruct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6U6Lin
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

private theorem scalar_mem_uU_six (c : xunKˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ uU xunH 6 := by
  rw [mem_uU]
  have h1 : xunH.bar (c : xunK) * (c : xunK) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ]
    exact Good.pow_three_eq_one_of_ne_zero (Units.ne_zero c)
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [h1]
  · simp [hij, Ne.symm hij]

private theorem exists_lift_sq {t : xunM 6} (ht2 : t ^ 2 = 1) :
    ∃ s : StatedSU 6 (2 ^ 1) xunK, s ^ 2 = 1 ∧ projH _ s = t := by
  obtain ⟨r, rfl⟩ := projH_surjective t
  have h1 : r ^ 2 ∈ (StatedScalars (Fin 6) xunK).subgroupOf (StatedSU 6 (2 ^ 1) xunK) := by
    have h := ht2
    rw [← map_pow, projH, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 h1)
  refine ⟨r ^ 3, Subtype.ext ?_, ?_⟩
  · rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, Subgroup.coe_pow, ← hc, ← map_pow,
      Struct.units_pow_three xunK_card_four c, map_one]
    rfl
  · calc projH _ (r ^ 3) = projH _ r ^ 2 * projH _ r := by rw [map_pow]; exact pow_succ _ 2
      _ = projH _ r := by rw [ht2, one_mul (projH _ r)]

private theorem commute_of_fix (g : uU xunH 6) {s : StatedSU 6 (2 ^ 1) xunK} (hs : s ^ 2 = 1)
    (hfix : xunConj 6 (by norm_num) g (projH _ s) = projH _ s) :
    (g : GL (Fin 6) xunK) * s = s * g := by
  obtain ⟨z, hz, hgz⟩ := Good.exists_conj_eq_mul_central (by norm_num) g s hfix
  have hs2 : (s : GL (Fin 6) xunK) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hs, Subgroup.coe_one]
  have hzs : Commute (s : GL (Fin 6) xunK) z := Subgroup.mem_center_iff.1 hz _
  have hz2 : z ^ 2 = 1 := by
    have h1 : ((g : GL (Fin 6) xunK) * s * (g : GL (Fin 6) xunK)⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hs2, mul_one (g : GL (Fin 6) xunK), mul_inv_cancel]
    rw [hgz, hzs.mul_pow, hs2, one_mul (z ^ 2)] at h1
    exact h1
  have hz3 : z ^ 3 = 1 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [← map_pow, Struct.units_pow_three xunK_card_four c, map_one]
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  rw [hz1, mul_one (s : GL (Fin 6) xunK)] at hgz
  calc (g : GL (Fin 6) xunK) * s
      = (g : GL (Fin 6) xunK) * s * (g : GL (Fin 6) xunK)⁻¹ * g := by group
    _ = s * g := by rw [hgz]

theorem exists_diag_conj_of_fix_involution (A : Subgroup (MulAut (xunM 6)))
    (hA : IsElemAbelian 3 A) (h3 : 3 ^ 3 ≤ Nat.card A) {t : xunM 6} (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (hfix : ∀ a ∈ A, a t = t) :
    3 ^ 4 ≤ Nat.card (A.comap (xunConj 6 (by norm_num))) ∧
      ∃ c : uU xunH 6, ∀ g ∈ A.comap (xunConj 6 (by norm_num)),
        IsDiagU 6 ((c * g * c⁻¹ : uU xunH 6) : GL (Fin 6) xunK) := by
  have hN1 : 1 ≤ 6 := by norm_num
  set P : Subgroup (uU xunH 6) := A.comap (xunConj 6 hN1) with hP
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  let Φ : uU xunH 6 →* ((Fin 6 → xunK) ≃ₗ[xunK] (Fin 6 → xunK)) :=
    (xunLin 6).comp (uU xunH 6).subtype
  have hΦinj : Function.Injective Φ :=
    (xunLin_injective 6).comp (uU xunH 6).subtype_injective
  have hΦscal : ∀ g : uU xunH 6, xunConj 6 hN1 g = 1 →
      Φ g ∈ Struct.scalars xunK (Fin 6 → xunK) := by
    intro g hg
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff xunH (by norm_num) g).1 hg
    have : Φ g = xunLin 6 (Matrix.GeneralLinearGroup.scalar (Fin 6) c) := by
      change xunLin 6 (g : GL (Fin 6) xunK) = _
      rw [hc]
    rw [this]
    exact xunLin_scalar 6 c
  have hQgood : Struct.IsGoodIn (Struct.scalars xunK (Fin 6 → xunK)) (P.map Φ) := by
    constructor
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_commutatorElement]
      refine hΦscal _ ?_
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hAcomm _ hg _ hg')
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      refine hΦscal _ ?_
      rw [map_pow]
      exact hA.2 _ hg
  let s : P →* MulAut (xunM 6) := (xunConj 6 hN1).comp P.subtype
  have hrange : s.range = A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hP, Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun a ha =>
      KD264Lie.RowX1Un.le_range_xunConj_of_isElemAbelian4 (by norm_num) A hA a ha
  have hscal1 : ∀ c : xunKˣ, xunConj 6 hN1 ⟨_, scalar_mem_uU_six c⟩ = 1 := fun c =>
    (uConjAut_eq_one_iff xunH (by norm_num) _).2 ⟨c, rfl⟩
  have hker3 : 3 ≤ Nat.card s.ker := by
    let ι : xunKˣ → s.ker := fun c => ⟨⟨⟨_, scalar_mem_uU_six c⟩, by
      rw [hP, Subgroup.mem_comap, hscal1 c]
      exact A.one_mem⟩, MonoidHom.mem_ker.2 (hscal1 c)⟩
    have hinj : Function.Injective ι := by
      intro c c' h
      have h1 := congrArg (fun z : s.ker => (((z.1 : P) : uU xunH 6) : GL (Fin 6) xunK)) h
      have h2 := congrArg (fun g : GL (Fin 6) xunK => (g : Matrix (Fin 6) (Fin 6) xunK) 0 0) h1
      simp only [ι, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h2
      exact Units.ext h2
    have := Nat.card_le_card_of_injective ι hinj
    rwa [Struct.card_units_eq_three xunK_card_four] at this
  have hcardP : 3 ^ 4 ≤ Nat.card P := by
    have h := Good.card_eq_card_range_mul_card_ker s
    rw [hrange] at h
    rw [h]
    calc 3 ^ 4 = 3 ^ 3 * 3 := by norm_num
      _ ≤ Nat.card A * Nat.card s.ker := Nat.mul_le_mul h3 hker3
  obtain ⟨u, hu2, hut⟩ := exists_lift_sq ht2
  have hPu : ∀ g ∈ P, (g : GL (Fin 6) xunK) * u = u * g := fun g hg =>
    commute_of_fix g hu2 (by rw [hut]; exact hfix _ hg)
  have hU2 : xunLin 6 (u : GL (Fin 6) xunK) ^ 2 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hu2, Subgroup.coe_one, map_one]
  have hU1 : xunLin 6 (u : GL (Fin 6) xunK) ≠ 1 := by
    intro h1
    apply ht1
    have hu1 : u = 1 := Subtype.ext (xunLin_injective 6 (h1.trans (map_one _).symm))
    rw [← hut, hu1, map_one]
  have hQU : ∀ x ∈ P.map Φ, x * xunLin 6 (u : GL (Fin 6) xunK) =
      xunLin 6 (u : GL (Fin 6) xunK) * x := by
    rintro _ ⟨g, hg, rfl⟩
    change xunLin 6 (g : GL (Fin 6) xunK) * xunLin 6 (u : GL (Fin 6) xunK) =
      xunLin 6 (u : GL (Fin 6) xunK) * xunLin 6 (g : GL (Fin 6) xunK)
    rw [← map_mul, ← map_mul, hPu g hg]
  have hfin : Module.finrank xunK (Fin 6 → xunK) = 6 := by simp
  have hQcard : 3 ^ 4 ≤ Nat.card (P.map Φ) := by
    rw [Subgroup.card_map_of_injective hΦinj]
    exact hcardP
  obtain ⟨hQab, hQ3⟩ := abelian_exp_three_of_commute_involution xunK_card_four hfin hQgood
    hQcard hU2 hU1 hQU
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    apply hΦinj
    rw [map_mul, map_mul]
    exact hQab _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hPpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hΦinj
    rw [map_pow, map_one]
    exact hQ3 _ ⟨x, hx, rfl⟩
  obtain ⟨P0, hP0⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag xunH Nat.prime_three
    (by norm_num) P hPcomm hPpow
  refine ⟨hcardP, P0⁻¹, fun g hg i j hij => ?_⟩
  have := hP0 g hg hij
  rw [inv_inv]
  exact this

end CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

end
