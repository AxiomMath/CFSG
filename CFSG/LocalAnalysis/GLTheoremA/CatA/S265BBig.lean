module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigLin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BBig

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

private theorem pow_max_le {N a : ℕ} (hN5 : 5 ≤ N) (hN9 : N ≤ 9) (h4 : 3 ^ 4 ≤ a)
    (hn : 3 ^ N ≤ 3 ^ 3 * a) : 3 ^ (max 5 (N - 2)) ≤ 3 * a := by
  interval_cases N <;> norm_num at h4 hn ⊢ <;> omega

private theorem scalar_mem_uU_xun (N : ℕ) (c : xunKˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin N) c ∈ uU xunH N := by
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

theorem exists_diag_conj_of_isElemAbelian {N : ℕ} (hN5 : 5 ≤ N) (hN9 : N ≤ 9)
    (A : Subgroup (MulAut (xunM N))) (hA : IsElemAbelian 3 A) (h4 : 3 ^ 4 ≤ Nat.card A)
    (hn : 3 ^ N ≤ 3 ^ 3 * Nat.card A) :
    ∃ c : uU xunH N, ∀ g : uU xunH N, xunConj N (by omega) g ∈ A →
      IsDiagU N ((c * g * c⁻¹ : uU xunH N) : GL (Fin N) xunK) := by
  have hN1 : 1 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  set P : Subgroup (uU xunH N) := A.comap (xunConj N hN1) with hP
  have hker : ∀ g : uU xunH N, xunConj N hN1 g = 1 →
      ∃ c : xunKˣ, (g : GL (Fin N) xunK) = Matrix.GeneralLinearGroup.scalar (Fin N) c :=
    fun g hg => (uConjAut_eq_one_iff xunH hN3 g).1 hg
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  let Φ : uU xunH N →* ((Fin N → xunK) ≃ₗ[xunK] (Fin N → xunK)) :=
    (xunLin N).comp (uU xunH N).subtype
  have hΦinj : Function.Injective Φ :=
    (xunLin_injective N).comp (uU xunH N).subtype_injective
  have hΦscal : ∀ g : uU xunH N, (∃ c : xunKˣ,
      (g : GL (Fin N) xunK) = Matrix.GeneralLinearGroup.scalar (Fin N) c) →
      Φ g ∈ Struct.scalars xunK (Fin N → xunK) := by
    rintro g ⟨c, hc⟩
    have : Φ g = xunLin N (Matrix.GeneralLinearGroup.scalar (Fin N) c) := by
      change xunLin N (g : GL (Fin N) xunK) = _
      rw [hc]
    rw [this]
    exact xunLin_scalar N c
  have hQgood : Struct.IsGoodIn (Struct.scalars xunK (Fin N → xunK)) (P.map Φ) := by
    constructor
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      have hc : xunConj N hN1 ⁅g, g'⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hAcomm _ hg _ hg')
      rw [← map_commutatorElement]
      exact hΦscal _ (hker _ hc)
    · rintro _ ⟨g, hg, rfl⟩
      have hc : xunConj N hN1 (g ^ 3) = 1 := by
        rw [map_pow]
        exact hA.2 _ hg
      rw [← map_pow]
      exact hΦscal _ (hker _ hc)
  let s : P →* MulAut (xunM N) := (xunConj N hN1).comp P.subtype
  have hAle : A ≤ (xunConj N hN1).range := fun a ha =>
    KD264Lie.RowX1Un.le_range_xunConj_of_isElemAbelian4 (by omega) A hA a ha
  have hrange : s.range = A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hP, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hAle
  have hscal1 : ∀ c : xunKˣ, xunConj N hN1 ⟨_, scalar_mem_uU_xun N c⟩ = 1 := fun c =>
    (uConjAut_eq_one_iff xunH hN3 _).2 ⟨c, rfl⟩
  have hker3 : 3 ≤ Nat.card s.ker := by
    let ι : xunKˣ → s.ker := fun c => ⟨⟨⟨_, scalar_mem_uU_xun N c⟩, by
      rw [hP, Subgroup.mem_comap, hscal1 c]
      exact A.one_mem⟩, MonoidHom.mem_ker.2 (hscal1 c)⟩
    have hinj : Function.Injective ι := by
      intro c c' h
      have h1 := congrArg (fun z : s.ker => (((z.1 : P) : uU xunH N) : GL (Fin N) xunK)) h
      have h2 := congrArg (fun g : GL (Fin N) xunK =>
        (g : Matrix (Fin N) (Fin N) xunK) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
      simp only [ι, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h2
      exact Units.ext h2
    have := Nat.card_le_card_of_injective ι hinj
    rwa [Struct.card_units_eq_three xunK_card_four] at this
  have hcardP : 3 * Nat.card A ≤ Nat.card P := by
    have h := Good.card_eq_card_range_mul_card_ker s
    rw [hrange] at h
    rw [h, Nat.mul_comm (Nat.card A)]
    exact Nat.mul_le_mul_right _ hker3
  have hcard : 3 ^ (max 5 (N - 2)) ≤ Nat.card (P.map Φ) := by
    rw [Subgroup.card_map_of_injective hΦinj]
    exact (pow_max_le hN5 hN9 h4 hn).trans hcardP
  have hfin : Module.finrank xunK (Fin N → xunK) = N := by simp
  obtain ⟨hQab, hQ3⟩ := abelian_exp_three_of_card_le_nine xunK_card_four hfin hN5 hN9 hQgood hcard
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
  refine ⟨P0⁻¹, fun g hg i j hij => ?_⟩
  have := hP0 g hg hij
  rw [inv_inv]
  exact this

end CFSG.LocalAnalysis.GLTheoremA.S265.BBig

end
