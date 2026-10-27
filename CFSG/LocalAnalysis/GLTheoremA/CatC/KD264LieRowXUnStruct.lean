module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructKey
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

@[expose] noncomputable def xunLin (N : ℕ) :
    GL (Fin N) xunK →* ((Fin N → xunK) ≃ₗ[xunK] (Fin N → xunK)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv xunK (Fin N → xunK)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := xunK)).toMonoidHom

theorem xunLin_injective (N : ℕ) : Function.Injective (xunLin N) :=
  fun _ _ h => (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := xunK)).injective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv xunK (Fin N → xunK)).injective h)

theorem xunLin_apply (N : ℕ) (g : GL (Fin N) xunK) (v : Fin N → xunK) :
    xunLin N g v = Matrix.mulVec (g : Matrix (Fin N) (Fin N) xunK) v := rfl

theorem xunLin_scalar (N : ℕ) (c : xunKˣ) :
    xunLin N (Matrix.GeneralLinearGroup.scalar (Fin N) c) ∈
      Struct.scalars xunK (Fin N → xunK) := by
  rw [Struct.mem_scalars_iff]
  refine ⟨c, fun v => ?_⟩
  rw [xunLin_apply, Matrix.GeneralLinearGroup.coe_scalar]
  funext x
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem xunK_card_four : Nat.card xunK = 4 := by
  rw [xunK_card]
  norm_num

theorem kd264XUnTorusStruct_holds : KD264XUnTorusStruct := by
  intro N hN _h3 A hA hrank
  have hN1 : 1 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  set P : Subgroup (uU xunH N) := A.comap (xunConj N hN1) with hP
  have hker : ∀ g : uU xunH N, xunConj N hN1 g = 1 →
      ∃ c : xunKˣ, (g : GL (Fin N) xunK) = Matrix.GeneralLinearGroup.scalar (Fin N) c :=
    fun g hg => (uConjAut_eq_one_iff xunH hN3 g).1 hg
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := hA.2
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
        exact hApow _ hg
      rw [← map_pow]
      exact hΦscal _ (hker _ hc)
  have hcard : 3 ^ (N - 2) ≤ Nat.card (P.map Φ) := by
    rw [Subgroup.card_map_of_injective hΦinj]
    have h1 : Nat.card A ≤ Nat.card P := by
      apply Nat.card_le_card_of_surjective (fun g : P => (⟨xunConj N hN1 g, g.2⟩ : A))
      intro a
      obtain ⟨g, hg⟩ := le_range_xunConj_of_isElemAbelian hN A hA a a.2
      exact ⟨⟨g, by rw [hP, Subgroup.mem_comap, hg]; exact a.2⟩, Subtype.ext hg⟩
    have h2 : Nat.card A = 3 ^ CFSG.Open.pRank 3 A :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hA
    calc 3 ^ (N - 2) ≤ 3 ^ CFSG.Open.pRank 3 A := Nat.pow_le_pow_right (by norm_num) hrank
      _ = Nat.card A := h2.symm
      _ ≤ Nat.card P := h1
  have hfin : Module.finrank xunK (Fin N → xunK) = N := by simp
  obtain ⟨hQab, hQ3⟩ := Struct.abelian_exp_three_of_card xunK_card_four hfin hN hQgood hcard
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

theorem kd264XUnRow_holds : KD264XUnRow :=
  kd264XUnRow_of_pieces kd264XUnTorusStruct_holds Good.kd264XUnTorusGood_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

end
