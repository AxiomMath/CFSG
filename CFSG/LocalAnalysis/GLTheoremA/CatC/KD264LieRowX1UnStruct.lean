module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

section Lemmas

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem abelian_exp_three_of_card7 [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {N : ℕ} (hN : Module.finrank K V = N) (hN7 : 7 ≤ N) {Q : Subgroup (V ≃ₗ[K] V)}
    (hQ : Struct.IsGoodIn (Struct.scalars K V) Q) (hcard : 3 ^ (N - 1) ≤ Nat.card Q) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := Struct.finite_linearEquiv
  have hZ := Struct.scalarLike_scalars (V := V) hK
  by_cases hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  · refine ⟨hab, ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx3⟩ := hne
    have hc' : 3 ^ (Module.finrank K V - 2) ≤ Nat.card Q := by
      rw [hN]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard
    have := Struct.finrank_le_six_of_abelian hK hQ hab hx hx3 hc'
    omega
  · exfalso
    obtain ⟨g, hg, h, hh, hg3, hgh⟩ := Struct.exists_pow_three_eq_one_noncomm hZ hQ hab
    obtain ⟨n, hn3, hcardn⟩ := Struct.card_le_of_nonab hK hQ hg hh hg3 hgh
    have h1 : 3 ^ (N - 1) ≤ 3 ^ (2 + (n + n / 2)) := hcard.trans hcardn
    have h2 : N - 1 ≤ 2 + (n + n / 2) := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    rw [hN] at hn3
    omega

end Lemmas

theorem kd264X1UnTorusStruct7 {N : ℕ} (hN : 7 ≤ N) (A : Subgroup (MulAut (xunM N)))
    (hA : IsElemAbelian 3 A) (hrank : N - 1 ≤ CFSG.Open.pRank 3 A) :
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
  have hcard : 3 ^ (N - 1) ≤ Nat.card (P.map Φ) := by
    rw [Subgroup.card_map_of_injective hΦinj]
    have h1 : Nat.card A ≤ Nat.card P := by
      apply Nat.card_le_card_of_surjective (fun g : P => (⟨xunConj N hN1 g, g.2⟩ : A))
      intro a
      obtain ⟨g, hg⟩ := le_range_xunConj_of_isElemAbelian4 (by omega) A hA a a.2
      exact ⟨⟨g, by rw [hP, Subgroup.mem_comap, hg]; exact a.2⟩, Subtype.ext hg⟩
    have h2 : Nat.card A = 3 ^ CFSG.Open.pRank 3 A :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hA
    calc 3 ^ (N - 1) ≤ 3 ^ CFSG.Open.pRank 3 A := Nat.pow_le_pow_right (by norm_num) hrank
      _ = Nat.card A := h2.symm
      _ ≤ Nat.card P := h1
  have hfin : Module.finrank xunK (Fin N → xunK) = N := by simp
  obtain ⟨hQab, hQ3⟩ := abelian_exp_three_of_card7 xunK_card_four hfin hN hQgood hcard
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

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

end
