module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTori
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadOdd)

variable {K : Type} [Field K] [Finite K]

section Types

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] in
theorem finrank_quadPlus_space (m : ℕ) : finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]

omit [Finite K] in
theorem finrank_quadMinus_space {m : ℕ} (hm : 1 ≤ m) :
    finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

omit [Finite K] in
theorem nonempty_isometry_quadPlus_prod (d r : ℕ) {k : ℕ} (hk : k = d + r) :
    Nonempty (((quadPlus d K).prod (quadPlus r K)).IsometryEquiv (quadPlus k K)) :=
  nonempty_isometry_quadPlus
    (nondegenerate_polarBilin_prod
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus d K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K))
    (by rw [Module.finrank_prod, finrank_quadPlus_space, finrank_quadPlus_space, hk]; ring)
    ((isPlusType_quadPlus K d).prod (isPlusType_quadPlus K r))

theorem not_isPlusType_prod_quadMinus {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {d : ℕ} (hdim : finrank K V = 2 * d) (h : IsPlusType Q)
    {r : ℕ} (hr : 1 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsPlusType (Q.prod (quadMinus r K b c)) := by
  obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ hdim h
  obtain ⟨e₂⟩ := nonempty_isometry_quadPlus_prod (K := K) d (r - 1) (k := d + r - 1) (by omega)
  have e' : (Q.prod (quadMinus r K b c)).IsometryEquiv (quadMinus (d + r) K b c) :=
    (e.prod (quadMinusIsometry r b c)).trans
      ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
        ((e₂.prod (QuadraticMap.IsometryEquiv.refl _)).trans
          (quadMinusIsometry (d + r) b c).symm))
  rw [isPlusType_congr e']
  exact not_isPlusType_quadMinus (by omega) hirr

theorem not_isPlusType_prod_quadPlus {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {d : ℕ} (hd : 1 ≤ d) (hdim : finrank K V = 2 * d)
    (h : ¬ IsPlusType Q) (r : ℕ) : ¬ IsPlusType (Q.prod (quadPlus r K)) := by
  rcases exists_isometry_quadPlus_or_quadMinus Q hQ hd hdim with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K d)) h
  obtain ⟨e⟩ := he
  obtain ⟨e₂⟩ := nonempty_isometry_quadPlus_prod (K := K) (d - 1) r (k := d + r - 1) (by omega)
  have e' : (Q.prod (quadPlus r K)).IsometryEquiv (quadMinus (d + r) K b c) :=
    ((e.trans (quadMinusIsometry d b c)).prod (QuadraticMap.IsometryEquiv.refl _)).trans
      ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).trans
        (((QuadraticMap.IsometryEquiv.refl _).prod
          (QuadraticMap.IsometryEquiv.prodComm _ _)).trans
          ((QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
            ((e₂.prod (QuadraticMap.IsometryEquiv.refl _)).trans
              (quadMinusIsometry (d + r) b c).symm))))
  rw [isPlusType_congr e']
  exact not_isPlusType_quadMinus (by omega) hirr

theorem isPlusType_prod_quadMinus {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    {d : ℕ} (hd : 1 ≤ d) (hdim : finrank K V = 2 * d) (h : ¬ IsPlusType Q) (r : ℕ)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsPlusType (Q.prod (quadMinus r K b c)) := by
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType hQ hd hdim h hirr
  obtain ⟨φ, hφ⟩ := exists_binForm_similitude hirr (neg_ne_zero.2 (one_ne_zero (α := K)))
  let e' := (e.trans (quadMinusIsometry d b c)).prod (quadMinusIsometry r b c)
  rw [isPlusType_congr e']
  let j : ((Fin (d - 1) → K) × (Fin (r - 1) → K)) × (K × K) →ₗ[K]
      ((Fin (d - 1) ⊕ Fin (d - 1) → K) × (K × K)) × ((Fin (r - 1) ⊕ Fin (r - 1) → K) × (K × K)) :=
    LinearMap.prod
      (LinearMap.prod ((plusHalf K (d - 1)).comp ((LinearMap.fst _ _ _).comp (LinearMap.fst _ _ _)))
        (LinearMap.snd _ _ _))
      (LinearMap.prod ((plusHalf K (r - 1)).comp ((LinearMap.snd _ _ _).comp (LinearMap.fst _ _ _)))
        (φ.toLinearMap.comp (LinearMap.snd _ _ _)))
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 := congrArg (fun z => z.1.1) hxy
    have h2 := congrArg (fun z => z.2.1) hxy
    have h3 := congrArg (fun z => z.1.2) hxy
    exact Prod.ext (Prod.ext (plusHalf_injective _ h1) (plusHalf_injective _ h2)) h3
  refine ⟨LinearMap.range j, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj]
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self,
      finrank_quadPlus_space]
    omega
  · rintro _ ⟨x, rfl⟩
    change ((quadPlus (d - 1) K).prod (binForm b c) (plusHalf K (d - 1) x.1.1, x.2)) +
      ((quadPlus (r - 1) K).prod (binForm b c) (plusHalf K (r - 1) x.1.2, φ x.2)) = 0
    simp only [QuadraticMap.prod_apply, hφ]
    have h1 : ∀ m (y : Fin m → K), quadPlus m K (plusHalf K m y) = 0 := fun m y => by
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [plusHalf]
    rw [h1, h1]
    ring

end Types

omit [Finite K] in
theorem exists_injective_orthogonal_of_prod {G : Type} [Group G] (X T : FormSpace K K)
    {QX : QuadraticForm K X.V} {QT : QuadraticForm K T.V} (hX : ∀ x y, X.F x y = QX x)
    (hT : ∀ x y, T.F x y = QT x) (φ : G →* X.isom) (hφ : Function.Injective φ) {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (e : (QX.prod QT).IsometryEquiv Q) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_rep_prod X T φ hφ
  have hXT : ∀ x y, (X.prod T).F x y = (QX.prod QT) x := fun x y => by
    change X.F x.1 y.1 + T.F x.2 y.2 = _
    rw [hX, hT, QuadraticMap.prod_apply]
  let ι := (isomEquivOrthogonal (X.prod T) hXT).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr e)
  exact ⟨ι.toMonoidHom.comp ψ₀, ι.injective.comp hψ₀⟩

end CFSG.GroupTheory.WeirSylow
