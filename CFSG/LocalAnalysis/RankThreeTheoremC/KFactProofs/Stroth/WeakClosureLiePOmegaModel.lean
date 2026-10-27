module

public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Comm

variable {K : Type} [Field K]

theorem finrank_commSpace_conj {W V : Type} [AddCommGroup W] [Module K W] [AddCommGroup V]
    [Module K V] (E : W ≃ₗ[K] V) (g : W ≃ₗ[K] W) :
    finrank K (commSpace (E.symm.trans (g.trans E))) = finrank K (commSpace g) := by
  have h : commSpace (E.symm.trans (g.trans E)) = (commSpace g).map (E : W →ₗ[K] V) := by
    ext x
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace, Submodule.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨g (E.symm v) - E.symm v, CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.2
        ⟨E.symm v, rfl⟩, ?_⟩
      simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.1 hy
      exact ⟨E w, by simp⟩
  rw [h]
  exact LinearEquiv.finrank_map_eq E _

theorem finrank_commSpace_prodCongr {W X : Type} [AddCommGroup W] [Module K W] [AddCommGroup X]
    [Module K X] (g : W ≃ₗ[K] W) :
    finrank K (commSpace (g.prodCongr (1 : X ≃ₗ[K] X))) = finrank K (commSpace g) := by
  have h : commSpace (g.prodCongr (1 : X ≃ₗ[K] X)) = (commSpace g).map (LinearMap.inl K W X) := by
    ext ⟨x, y⟩
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace, Submodule.mem_map]
    constructor
    · rintro ⟨v, hv⟩
      have h1 : g v.1 - v.1 = x := congrArg Prod.fst hv
      have h2 : y = 0 := by simpa using (congrArg Prod.snd hv).symm
      exact ⟨x, CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.2 ⟨v.1, h1⟩, by simp [h2]⟩
    · rintro ⟨z, hz, hzx⟩
      obtain ⟨w, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.1 hz
      refine ⟨(w, 0), ?_⟩
      have := congrArg Prod.fst hzx
      have h2 := congrArg Prod.snd hzx
      simp only [LinearMap.inl_apply] at this h2
      ext
      · simpa using this
      · simpa using h2
  rw [h]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end Comm

section Embedding

variable {K : Type} [Field K] [Finite K]

theorem exists_orthogonal_of_prod_comm {G : Type} [Group G] (X T : FormSpace K K)
    {QX : QuadraticForm K X.V} {QT : QuadraticForm K T.V} (hX : ∀ x y, X.F x y = QX x)
    (hT : ∀ x y, T.F x y = QT x) (φ : G →* X.isom) (hφ : Function.Injective φ) {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (e : (QX.prod QT).IsometryEquiv Q) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ ∧
      ∀ g, finrank K (commSpace (ψ g : V ≃ₗ[K] V)) =
        finrank K (commSpace (φ g : X.V ≃ₗ[K] X.V)) := by
  let ψ₀ : G →* (X.prod T).isom := (prodIsometryHom K X.F T.F).comp (φ.prod 1)
  have hψ₀ : Function.Injective ψ₀ :=
    (prodIsometryHom_injective K X.F T.F).comp fun _ _ h => hφ (congrArg Prod.fst h)
  have hXT : ∀ x y, (X.prod T).F x y = (QX.prod QT) x := fun x y => by
    change X.F x.1 y.1 + T.F x.2 y.2 = _
    rw [hX, hT, QuadraticMap.prod_apply]
  let ι := (isomEquivOrthogonal (X.prod T) hXT).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr e)
  refine ⟨ι.toMonoidHom.comp ψ₀, ι.injective.comp hψ₀, fun g => ?_⟩
  have h1 : (((ι.toMonoidHom.comp ψ₀) g : TauCeti.QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[K] V) = e.toLinearEquiv.symm.trans (((φ g : X.V ≃ₗ[K] X.V).prodCongr
        (1 : T.V ≃ₗ[K] T.V)).trans e.toLinearEquiv) := by
    refine LinearEquiv.ext fun m => ?_
    show (TauCeti.QuadraticMap.orthogonalGroupCongr e
      (isomEquivOrthogonal (X.prod T) hXT (ψ₀ g)) : V ≃ₗ[K] V) m = _
    rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
    rfl
  rw [h1, finrank_commSpace_conj, finrank_commSpace_prodCongr]

theorem exists_orthogonal_embedding_comm {G : Type} [Group G] (S : FormSpace K K)
    {QS : QuadraticForm K S.V} (hSF : ∀ x y, S.F x y = QS x) (hQS : (polarBilin QS).Nondegenerate)
    {t : ℕ} (hSdim : finrank K S.V = 2 * t) (φ : G →* S.isom) (hφ : Function.Injective φ)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n) (htn : t ≤ n)
    (htype : t = n → (IsPlusType QS ↔ IsPlusType Q)) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ ∧
      ∀ g, finrank K (commSpace (ψ g : V ≃ₗ[K] V)) =
        finrank K (commSpace (φ g : S.V ≃ₗ[K] S.V)) := by
  rcases eq_or_lt_of_le htn with rfl | hlt
  · obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hQS hQ hSdim hdim (htype rfl)
    let ι := (isomEquivOrthogonal S hSF).trans (TauCeti.QuadraticMap.orthogonalGroupCongr e)
    refine ⟨ι.toMonoidHom.comp φ, ι.injective.comp hφ, fun g => ?_⟩
    have h1 : (((ι.toMonoidHom.comp φ) g : TauCeti.QuadraticMap.orthogonalGroup Q) :
        V ≃ₗ[K] V) = e.toLinearEquiv.symm.trans ((φ g : S.V ≃ₗ[K] S.V).trans e.toLinearEquiv) := by
      refine LinearEquiv.ext fun m => ?_
      show (TauCeti.QuadraticMap.orthogonalGroupCongr e
        (isomEquivOrthogonal S hSF (φ g)) : V ≃ₗ[K] V) m = _
      rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
      rfl
    rw [h1, finrank_commSpace_conj]
  obtain ⟨b₀, c₀, hirr⟩ := exists_irreducible_quadratic K
  set r := n - t with hr
  have hr1 : 1 ≤ r := by omega
  have hS0 : t = 0 → IsPlusType QS := fun h => isPlusType_of_finrank_eq_zero QS (by omega)
  by_cases hiff : IsPlusType QS ↔ IsPlusType Q
  · let T : FormSpace K K := ⟨Fin r ⊕ Fin r → K, fun x _ => quadPlus r K x⟩
    have hT : ∀ x y, T.F x y = quadPlus r K x := fun _ _ => rfl
    have hnd := nondegenerate_polarBilin_prod hQS
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K)
    have htyp : IsPlusType (QS.prod (quadPlus r K)) ↔ IsPlusType Q := by
      by_cases hp : IsPlusType QS
      · exact ⟨fun _ => hiff.1 hp, fun _ => hp.prod (isPlusType_quadPlus K r)⟩
      · have ht1 : 1 ≤ t := by
          by_contra h0
          exact hp (hS0 (by omega))
        exact ⟨fun h => absurd h (not_isPlusType_prod_quadPlus hQS ht1 hSdim hp r),
          fun h => absurd (hiff.2 h) hp⟩
    obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hnd hQ
      (by rw [Module.finrank_prod, hSdim, finrank_quadPlus_space]; omega) hdim htyp
    exact exists_orthogonal_of_prod_comm S T hSF hT φ hφ e
  · let T : FormSpace K K := ⟨Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K,
      fun x _ => quadMinus r K b₀ c₀ x⟩
    have hT : ∀ x y, T.F x y = quadMinus r K b₀ c₀ x := fun _ _ => rfl
    have hnd := nondegenerate_polarBilin_prod hQS
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hirr)
    have htyp : IsPlusType (QS.prod (quadMinus r K b₀ c₀)) ↔ IsPlusType Q := by
      by_cases hp : IsPlusType QS
      · exact ⟨fun h => absurd h (not_isPlusType_prod_quadMinus hQS hSdim hp hr1 hirr),
          fun h => absurd (iff_of_true hp h) hiff⟩
      · have ht1 : 1 ≤ t := by
          by_contra h0
          exact hp (hS0 (by omega))
        refine ⟨fun _ => ?_, fun _ => isPlusType_prod_quadMinus hQS ht1 hSdim hp r hirr⟩
        by_contra hq
        exact hiff (iff_of_false hp hq)
    obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff hnd hQ
      (by rw [Module.finrank_prod, hSdim, finrank_quadMinus_space hr1]; omega) hdim htyp
    exact exists_orthogonal_of_prod_comm S T hSF hT φ hφ e

theorem exists_orthogonal_embedding_dickson {G : Type} [Group G] (S : FormSpace K K)
    {QS : QuadraticForm K S.V} (hSF : ∀ x y, S.F x y = QS x) (hQS : (polarBilin QS).Nondegenerate)
    {t : ℕ} (hSdim : finrank K S.V = 2 * t) (φ : G →* S.isom) (hφ : Function.Injective φ)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {n : ℕ}
    (hdim : finrank K V = 2 * n) (htn : t ≤ n) (htype : t = n → (IsPlusType QS ↔ IsPlusType Q)) :
    ∃ ψ : G →* TauCeti.QuadraticMap.orthogonalGroup Q, Function.Injective ψ ∧
      (CharP K 2 → ∀ g : G, Even (finrank K (commSpace (φ g : S.V ≃ₗ[K] S.V))) →
        (ψ g : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  obtain ⟨ψ, hψ, hD⟩ := exists_orthogonal_embedding_comm S hSF hQS hSdim φ hφ hQ hdim htn htype
  refine ⟨ψ, hψ, fun h2 g hev => ?_⟩
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    ⟨(ψ g).2, by rw [hD g]; exact hev⟩

end Embedding

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
