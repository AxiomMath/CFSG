module

public import CFSG.LieType.AlgebraicGroups.SemisimpleFixedCoordinatesThree
public import CFSG.LieType.AlgebraicGroups.NilpotentSemisimple

public noncomputable section

open WithConv
open scoped commutatorElement

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)

omit [IsAlgClosed k] in
theorem exists_fixedCoordinate_point_of_fixed (g : RationalGroup H)
    (hg : TauCeti.AlgHom.mapDomain σ g = g) :
    ∃ x : RationalGroup (fixedCoordinate H σ), TauCeti.AlgHom.mapDomain
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom x = g := by
  have hker : ∀ h : H.obj, h ∈ fixedHopfIdeal H σ → g.ofConv h = 0 := by
    intro h hh
    have hle : (fixedHopfIdeal H σ).toIdeal ≤ RingHom.ker g.ofConv := by
      rw [fixedHopfIdeal, TauCeti.HopfIdeal.equalizer_toIdeal]
      refine TauCeti.HopfIdeal.equalizerIdeal_le_iff.2 fun a => ?_
      rw [RingHom.mem_ker, map_sub, BialgHom.id_apply, sub_eq_zero]
      have h1 := congrArg (fun p : RationalGroup H => p.ofConv a) hg
      simpa only [TauCeti.AlgHom.mapDomain_apply_apply] using h1
    exact hle (TauCeti.HopfIdeal.mem_toIdeal.mpr hh)
  exact ⟨TauCeti.CommHopfAlgCat.liftQuotientPoint H.obj (fixedHopfIdeal H σ)
      (CommAlgCat.of k k) g hker,
    TauCeti.CommHopfAlgCat.quotientPointsHom_liftQuotientPoint H.obj (fixedHopfIdeal H σ)
      (CommAlgCat.of k k) g hker⟩

theorem fixedBorel_le_of_isBorelCandidate_of_bruhat
    (B : TauCeti.HopfIdeal k H) (T U : Subgroup (RationalGroup H))
    (V : RationalGroup H → Set (RationalGroup H))
    (hB : TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) = T ⊔ U)
    (hT : ∀ t ∈ T, TauCeti.HopfAlgebra.IsSemisimplePoint t)
    (hVU : ∀ n, V n ⊆ U)
    (hU : ∀ u ∈ U, TauCeti.AlgHom.mapDomain σ u ∈ U)
    (hN : ∀ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)),
      TauCeti.AlgHom.mapDomain σ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)))
    (hV : ∀ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)), ∀ v ∈ V n,
      TauCeti.AlgHom.mapDomain σ v ∈ V (TauCeti.AlgHom.mapDomain σ n))
    (hcover : ∀ g : RationalGroup H, ∃ u ∈ U,
      ∃ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)), ∃ v ∈ V n, g = u * n * v)
    (hunique : ∀ u ∈ U, ∀ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)), ∀ v ∈ V n,
      ∀ u' ∈ U, ∀ n' ∈ Subgroup.normalizer (T : Set (RationalGroup H)), ∀ v' ∈ V n',
      u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v')
    (hreg : ∀ n ∈ Subgroup.normalizer (T : Set (RationalGroup H)) ⊓
        TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain σ),
      (∀ s ∈ T ⊓ TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain σ), Commute n s) → n ∈ T)
    (J : TauCeti.HopfIdeal k (fixedCoordinate H σ))
    (hJ : TauCeti.HopfIdeal.IsBorelCandidate k (fixedCoordinate H σ) J)
    (hJB : J ≤ B.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom) :
    B.map (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom ≤ J := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  let F := fixedCoordinate H σ
  let ι := TauCeti.AlgHom.mapDomain (A := k) q
  have hcJ := (TauCeti.HopfIdeal.isBorelCandidate_iff k F J).mp hJ
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient F J
  have : Algebra.Smooth k Q := (TauCeti.smoothCommHopfAlgProperty_iff _).mp hcJ.1
  have : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  have hmemB : ∀ x : RationalGroup F, ι x ∈ T ⊔ U → x ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj (B.map q) (CommAlgCat.of k k) := by
    intro x hx
    refine (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_map_mkQuotient_iff H.obj
      (fixedHopfIdeal H σ) B (CommAlgCat.of k k) x).mpr ?_
    rw [hB]
    exact hx
  have hBJ := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le F.obj hJB (CommAlgCat.of k k)
  have hfixJ : ∀ y : RationalGroup H, TauCeti.AlgHom.mapDomain σ y = y → y ∈ T ⊔ U →
      ∃ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj J (CommAlgCat.of k k), ι x = y := by
    intro y hy hyB
    obtain ⟨x, rfl⟩ := exists_fixedCoordinate_point_of_fixed H σ y hy
    exact ⟨x, hBJ (hmemB x hyB), rfl⟩
  apply TauCeti.HopfIdeal.le_of_quotientPointsSubgroup_le (K := k)
  intro g hg
  apply hmemB
  have hgfix : TauCeti.AlgHom.mapDomain σ (ι g) = ι g := fixedCoordinate_point_fixed H σ g
  obtain ⟨u, hu, hfu, n, hn, hfn, v, hv, hfv, hgnv⟩ :=
    exists_fixed_bruhat_factors (TauCeti.AlgHom.mapDomain σ) U
      (Subgroup.normalizer (T : Set (RationalGroup H))) V hU hN hV hcover hunique hgfix
  obtain ⟨uF, huJ, rfl⟩ := hfixJ u hfu (Subgroup.mem_sup_right hu)
  obtain ⟨vF, hvJ, rfl⟩ := hfixJ v hfv (Subgroup.mem_sup_right (hVU n hv))
  let nF := uF⁻¹ * g * vF⁻¹
  have hnJ : nF ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup F.obj J (CommAlgCat.of k k) :=
    mul_mem (mul_mem (inv_mem huJ) hg) (inv_mem hvJ)
  have hιn : ι nF = n := by
    simp only [nF, map_mul, map_inv, hgnv]
    group
  have hcomm : ∀ s ∈ T ⊓ TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain σ), Commute n s := by
    rintro s ⟨hsT, hsfix⟩
    obtain ⟨sF, hsJ, rfl⟩ :=
      hfixJ s (TauCeti.mem_fixedSubgroup.mp hsfix) (Subgroup.mem_sup_left hsT)
    have hnker := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hnJ
    have hsker := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hsJ
    let nQ : WithConv (Q →ₐ[k] k) :=
      TauCeti.CommHopfAlgCat.liftQuotientPoint F.obj J (CommAlgCat.of k k) nF hnker
    let sQ : WithConv (Q →ₐ[k] k) :=
      TauCeti.CommHopfAlgCat.liftQuotientPoint F.obj J (CommAlgCat.of k k) sF hsker
    have hQ : TauCeti.HopfAlgebra.IsUnipotentPoint ⁅nQ, sQ⁆ :=
      NilpotentSemisimple.isUnipotentPoint_commutator_of_solvable Q hcJ.2.1 hcJ.2.2 nQ sQ
    have hnQ : TauCeti.AlgHom.mapDomain (A := k)
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient F J).hom.hom nQ = nF :=
      TauCeti.CommHopfAlgCat.quotientPointsHom_liftQuotientPoint F.obj J (CommAlgCat.of k k) nF hnker
    have hsQ : TauCeti.AlgHom.mapDomain (A := k)
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient F J).hom.hom sQ = sF :=
      TauCeti.CommHopfAlgCat.quotientPointsHom_liftQuotientPoint F.obj J (CommAlgCat.of k k) sF hsker
    have hunip : TauCeti.HopfAlgebra.IsUnipotentPoint ⁅n, ι sF⁆ := by
      have h := (hQ.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient F J).hom.hom).mapDomain q
      rwa [map_commutatorElement, map_commutatorElement, hnQ, hsQ, hιn] at h
    have hmemT : ⁅n, ι sF⁆ ∈ T := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp hn _).mp hsT) (inv_mem hsT)
    have hone : ⁅n, ι sF⁆ = 1 := by
      calc ⁅n, ι sF⁆ = TauCeti.HopfAlgebra.Point.semisimplePart k H k ⁅n, ι sF⁆ :=
            (TauCeti.HopfAlgebra.Point.semisimplePart_eq_self k H k
              ((TauCeti.HopfAlgebra.isSemisimplePoint_def _).mp (hT _ hmemT))).symm
        _ = 1 := TauCeti.HopfAlgebra.Point.semisimplePart_eq_one_of_isUnipotent k H k hunip
    exact commutatorElement_eq_one_iff_commute.mp hone
  have hnT : n ∈ T := hreg n ⟨hn, TauCeti.mem_fixedSubgroup.mpr hfn⟩ hcomm
  rw [hgnv]
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hnT))
    (Subgroup.mem_sup_right (hVU n hv))

namespace StableTriangularCoordinates

variable {H σ}
variable (D : StableTriangularCoordinates H σ)

theorem fixedPositiveBorel_le_of_isBorelCandidate
    (hreg : ∀ n ∈ D.normalizer ⊓ D.fixed, (∀ s ∈ D.torus ⊓ D.fixed, Commute n s) → n ∈ D.torus)
    (J : TauCeti.HopfIdeal k (fixedCoordinate H σ))
    (hJ : TauCeti.HopfIdeal.IsBorelCandidate k (fixedCoordinate H σ) J)
    (hJB : J ≤ D.fixedPositiveBorel) : D.fixedPositiveBorel ≤ J :=
  D.fixedPositiveBorel_eq ▸ fixedBorel_le_of_isBorelCandidate_of_bruhat H σ D.positiveBorel D.torus D.positiveGroup
    D.inversion D.positiveBorelPoints D.torus_points_semisimple D.inversionPositive
    D.positiveStable D.normalizerStable D.inversionStable D.bruhatCover D.bruhatUnique hreg J hJ
    (D.fixedPositiveBorel_eq ▸ hJB)

theorem fixedNegativeBorel_le_of_isBorelCandidate
    (hreg : ∀ n ∈ D.normalizer ⊓ D.fixed, (∀ s ∈ D.torus ⊓ D.fixed, Commute n s) → n ∈ D.torus)
    (hcover : ∀ g : RationalGroup H, ∃ u ∈ D.negativeGroup, ∃ n ∈ D.normalizer,
      ∃ v ∈ D.negativeGroup, n * v * n⁻¹ ∈ D.positiveGroup ∧ g = u * n * v)
    (hunique : ∀ u ∈ D.negativeGroup, ∀ n ∈ D.normalizer, ∀ v ∈ D.negativeGroup,
      n * v * n⁻¹ ∈ D.positiveGroup → ∀ u' ∈ D.negativeGroup, ∀ n' ∈ D.normalizer,
      ∀ v' ∈ D.negativeGroup, n' * v' * n'⁻¹ ∈ D.positiveGroup →
      u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v')
    (J : TauCeti.HopfIdeal k (fixedCoordinate H σ))
    (hJ : TauCeti.HopfIdeal.IsBorelCandidate k (fixedCoordinate H σ) J)
    (hJB : J ≤ D.fixedNegativeBorel) : D.fixedNegativeBorel ≤ J := by
  rw [D.fixedNegativeBorel_eq]
  let V : RationalGroup H → Set (RationalGroup H) :=
    fun n => {v | v ∈ D.negativeGroup ∧ n * v * n⁻¹ ∈ D.positiveGroup}
  refine fixedBorel_le_of_isBorelCandidate_of_bruhat H σ D.negativeBorel D.torus D.negativeGroup V
    D.negativeBorelPoints D.torus_points_semisimple (fun n v hv => hv.1) D.negative_stable
    D.normalizerStable ?_ ?_ ?_ hreg J hJ (D.fixedNegativeBorel_eq ▸ hJB)
  · intro n _ v hv
    refine ⟨D.negative_stable v hv.1, ?_⟩
    have h := D.positiveStable _ hv.2
    simpa only [map_mul, map_inv] using h
  · intro g
    obtain ⟨u, hu, n, hn, v, hv, hnv, rfl⟩ := hcover g
    exact ⟨u, hu, n, hn, v, ⟨hv, hnv⟩, rfl⟩
  · intro u hu n hn v hv u' hu' n' hn' v' hv' h
    exact hunique u hu n hn v hv.1 hv.2 u' hu' n' hn' v' hv'.1 hv'.2 h

end StableTriangularCoordinates

end CFSG.LieType.AlgebraicGroups
