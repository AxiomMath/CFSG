module

public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverageLocal

public section

namespace CFSG.Wreathed.StationaryInvertedSylow

open scoped Pointwise
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.StationaryScalarCoverage CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.Wreathed.StationaryNormalizerCentralization

universe u

variable {G : Type u} [Group G]

theorem oddCore_not_le_of_factorization (H0 N : Subgroup G)
    (hfactor : CFSG.oddCore H0 ⊔ N.subgroupOf H0 = ⊤) (hH0N : ¬ H0 ≤ N) :
    ¬ (CFSG.oddCore H0).map H0.subtype ≤ N := by
  intro hO
  apply hH0N
  intro h hh
  have hmem : (⟨h, hh⟩ : H0) ∈ CFSG.oddCore H0 ⊔ N.subgroupOf H0 := hfactor ▸ Subgroup.mem_top _
  obtain ⟨o, ho, c, hc, hoc⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have h1 : (o : G) ∈ N := hO ⟨o, ho, rfl⟩
  have h2 : (c : G) ∈ N := hc
  have hh' : h = (o : G) * (c : G) := by
    rw [← Subgroup.coe_mul, hoc]
  rw [hh']
  exact N.mul_mem h1 h2

variable [Finite G]

theorem le_normalizer_map_oddCore (H0 : Subgroup G) :
    H0 ≤ Subgroup.normalizer (((CFSG.oddCore H0).map H0.subtype : Subgroup G) : Set G) := by
  have := BaseFourCentralizerStructure.oddCore_characteristic (G := H0)
  exact CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized H0 H0
    H0.le_normalizer (CFSG.oddCore H0)

theorem exists_sylow_oddCore_normalized (H0 : Subgroup G) (v : H0) (hv : orderOf v = 2)
    {r : ℕ} (hr : r.Prime) :
    ∃ V : Sylow r (CFSG.oddCore H0), v ∈ Subgroup.normalizer
      (((V : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype : Subgroup H0) :
        Set H0) := by
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  have hnorm : Subgroup.zpowers v ≤ Subgroup.normalizer ((CFSG.oddCore H0 : Subgroup H0) :
      Set H0) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨V, hV⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 2 r
    Nat.prime_two hr (Subgroup.zpowers v) (CFSG.oddCore H0) hv2 hnorm
    (CFSG.Wreathed.weakClosure_oddCore_card H0).coprime_two_left
  exact ⟨V, hV (Subgroup.mem_zpowers v)⟩

theorem localization_of_stationary_factorizations (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hst : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P₀ : Sylow ell (centralizerOddCore n S e),
      ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P₀ : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
          (involutionCentralizer n S e).subtype : Subgroup G) : Set G))),
        ((Q : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
          ((((P₀ : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype).map
              (involutionCentralizer n S e).subtype : Subgroup G) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P₀ : Subgroup (centralizerOddCore n S e)).map
              (centralizerOddCore n S e).subtype).map
                (involutionCentralizer n S e).subtype : Subgroup G) : Set G)).subtype =
          ((P₀ : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
            (involutionCentralizer n S e).subtype)
    (hfac : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
      modelT n S e ≤ Subgroup.normalizer (U : Set G) →
        (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
          (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
          ((Subgroup.normalizer (U : Set G) ⊓
            Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :
              Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G)) :
    ∀ ell : ℕ, ell.Prime →
      ell ∣ Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) →
      ∀ F : Subgroup G, F ≠ ⊥ →
        F ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        IsPGroup ell F → modelT n S e ≤ Subgroup.normalizer (F : Set G) →
        ∀ B : Subgroup G, B ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell B →
          wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.normalizer (B : Set G) →
          B ≤ Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) := by
  intro ell hell hdivR F hF hFR hFp hTF B hBN hBp hxB
  have : Fact ell.Prime := ⟨hell⟩
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  set N := involutionCentralizer n S e with hNdef
  set R := centralizerOddCore n S e with hRdef
  set T := modelT n S e with hTdef
  have : IsKleinFour T := modelT_isKleinFour n (by omega) S e
  have hTeq : T = Subgroup.closure {x, y} := CompatibleFamilies.modelT_eq_closure S e (by omega)
  have hxT : x ∈ T := by
    rw [hTeq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : y ∈ T := by
    rw [hTeq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx2 : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hy2 : orderOf y = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxy : x ≠ y := BrauerWong.modelHom_x_ne_x2 S e (by omega)
  have hdivR' : ell ∣ Nat.card R := by
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at hdivR
  have hRodd : Odd (Nat.card (R.map N.subtype)) := oddCore_map_odd n S e
  have hellodd : Odd ell := hRodd.of_dvd_nat hdivR
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hTR : T ≤ Subgroup.normalizer ((R.map N.subtype : Subgroup G) : Set G) :=
    (modelT_le_involutionCentralizer n hn S e).trans
      (involutionCentralizer_le_normalizer_oddCore n S e)
  obtain ⟨Q, hFQ, hTQ⟩ := exists_invariant_sylow_containing hell T (R.map N.subtype) F hT2
    hRodd hTR hFR hFp hTF
  obtain ⟨P, hP⟩ := intrinsic_sylow_from_ambient hell N R Q
  obtain ⟨P₀, hst₀⟩ := hst ell hell hdivR'
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R P₀ P
  have hPeq : (((P₀ : Subgroup R).map R.subtype).map N.subtype).map
      (MulAut.conj ((r : N) : G)).toMonoidHom = ((P : Subgroup R).map R.subtype).map N.subtype := by
    rw [← hr, map_subtype_smul_sylow, map_conj_map_subtype]
  have hstP := stationary_of_map_conj hell _ _ _ hPeq hst₀
  have hPR : ((P : Subgroup R).map R.subtype).map N.subtype ≤ R.map N.subtype :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hPp : IsPGroup ell (((P : Subgroup R).map R.subtype).map N.subtype) :=
    (P.isPGroup'.map _).map _
  have hTP : T ≤ Subgroup.normalizer
      ((((P : Subgroup R).map R.subtype).map N.subtype : Subgroup G) : Set G) := by
    rw [hP]
    exact hTQ
  have hPx : ((P : Subgroup R).map R.subtype).map N.subtype ≤
      Subgroup.centralizer ({x} : Set G) := hPR.trans (Subgroup.map_subtype_le _)
  have hloc :=
    (stationary_normalizer_factorizations_force_local_prime_centralization
      T x y hxT hyT hx2 hy2 hxy hell hellodd _ hPp hTP hPx hstP
      (fun U hU hUP hTU => hfac ell hell hdivR' U hU (hPp.to_le hUP) (hUP.trans hPR) hTU)).2
  have hFP : F ≤ ((P : Subgroup R).map R.subtype).map N.subtype := by
    rw [hP]
    exact hFQ
  exact hloc F hF hFP hTF B hBN hBp hxB

end CFSG.Wreathed.StationaryInvertedSylow
