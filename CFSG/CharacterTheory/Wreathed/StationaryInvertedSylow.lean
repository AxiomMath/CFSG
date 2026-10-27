module

public import CFSG.CharacterTheory.Wreathed.StationaryInvertedSylowSupport
public import CFSG.CharacterTheory.Wreathed.InvertedLocalSylow

public section

namespace CFSG.Wreathed.StationaryInvertedSylow

open scoped Pointwise
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.StationaryScalarCoverage CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.Wreathed.LocalOddCorePerfectNormalizer CFSG.Wreathed.InvertedLocalSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem stationary_factorizations_produce_actual_inverted_sylow_and_cyclic_actor
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (himage : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (H0 : Subgroup G) (hJ0 : J.map (involutionCentralizer n S e).subtype ≤ H0)
    (hfactor : CFSG.oddCore H0 ⊔ (involutionCentralizer n S e).subgroupOf H0 = ⊤)
    (hH0N : ¬ H0 ≤ involutionCentralizer n S e) :
    let s := wreathModelHom S e (Original.s (2 ^ n))
    let t := wreathModelHom S e (Original.t (2 ^ n))
    let z := wreathModelHom S e (Original.z (2 ^ n))
    let x := wreathModelHom S e (Original.x (2 ^ n))
    let y := wreathModelHom S e (Original.x2 (2 ^ n))
    let T := Subgroup.closure ({x, y} : Set G)
    let ι : Subgroup (centralizerOddCore n S e) → Subgroup G := fun P =>
      (P.map (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype
    let Stationary : ℕ → Prop := fun ell => ∃ P₀ : Sylow ell (centralizerOddCore n S e),
      ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (ι P₀ : Set G))),
        ((Q : Subgroup _).map (CFSG.pPrimeCore 2
          (Subgroup.normalizer (ι P₀ : Set G))).subtype).map
            (Subgroup.normalizer (ι P₀ : Set G)).subtype = ι P₀
    let Factorizations : ℕ → Prop := fun ell => ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
      T ≤ Subgroup.normalizer (U : Set G) →
        (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
          (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
          ((Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
            Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G)
    let Wι : (ell : ℕ) → Sylow ell (CFSG.oddCore H0) → Subgroup G := fun _ W =>
      ((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map H0.subtype
    T ≤ H0 →
    (∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) → Stationary ell) →
    (∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) → Factorizations ell) →
    (CFSG.oddCore H0).map H0.subtype ⊓ involutionCentralizer n S e ≤
        (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ∧
    (∃ ell : ℕ, ell.Prime ∧ ell ∣ Nat.card (CFSG.oddCore H0) ∧
      ∃ W : Sylow ell (CFSG.oddCore H0), T ≤ Subgroup.normalizer (Wι ell W : Set G) ∧
        ¬ Wι ell W ≤ involutionCentralizer n S e) ∧
    ∀ ell : ℕ, ell.Prime → ∀ W : Sylow ell (CFSG.oddCore H0),
      T ≤ Subgroup.normalizer (Wι ell W : Set G) → ¬ Wι ell W ≤ involutionCentralizer n S e →
      let E := Wι ell W ⊓ Subgroup.centralizer ({y} : Set G)
      let F := Wι ell W ⊓ Subgroup.centralizer ({x * y} : Set G)
      let A := Subgroup.zpowers (s * t⁻¹)
      let d := y * z
      let K := Subgroup.centralizer (E : Set G)
      (IsMulCommutative (Wι ell W) ∧ ∀ w ∈ Wι ell W, x * w * x⁻¹ = w⁻¹) ∧
      J.map (involutionCentralizer n S e).subtype ≤
        (Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
          (CFSG.oddCore H0).subtype : Subgroup H0) : Set H0)).map H0.subtype ∧
      (E ⊔ F = Wι ell W ∧ E ⊓ F = ⊥) ∧
      (E ≠ ⊥ ∧ F ≠ ⊥) ∧
      (E.map (MulAut.conj d).toMonoidHom = F ∧ F.map (MulAut.conj d).toMonoidHom = E) ∧
      Nat.card (Wι ell W) = Nat.card E ^ 2 ∧
      (IsCyclic A ∧ Nat.card A = 2 ^ n) ∧
      A ≤ J.map (involutionCentralizer n S e).subtype ∧
      A ≤ Subgroup.normalizer (E : Set G) ∧
      (x ∈ A ∧ orderOf x = 2 ∧ ∀ a ∈ A, orderOf a = 2 → a = x) ∧
      (∀ w ∈ E, x * w * x⁻¹ = w⁻¹) ∧
      y ∈ K ∧
      ((∃ D : Subgroup K, D.Normal ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.index = 2 ^ k) ∨
        ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* QuaternionGroup ((2 : ℕ) ^ (n - 1))) ∧
            Nat.card P = 2 * 2 ^ n) ∧
          (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
          CFSG.oddCore K ⊔ (Subgroup.centralizer ({y} : Set G)).subgroupOf K = ⊤)) ∧
      ∀ u ∈ K, Odd (orderOf u) → y * u * y⁻¹ = u⁻¹ →
        u ∈ (CFSG.oddCore K).map K.subtype := by
  intro s t z x y T ι Stationary Factorizations Wι hT0 hst hfac
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTeq : modelT n S e = T := CompatibleFamilies.modelT_eq_closure S e (by omega)
  have : IsKleinFour T := by
    rw [← hTeq]
    exact modelT_isKleinFour n (by omega) S e
  have hxT : x ∈ T := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyT : y ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx2 : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hy2 : orderOf y = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxy : x ≠ y := BrauerWong.modelHom_x_ne_x2 S e (by omega)
  have hx0 : x ∈ H0 := hT0 hxT
  have hloc := localization_of_stationary_factorizations n hn S e hst
    (fun ell hell hdiv U hU hUp hUR hTU => hfac ell hell hdiv U hU hUp hUR (by
      rw [← hTeq]
      exact hTU))
  have hloc' : ∀ ell : ℕ, ell.Prime →
      ell ∣ Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) →
      ∀ F : Subgroup G, F ≠ ⊥ →
        F ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        IsPGroup ell F → T ≤ Subgroup.normalizer (F : Set G) →
        ∀ B : Subgroup G, B ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell B →
          x ∈ Subgroup.normalizer (B : Set G) → B ≤ Subgroup.centralizer ({x} : Set G) :=
    fun ell hell hdiv F hF hFR hFp hTF => hloc ell hell hdiv F hF hFR hFp (by
      rw [hTeq]
      exact hTF)
  have hOnot : ¬ (CFSG.oddCore H0).map H0.subtype ≤ involutionCentralizer n S e :=
    oddCore_not_le_of_factorization H0 _ hfactor hH0N
  have hOne : Nat.card (CFSG.oddCore H0) ≠ 1 := by
    intro h1
    apply hOnot
    rw [Subgroup.card_eq_one.mp h1, Subgroup.map_bot]
    exact bot_le
  obtain ⟨r, hr, hrdiv⟩ := Nat.exists_prime_and_dvd hOne
  obtain ⟨V, hV⟩ := exists_sylow_oddCore_normalized H0 ⟨x, hx0⟩
    (by rw [Subgroup.orderOf_mk]; exact hx2) hr
  have hON := (local_odd_core_factorization_forces_actual_perfect_lift_to_normalize_Sylows
    hnonab n hn S e hfour J himage hcomm H0 hJ0 hx0 hfactor r hr hrdiv V hV).odd_core_intersection
  have hRN : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ≤
      Subgroup.centralizer ({x} : Set G) := Subgroup.map_subtype_le _
  have hTR : T ≤ Subgroup.normalizer
      (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
        Set G) := by
    rw [← hTeq]
    exact (modelT_le_involutionCentralizer n hn S e).trans
      (involutionCentralizer_le_normalizer_oddCore n S e)
  have hOodd : Odd (Nat.card ((CFSG.oddCore H0).map H0.subtype)) := by
    rw [Subgroup.card_map_of_injective H0.subtype_injective]
    exact CFSG.Wreathed.weakClosure_oddCore_card H0
  have hTO : T ≤ Subgroup.normalizer (((CFSG.oddCore H0).map H0.subtype : Subgroup G) :
      Set G) := hT0.trans (le_normalizer_map_oddCore H0)
  obtain ⟨hscalar, hesc⟩ :=
    LocalizedFixedPoints.localized_fixed_points_force_scalar_action_and_an_inverted_sylow
      T x y hxT hyT hx2 hy2 hxy _ hRN (oddCore_map_odd n S e) hTR hloc'
      ((CFSG.oddCore H0).map H0.subtype) hOodd hTO hON
  obtain ⟨⟨ell₀, hell₀, hdivO, Q, hTQ, hQN⟩, -⟩ := hesc hOnot
  obtain ⟨W₀, hW₀⟩ := intrinsic_sylow_from_ambient hell₀ H0 (CFSG.oddCore H0) Q
  refine ⟨hON, ⟨ell₀, hell₀, ?_, W₀, ?_, ?_⟩, ?_⟩
  · rwa [Subgroup.card_map_of_injective H0.subtype_injective] at hdivO
  · change T ≤ Subgroup.normalizer
      ((((W₀ : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map H0.subtype :
        Subgroup G) : Set G)
    rw [hW₀]
    exact hTQ
  · change ¬ ((W₀ : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map
      H0.subtype ≤ involutionCentralizer n S e
    rw [hW₀]
    exact hQN
  intro ell hell W hTW hWN E F A d K
  have : Fact ell.Prime := ⟨hell⟩
  have hWne : Wι ell W ≠ ⊥ := fun h => hWN (h ▸ bot_le)
  have hcardW : Nat.card (Wι ell W) = Nat.card (W : Subgroup (CFSG.oddCore H0)) := by
    change Nat.card (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype).map
      H0.subtype) = _
    rw [Subgroup.card_map_of_injective H0.subtype_injective,
      Subgroup.card_map_of_injective (CFSG.oddCore H0).subtype_injective]
  have hdiv : ell ∣ Nat.card (CFSG.oddCore H0) := by
    have h1 : ell ∣ Nat.card (W : Subgroup (CFSG.oddCore H0)) := by
      rcases W.isPGroup'.card_eq_or_dvd with h | h
      · exfalso
        apply hWne
        rw [← Subgroup.card_eq_one, hcardW, h]
      · exact h
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  have hellodd : Odd ell := (CFSG.Wreathed.weakClosure_oddCore_card H0).of_dvd_nat hdiv
  have hWO : Wι ell W ≤ (CFSG.oddCore H0).map H0.subtype :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hWp : IsPGroup ell (Wι ell W) := (W.isPGroup'.map _).map _
  obtain ⟨hcase, hnot⟩ := hscalar ell hell hellodd (Wι ell W) hWO hWp hTW
  have hinv : ∀ w ∈ Wι ell W, x * w * x⁻¹ = w⁻¹ := hcase.resolve_left hWN
  have hab : IsMulCommutative (Wι ell W) := (hnot hWN).2
  have hxW : (⟨x, hx0⟩ : H0) ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype : Subgroup H0) :
        Set H0) :=
    mem_normalizer_of_map_subtype _ _ (hTW hxT)
  have hJW := (local_odd_core_factorization_forces_actual_perfect_lift_to_normalize_Sylows
    hnonab n hn S e hfour J himage hcomm H0 hJ0 hx0 hfactor ell hell hdiv W
      hxW).perfect_lift_normalizes
  obtain ⟨-, hEF, hEFne, hconj, hcardE, hA, hAJ, hAE, hAx, hxE, hyK, halt, hKinv⟩ :=
    inverted_local_sylow_has_actual_cyclic_actor_and_controlled_eigensubgroup_centralizer
      hnonab n hn S e hfour J himage hcomm H0 hJ0 hfactor ell hell hdiv W hT0 hTW hinv
  exact ⟨⟨hab, hinv⟩, hJW, hEF, hEFne, hconj, hcardE, hA, hAJ, hAE, hAx, hxE, hyK, halt, hKinv⟩

end CFSG.Wreathed.StationaryInvertedSylow
