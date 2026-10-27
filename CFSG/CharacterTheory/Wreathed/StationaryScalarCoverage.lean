module

public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverageLocal

public section

namespace CFSG.Wreathed.StationaryScalarCoverage

open scoped Pointwise
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open CFSG.Wreathed.OriginalScalarSylowCoverage

universe u

variable {G : Type u} [Group G]

theorem mem_normalizer_of_map_subtype {N : Subgroup G} (K : Subgroup N) (v : N)
    (h : (v : G) ∈ Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G)) :
    v ∈ Subgroup.normalizer (K : Set N) := by
  have hcomap : (Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G)).comap N.subtype =
      Subgroup.normalizer ((K.map N.subtype).comap N.subtype : Set N) :=
    Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range N.subtype K)
  rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at hcomap
  rw [← hcomap]
  exact h

theorem isMulCommutative_of_inverted {N : Subgroup G} {R : Subgroup N} (P : Subgroup R) (t : G)
    (hinv : ∀ a ∈ (P.map R.subtype).map N.subtype, t * a * t⁻¹ = a⁻¹) : IsMulCommutative P := by
  have hab := abelian_of_inverted t _ hinv
  have hmem : ∀ c : P, (((c : R) : N) : G) ∈ (P.map R.subtype).map N.subtype := fun c =>
    Subgroup.mem_map_of_mem N.subtype (Subgroup.mem_map_of_mem R.subtype c.2)
  constructor
  constructor
  intro a b
  have h := hab.is_comm.comm ⟨_, hmem a⟩ ⟨_, hmem b⟩
  have h0 := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h0

theorem scalar_abelian_coverage_of_stationary_factorizations
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    {ell : ℕ} (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e))
    (hst : ∃ P₀ : Sylow ell (centralizerOddCore n S e),
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
    (hfactor : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup ell U →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
      modelT n S e ≤ Subgroup.normalizer (U : Set G) →
        (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
          (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
          ((Subgroup.normalizer (U : Set G) ⊓
            Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :
              Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G))
    (P : Sylow ell (centralizerOddCore n S e))
    (hTP : modelT n S e ≤ Subgroup.normalizer
      ((((P : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
        (involutionCentralizer n S e).subtype : Subgroup G) : Set G)) :
    ((∀ a ∈ ((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype,
        wreathModelHom S e (Original.x2 (2 ^ n)) * a *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = a) ∨
      (∀ a ∈ ((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype,
        wreathModelHom S e (Original.x2 (2 ^ n)) * a *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = a⁻¹)) ∧
    ((∀ a ∈ ((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype,
        wreathModelHom S e (Original.x2 (2 ^ n)) * a *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = a⁻¹) →
      IsMulCommutative (P : Subgroup (centralizerOddCore n S e))) ∧
    (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
      (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
        (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) := by
  have : Fact ell.Prime := ⟨hell⟩
  have hRodd : Odd (Nat.card (centralizerOddCore n S e)) := weakClosure_oddCore_card _
  have hellodd : Odd ell := hRodd.of_dvd_nat hdiv
  obtain ⟨P₀, hst₀⟩ := hst
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (centralizerOddCore n S e) P₀ P
  have hPeq : (((P₀ : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype).map
        (MulAut.conj ((r : involutionCentralizer n S e) : G)).toMonoidHom =
      ((P : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
        (involutionCentralizer n S e).subtype := by
    rw [← hr, map_subtype_smul_sylow, map_conj_map_subtype]
  have hstP := stationary_of_map_conj hell _ _ _ hPeq hst₀
  have hPR : ((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype ≤
        (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hPp : IsPGroup ell (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype) :=
    (P.isPGroup'.map _).map _
  have hscalar := scalar_of_stationary_factorizations hnonab n hn S e hell hellodd _ hPR hPp
    hTP hstP hfactor
  refine ⟨hscalar, fun hinv => isMulCommutative_of_inverted _ _ hinv, ?_⟩
  have hyT : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ modelT n S e := by
    rw [CompatibleFamilies.modelT_eq_closure S e (by omega)]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hyN : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ involutionCentralizer n S e :=
    modelT_le_involutionCentralizer n hn S e hyT
  let v : involutionCentralizer n S e := ⟨_, hyN⟩
  have hv : orderOf v = 2 := by
    rw [Subgroup.orderOf_mk]
    exact CompatibleFamilies.orderOf_x2 S e hn
  have hne : v ≠ centralInvolution n S e := fun h =>
    modelHom_x_ne_x2 S e (by omega) (congrArg Subtype.val h).symm
  have hnormalizes : v ∈ Subgroup.normalizer (((P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) :=
    mem_normalizer_of_map_subtype _ v (hTP hyT)
  have hscalarN : (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a) ∨
      (∀ a ∈ (P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype, v * a * v⁻¹ = a⁻¹) := by
    rcases hscalar with h | h
    · exact Or.inl fun a ha => Subtype.ext
        (h a (Subgroup.mem_map_of_mem (involutionCentralizer n S e).subtype ha))
    · exact Or.inr fun a ha => Subtype.ext
        (h a (Subgroup.mem_map_of_mem (involutionCentralizer n S e).subtype ha))
  exact original_scalar_Sylow_action_gives_primewise_layer_coverage hnonab n hn S e hfour hell
    hdiv P v hv hne hnormalizes hscalarN

variable [Finite G]

theorem stationary_normalizer_factorizations_give_original_scalar_sylows_and_coverage
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4))) :
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
    (∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      Stationary ell → Factorizations ell →
      ∀ P : Sylow ell (centralizerOddCore n S e), T ≤ Subgroup.normalizer (ι P : Set G) →
        ((∀ a ∈ ι P, y * a * y⁻¹ = a) ∨ (∀ a ∈ ι P, y * a * y⁻¹ = a⁻¹)) ∧
        ((∀ a ∈ ι P, y * a * y⁻¹ = a⁻¹) →
          IsMulCommutative (P : Subgroup (centralizerOddCore n S e))) ∧
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
          (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
            (centralizerOddCoreMap n S e)).map (centralizerOddCoreMap n S e) =
              CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
    ((∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
        Stationary ell ∧ Factorizations ell) →
      ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
        ∃ P : Sylow ell (centralizerOddCore n S e),
          (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
            (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
              (centralizerOddCoreMap n S e)).map (centralizerOddCoreMap n S e) =
                CFSG.layer (centralizerOddCoreQuotient n S e)) := by
  intro x y T ι Stationary Factorizations
  have hTeq : modelT n S e = T := CompatibleFamilies.modelT_eq_closure S e (by omega)
  refine ⟨fun ell hell hdiv hst hfac P hTP => ?_, fun hall ell hell hdiv => ?_⟩
  · exact scalar_abelian_coverage_of_stationary_factorizations hnonab n hn S e hfour hell hdiv
      hst (fun U hU1 hUp hUR hTU => hfac U hU1 hUp hUR (hTeq ▸ hTU)) P (hTeq ▸ hTP)
  · obtain ⟨hst, hfac⟩ := hall ell hell hdiv
    obtain ⟨P, hTP⟩ := exists_invariant_sylow_centralizerOddCore n hn S e hell
    exact ⟨P, (scalar_abelian_coverage_of_stationary_factorizations hnonab n hn S e hfour hell
      hdiv hst (fun U hU1 hUp hUR hTU => hfac U hU1 hUp hUR (hTeq ▸ hTU)) P hTP).2.2⟩

end CFSG.Wreathed.StationaryScalarCoverage
