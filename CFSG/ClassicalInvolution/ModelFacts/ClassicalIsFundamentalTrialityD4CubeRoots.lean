module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeTriple

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Triple

variable (p e : ℕ) [Fact p.Prime]

theorem map_rootGroup_le_rootSubgroup_d4 (k : Type) [Field k]
    [Algebra (GaloisField p (3 * e)) k] {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    (rootGroup (rootOperatorFamily d4) (GaloisField p (3 * e)) γ).map
        ((baseChangeGL (algebraMap (GaloisField p (3 * e)) k)).comp
          (adjointGroup d4 (GaloisField p (3 * e))).subtype) ≤ rootSubgroup d4 k γ := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  change baseChangeGL (algebraMap (GaloisField p (3 * e)) k)
    ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 (GaloisField p (3 * e))) :
      ModGL d4 (GaloisField p (3 * e))) ∈ _
  rw [coe_xPar_d4 hγ, baseChangeGL_pinnedX]
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

theorem tripleGroup_le_adjointGroup (k : Type) [Field k] (β : Fin d4.rank → ℤ) :
    tripleGroup k β ≤ adjointGroup d4 k :=
  sup_le (sup_le (rootSubgroup_le_adjointGroup β) (rootSubgroup_le_adjointGroup _))
    (rootSubgroup_le_adjointGroup _)

theorem map_twistedRootGroup_orbit_d4 (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) (hne : rho β ≠ β) :
    (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β)).map
        (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
      fixedPointsIn (tripleGroup (AlgebraicClosure (GaloisField p (3 * e))) β)
        (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
          (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  set σ := iterateFrobenius K0 p e with hσdef
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have hσ3 : ∀ c, σ (σ (σ c)) = c := sigma_cube_frobenius p e he
  set F := frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) with hF
  set Φ := trialityD4Phi p e k with hΦ
  have hΦR : ∀ g, Φ g ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F := fun g =>
    trialityD4Phi_mem_fixedPointsIn p e hp2 he g
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.D4.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)
  set S := fixedPointsIn (tripleGroup k β) F with hS
  have hSle : S ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F :=
    inf_le_inf_right _ (tripleGroup_le_adjointGroup k β)
  have hSfin : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSle)
  set T := (twistedRootGroup σ (proj β)).map Φ with hT
  set Ψ : adjointGroup d4 K0 →* ModGL d4 k :=
    (baseChangeGL (algebraMap K0 k)).comp (adjointGroup d4 K0).subtype with hΨ
  have h1 := isRoot_rho hβ
  have h2 := isRoot_rho h1
  have hΨle : (rootGroup (rootOperatorFamily d4) K0 β ⊔
      rootGroup (rootOperatorFamily d4) K0 (rho β) ⊔
      rootGroup (rootOperatorFamily d4) K0 (rho (rho β))).map Ψ ≤ tripleGroup k β := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le_sup (sup_le_sup (map_rootGroup_le_rootSubgroup_d4 p e k hβ)
      (map_rootGroup_le_rootSubgroup_d4 p e k h1)) (map_rootGroup_le_rootSubgroup_d4 p e k h2)
  have hTS : T ≤ S := by
    rintro _ ⟨g, hg, rfl⟩
    have hgmem : (g : adjointGroup d4 K0) ∈ twistedRootSubgroupD4 σ (proj β) :=
      (mem_twistedRootGroup (σ := σ)).1 hg
    have h3 := twistedRootSubgroupD4_le σ hβ rfl hgmem
    refine mem_fixedPointsIn.2 ⟨hΨle ⟨_, h3, rfl⟩, (mem_fixedPointsIn.1 (hΦR g)).2⟩
  have hTfin : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hTS)
  have hSq : Nat.card S ≤ (p ^ e) ^ 3 := card_fixedPointsIn_tripleGroup_le p he hβ hne
  have hK3 : Nat.card K0 = (p ^ e) ^ 3 := card_galoisField_three_mul p e he
  let x : K0 → twistedGroup σ := fun c =>
    ⟨xOrbit σ β c, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hβ)
      (xOrbit_mem hσ3 hβ hne c)⟩
  have hxmem : ∀ c, x c ∈ twistedRootGroup σ (proj β) := fun c =>
    (mem_twistedRootGroup (σ := σ)).2 (xOrbit_mem hσ3 hβ hne c)
  let ψ : K0 → T := fun c => ⟨Φ (x c), Subgroup.mem_map_of_mem _ (hxmem c)⟩
  have hψ : Function.Injective ψ := by
    intro c c' h
    have h4 : Φ (x c) = Φ (x c') := congrArg Subtype.val h
    have h5 := trialityD4Phi_injective p e k h4
    exact xOrbit_injective σ hβ hne (congrArg Subtype.val h5)
  have hcard : (p ^ e) ^ 3 ≤ Nat.card T := by
    rw [← hK3]
    exact Nat.card_le_card_of_injective _ hψ
  exact Subgroup.eq_of_le_of_card_ge hTS (hSq.trans hcard)

theorem map_twistedRootGroup_sup_orbit_d4 (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) (hne : rho β ≠ β) :
    (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β) ⊔
        twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (-proj β)).map
          (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
      fixedPointsIn (tripleGroup (AlgebraicClosure (GaloisField p (3 * e))) β)
          (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
            (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) ⊔
        fixedPointsIn (tripleGroup (AlgebraicClosure (GaloisField p (3 * e))) (-β))
          (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
            (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) := by
  rw [Subgroup.map_sup, map_twistedRootGroup_orbit_d4 p e hp2 he hβ hne, ← map_neg proj β,
    map_twistedRootGroup_orbit_d4 p e hp2 he (IsRoot.neg hβ) (rho_neg_ne hne)]

end Triple

end CFSG.ClassicalInvolution.ModelFacts
