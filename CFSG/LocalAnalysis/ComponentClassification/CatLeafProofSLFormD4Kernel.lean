module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Twist
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddRational
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ClassicalInvolution.ModelFacts Matrix
open scoped MatrixGroups

@[expose] def d4Decomp0 : List (ℕ × ℕ × ℕ) :=
  [(5, 0, 2), (7, 1, 2), (9, 2, 3), (12, 0, 7), (13, 0, 9), (15, 1, 9), (19, 0, 15), (22, 2, 19)]

theorem d4_decomp0 : decompCheck d4Certificate d4Splus0 d4Delta0 d4Decomp0 = true := by
  decide +kernel

@[expose] def d4FundRoot (i : Fin 4) : Fin (Tag.rank .D4) → ℤ :=
  Pi.single (show Fin (Tag.rank .D4) from i) 1

theorem simpleUnion_d4_zero :
    simpleUnion (signMaskChar .D4 0) = Set.range d4FundRoot := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck d4Certificate_check d4_splus0 d4_delta0 d4_decomp0]
  have h1 : ∀ d ∈ d4Delta0, ∃ i, d4FundRoot i = d4Certificate.root d := by decide +kernel
  have h2 : ∀ i, ∃ d ∈ d4Delta0, d4Certificate.root d = d4FundRoot i := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨i, rfl⟩
    exact h2 i

theorem d4_simple_inter_zero
    {χ : Multiplicative (Fin (Tag.rank .D4) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .D4 0)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range d4FundRoot := by
  subst hχ
  exact inter_componentRoots_of_parent d4FundRoot simpleUnion_d4_zero ![2, 2, 2, 2] 2
    (by decide) 1 (by decide) i

theorem thetaMap_d4_nil_alpha3 :
    thetaMap (ToralSign.wordElt .D4 []) TwistTag.D4.perm (d4FundRoot 2) = d4FundRoot 2 := by
  unfold thetaMap
  rw [wordElt_nil, one_smul]
  funext j
  change d4FundRoot 2 (TwistTag.D4.perm.symm j) = d4FundRoot 2 j
  have h : ∀ i : Fin 4, (Pi.single 2 1 : Fin 4 → ℤ)
      ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 3).symm i) = (Pi.single 2 1 : Fin 4 → ℤ) i := by
    decide
  exact h j

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem d4_zero_datum_classes
    (D : OrthogonalSemilinearFixedRootDatum .D4 p k) (hχ : D.χ = signMaskChar .D4 0)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .D4 []) TwistTag.D4.perm γ)) :
    D.θ (toReal (d4FundRoot 2)) = toReal (d4FundRoot 2) ∧
      ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
        (D.withOrbit J').simpleRootsJ = Set.range d4FundRoot := by
  refine ⟨by rw [hθ, thetaMap_d4_nil_alpha3], fun J' hq => ?_⟩
  have hS : simpleUnion D.χ = Set.range d4FundRoot := by
    rw [hχ]
    exact simpleUnion_d4_zero
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hS (d4_simple_inter_zero hχ) with h0 | h
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact h

theorem d4_four_orbitGroup_mulEquiv_SL
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k)
    (hχ : D.χ = signMaskChar TwistTag.D4.tag 4) {ω : WeylGroup TwistTag.D4.tag}
    (hθ : ThetaProperties TwistTag.D4.perm 3 D.χ ω)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap ω TwistTag.D4.perm γ))
    (J' : Set.range D.classOrbit) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), (Nat.card F = D.q ∨ Nat.card F = D.q ^ 3) ∧
      Nonempty ((D.withOrbit J').orbitGroup ≃* SL(2, F)) := by
  obtain ⟨O₀, hA⟩ := d4_orbits_eq_singleton D hχ J'
  have hO₀ : O₀ ∈ (D.withOrbit J').orbits := hA ▸ Set.mem_singleton O₀
  have hcard := orbitCard_eq_of_thetaProperties (D.withOrbit J') hθ hDθ hO₀
  have hne := ExcSelector.orbitMap_neg_one_ne_one (D.withOrbit J') (Or.inr ⟨rfl, rfl⟩) hO₀ hcard
  have hinj : Function.Injective ((D.withOrbit J').orbitGroupHom hO₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA'
    have h1 : (D.withOrbit J').orbitMap O₀ A = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hA')
    rcases (D.withOrbit J').eq_one_or_neg_one_of_orbitMap_eq_one hO₀ h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) hne
  have hfin := ExcSelector.finite_orbitField' (D.withOrbit J') hO₀
  refine ⟨_, inferInstance, hfin, ?_, ⟨(MulEquiv.ofBijective _
    ⟨hinj, (D.withOrbit J').orbitGroupHom_surjective hO₀ hA⟩).symm⟩⟩
  rw [(D.withOrbit J').card_orbitField hO₀]
  rcases hcard with h | h
  · exact Or.inl (by rw [h, pow_one]; rfl)
  · exact Or.inr (by rw [h]; rfl)

theorem card_SL_dvd_card_SL_cube {K F : Type*} [Field K] [Finite K] [Field F] [Finite F]
    (hF : Nat.card F = Nat.card K ^ 3) : Nat.card SL(2, K) ∣ Nat.card SL(2, F) := by
  rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  refine Nat.mul_dvd_mul (dvd_pow_self _ (by norm_num)) ?_
  have h := Nat.sub_dvd_pow_sub_pow (Nat.card K ^ 2) 1 3
  rw [one_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul] at h
  exact h

theorem slComponentForm_of_SL_q_or_cube {K : Type} [Field K] [Finite K] {G : Type} [Group G]
    (hG : ∀ L : Subgroup G, IsComponent L → ∃ (F : Type) (_ : Field F) (_ : Finite F),
      (Nat.card F = Nat.card K ∨ Nat.card F = Nat.card K ^ 3) ∧ Nonempty (L ≃* SL(2, F))) :
    SLComponentForm K G := by
  intro L hL
  obtain ⟨F, _, _, hF | hF, ⟨eL⟩⟩ := hG L hL
  · obtain ⟨e⟩ := nonempty_SL_mulEquiv_of_card hF
    exact Or.inl ⟨eL.trans e⟩
  · refine Or.inr ⟨?_, fun L' hL' hL'SL => ?_⟩
    · rw [Nat.card_congr eL.toEquiv]
      exact card_SL_dvd_card_SL_cube hF
    · obtain ⟨F', _, _, hF' | hF', ⟨eL'⟩⟩ := hG L' hL'
      · obtain ⟨e⟩ := nonempty_SL_mulEquiv_of_card hF'
        exact absurd ⟨eL'.trans e⟩ hL'SL
      · obtain ⟨e⟩ := nonempty_SL_mulEquiv_of_card (hF.trans hF'.symm)
        exact ⟨(eL.trans e).trans eL'.symm⟩

end CFSG.ComponentClassification.CatLeafProof
