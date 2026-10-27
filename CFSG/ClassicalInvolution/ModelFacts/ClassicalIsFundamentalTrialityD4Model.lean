module

public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (p e : ℕ) [Fact p.Prime]

@[expose] noncomputable def trialityD4Phi (k : Type) [Field k]
    [Algebra (GaloisField p (3 * e)) k] :
    twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e) →* ModGL TwistTag.D4.tag k :=
  (baseChangeGL (algebraMap (GaloisField p (3 * e)) k)).comp
    ((adjointGroup d4 (GaloisField p (3 * e))).subtype.comp
      (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)).subtype)

theorem trialityD4Phi_injective (k : Type) [Field k] [Algebra (GaloisField p (3 * e)) k] :
    Function.Injective (trialityD4Phi p e k) :=
  (baseChangeGL_injective (algebraMap (GaloisField p (3 * e)) k)).comp
    (Subtype.val_injective.comp Subtype.val_injective)

theorem card_galoisField_three_mul (he : 1 ≤ e) :
    Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ TwistTag.D4.order := by
  rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
  rfl

theorem range_trialityD4Phi (hp2 : p ≠ 2) (he : 1 ≤ e) :
    (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))).range =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
          (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
            (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))),
        fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
          (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
            (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))⁆ := by
  classical
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  set σ := iterateFrobenius K0 p e with hσdef
  have hodd : Odd (p ^ e) := (Nat.Prime.eq_two_or_odd' Fact.out |>.resolve_left hp2).pow
  have hK : Nat.card K0 = (p ^ e) ^ TwistTag.D4.order := card_galoisField_three_mul p e he
  have hK3 : Nat.card K0 = (p ^ e) ^ 3 := hK
  have hfin : Finite K0 := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hChark : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have hFr : ∀ c : k, iterateFrobenius k p e c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hσ : ∀ c : K0, σ c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  have hK2 : ringChar K0 ≠ 2 := by
    rw [ringChar.eq K0 p]
    exact hp2
  have hq2 : 2 ≤ p ^ e := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  let σK : K0 ≃+* K0 := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.D4 (Fact.out : p.Prime) he hodd K0 hK σ hσ k (iterateFrobenius k p e) hFr
  have h1 := (odd_diagram_fixed_root_group_perfect TwistTag.D4 K0 hK2 σK).2.2
  rw [hσK] at h1
  have h2 := commutator_twistedFixedGroup_eq_map σ hq2 hK3 hσ
  have h3 : (twistedGroup σ).map (adjointGroup d4 K0).subtype =
      (graphFixedRootGroup TwistTag.D4 K0 σ) := h2.symm.trans h1
  have h4 : (twistedGroup σ).subtype.range = twistedGroup σ := Subgroup.range_subtype _
  have h5 : (trialityD4Phi p e k).range =
      ((twistedGroup σ).map (adjointGroup d4 K0).subtype).map (baseChangeGL (algebraMap K0 k)) := by
    rw [trialityD4Phi, MonoidHom.range_comp, MonoidHom.range_comp, h4]
  rw [h5, h3]
  exact hder.symm

theorem trialityD4Phi_mem_fixedPointsIn (hp2 : p ≠ 2) (he : 1 ≤ e)
    (x : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) :
    trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e))) x ∈
      fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
        (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
          (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) := by
  have h1 : trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e))) x ∈
      (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))).range := ⟨x, rfl⟩
  rw [range_trialityD4Phi p e hp2 he] at h1
  refine Subgroup.commutator_le.2 (fun a ha b hb => ?_) h1
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

section Sign

@[expose] noncomputable def d4Sign (γ : Fin d4.rank → ℤ) : ℤ :=
  (rootOperatorFamily d4).pinnedFamilySign γ

theorem d4Sign_mul_self {K : Type} [Field K] (γ : Fin d4.rank → ℤ) :
    (d4Sign γ : K) * (d4Sign γ : K) = 1 :=
  (rootOperatorFamily d4).pinnedFamilySign_mul_self K γ

theorem d4Sign_ne_zero {K : Type} [Field K] (γ : Fin d4.rank → ℤ) : (d4Sign γ : K) ≠ 0 :=
  fun h => by
    have := d4Sign_mul_self (K := K) γ
    rw [h, zero_mul] at this
    exact zero_ne_one this

theorem coe_xPar_d4 {K : Type} [Field K] {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K γ ((d4Sign γ : K) * c) := by
  have h2 : pinnedX d4 K γ ((d4Sign γ : K) * c) =
      (rootOperatorFamily d4).eltUnit K ⟨γ, hγ⟩ c := by
    have e : (d4Sign γ : K) = ((rootOperatorFamily d4).pinnedFamilySign γ : K) := rfl
    rw [e, (rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ, ← mul_assoc,
      (rootOperatorFamily d4).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot hγ]
  exact h2.symm

end Sign

section RootGroup

variable {p e}

theorem trialityD4Phi_eq_pinnedX (k : Type) [Field k] [Algebra (GaloisField p (3 * e)) k]
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    {x : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)} {c : GaloisField p (3 * e)}
    (hx : (x : adjointGroup d4 (GaloisField p (3 * e))) =
      xPar (rootOperatorFamily d4) γ c) :
    (trialityD4Phi p e k x : ModGL TwistTag.D4.tag k) =
      pinnedX TwistTag.D4.tag k γ
        ((d4Sign γ : k) * algebraMap (GaloisField p (3 * e)) k c) := by
  have h1 : (trialityD4Phi p e k x : ModGL TwistTag.D4.tag k) =
      baseChangeGL (algebraMap (GaloisField p (3 * e)) k)
        (((x : adjointGroup d4 (GaloisField p (3 * e))) : ModGL d4 (GaloisField p (3 * e)))) := rfl
  have h2 := baseChangeGL_pinnedX (algebraMap (GaloisField p (3 * e)) k) (τ := TwistTag.D4.tag) γ
    ((d4Sign γ : GaloisField p (3 * e)) * c)
  rw [h1, hx, coe_xPar_d4 hγ, h2, map_mul, map_intCast]

end RootGroup

section FixedRoots

variable (p e : ℕ) [Fact p.Prime]

theorem sigma_cube_frobenius (he : 1 ≤ e) (c : GaloisField p (3 * e)) :
    iterateFrobenius (GaloisField p (3 * e)) p e
      (iterateFrobenius (GaloisField p (3 * e)) p e
        (iterateFrobenius (GaloisField p (3 * e)) p e c)) = c :=
  sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    (card_galoisField_three_mul p e he) (fun c => iterateFrobenius_def p e c) c

theorem exists_eq_algebraMap_of_pow_eq_d4 (he : 1 ≤ e)
    {d : AlgebraicClosure (GaloisField p (3 * e))} (hd : d ^ p ^ e = d) :
    ∃ c : GaloisField p (3 * e), algebraMap _ _ c = d ∧
      iterateFrobenius (GaloisField p (3 * e)) p e c = c := by
  have h1 : d ^ Nat.card (GaloisField p (3 * e)) = d := by
    rw [card_galoisField_three_mul p e he]
    change d ^ ((p ^ e) ^ 3) = d
    rw [pow_succ, pow_mul, pow_two, pow_mul, hd, hd, hd]
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_card_eq h1
  refine ⟨c, hc, ?_⟩
  apply (algebraMap (GaloisField p (3 * e)) (AlgebraicClosure (GaloisField p (3 * e)))).injective
  rw [iterateFrobenius_def, map_pow, hc, hd]

theorem map_twistedRootGroup_fixed_d4 (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) (hfix : rho β = β) :
    (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β)).map
        (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
      fixedPointsIn (rootSubgroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) β)
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
  set S := fixedPointsIn (rootSubgroup TwistTag.D4.tag k β) F with hS
  have hSle : S ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F :=
    inf_le_inf_right _ (rootSubgroup_le_adjointGroup β)
  have hSfin : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSle)
  set T := (twistedRootGroup σ (proj β)).map Φ with hT
  have hTS : T ≤ S := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ3 hβ rfl hfix _).1
      ((mem_twistedRootGroup (σ := σ)).1 hg)
    refine mem_fixedPointsIn.2 ⟨?_, (mem_fixedPointsIn.1 (hΦR g)).2⟩
    rw [hΦ, trialityD4Phi_eq_pinnedX k hβ hgc]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hTfin : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hTS)
  have hSq : Nat.card S ≤ p ^ e := card_fixedPointsIn_rootSubgroup_le p TwistTag.D4 he hβ hfix
  have hFq : Nat.card (frobeniusFixedField k p e) = p ^ e := card_frobeniusFixedField (by omega)
  have hex : ∀ d : frobeniusFixedField k p e, ∃ c : K0, algebraMap K0 k c = d ∧ σ c = c :=
    fun d => exists_eq_algebraMap_of_pow_eq_d4 p e he (mem_frobeniusFixedField.1 d.2)
  choose c hc1 hc2 using hex
  have hmem : ∀ d, xPar (rootOperatorFamily d4) β (c d) ∈
      twistedRootSubgroupD4 σ (proj β) := fun d => xPar_mem_of_fixed hσ3 hβ hfix (hc2 d)
  let x : ∀ d, twistedGroup σ := fun d =>
    ⟨xPar (rootOperatorFamily d4) β (c d),
      twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hβ) (hmem d)⟩
  let ψ : frobeniusFixedField k p e → T := fun d =>
    ⟨Φ (x d), Subgroup.mem_map_of_mem _ ((mem_twistedRootGroup (σ := σ)).2 (hmem d))⟩
  have hψ : Function.Injective ψ := by
    intro d d' h
    have h1 := congrArg Subtype.val h
    simp only [ψ] at h1
    rw [hΦ, trialityD4Phi_eq_pinnedX k hβ (x := x d) (c := c d) rfl,
      trialityD4Phi_eq_pinnedX k hβ (x := x d') (c := c d') rfl, hc1, hc1] at h1
    have h2 := pinnedX_injective _ _ _ h1
    exact Subtype.ext (mul_left_cancel₀ (d4Sign_ne_zero β) h2)
  have hcard : p ^ e ≤ Nat.card T := by
    calc p ^ e = Nat.card (frobeniusFixedField k p e) := hFq.symm
      _ ≤ Nat.card T := Nat.card_le_card_of_injective _ hψ
  exact Subgroup.eq_of_le_of_card_ge hTS (hSq.trans hcard)

end FixedRoots

end CFSG.ClassicalInvolution.ModelFacts
