module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Model
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule

section Sign

@[expose] noncomputable def e6Sign (β : Fin (Tag.rank .E6) → ℤ) : ℤ :=
  (rootOperatorFamily .E6).pinnedFamilySign β * relSignOr (rootOperatorFamily .E6) e6AdjData_valid β

theorem e6Sign_mul_self {K : Type} [Field K] (β : Fin (Tag.rank .E6) → ℤ) :
    (e6Sign β : K) * (e6Sign β : K) = 1 := by
  simp only [e6Sign, Int.cast_mul]
  calc _ = ((rootOperatorFamily .E6).pinnedFamilySign β : K) *
        ((rootOperatorFamily .E6).pinnedFamilySign β : K) *
        ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid β : K) *
          (relSignOr (rootOperatorFamily .E6) e6AdjData_valid β : K)) := by ring
    _ = 1 := by
      rw [(rootOperatorFamily .E6).pinnedFamilySign_mul_self, relSignOr_mul_self, one_mul]

theorem e6Sign_ne_zero {K : Type} [Field K] (β : Fin (Tag.rank .E6) → ℤ) : (e6Sign β : K) ≠ 0 :=
  fun h => by
    have := e6Sign_mul_self (K := K) β
    rw [h, zero_mul] at this
    exact zero_ne_one this

theorem coe_e6Isogeny_xm {K : Type} [Field K] [Finite K] {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) (c : K) :
    ((e6IsogenyT K (e6Data_valid.xm K β c) : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K β ((e6Sign β : K) * c) := by
  have h : e6IsogenyT K (e6Data_valid.xm K β c) =
      yPar (rootOperatorFamily .E6) e6AdjData_valid β c := e6Isogeny_xm K hβ c
  have h2 : pinnedX .E6 K β ((e6Sign β : K) * c) = (rootOperatorFamily .E6).eltUnit K ⟨β, hβ⟩
      ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid β : K) * c) := by
    rw [(rootOperatorFamily .E6).pinnedX_eq_eltUnit K hβ]
    congr 1
    rw [e6Sign, Int.cast_mul]
    calc _ = ((rootOperatorFamily .E6).pinnedFamilySign β : K) *
          ((rootOperatorFamily .E6).pinnedFamilySign β : K) *
          ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid β : K) * c) := by ring
      _ = _ := by rw [(rootOperatorFamily .E6).pinnedFamilySign_mul_self, one_mul]
  rw [h, yPar, xPar_of_isRoot hβ]
  exact h2.symm

end Sign

section Phi

variable (p f : ℕ) [Fact p.Prime]

theorem twistedE6Phi_xFixed (k : Type) [Field k] [Algebra (GaloisField p (2 * f)) k]
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (hfix : rho β = β)
    (c : GaloisField p (2 * f)) (hc : frobQ p f c = c) :
    (twistedE6Phi p f k (xFixed (frobQ p f) hβ hfix c hc) : ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k β ((e6Sign β : k) * algebraMap (GaloisField p (2 * f)) k c) := by
  have h1 : (twistedE6Phi p f k (xFixed (frobQ p f) hβ hfix c hc) : ModGL TwistTag.E6.tag k) =
      baseChangeGL (algebraMap (GaloisField p (2 * f)) k)
        ((e6IsogenyT (GaloisField p (2 * f)) (e6Data_valid.xm _ β c) :
          ↥(adjointGroup TwistTag.E6.tag (GaloisField p (2 * f)))) :
            ModGL TwistTag.E6.tag (GaloisField p (2 * f))) := rfl
  have h2 := baseChangeGL_pinnedX (algebraMap (GaloisField p (2 * f)) k) (τ := TwistTag.E6.tag) β
    ((e6Sign β : GaloisField p (2 * f)) * c)
  rw [h1, coe_e6Isogeny_xm hβ, h2, map_mul, map_intCast]

theorem exists_eq_algebraMap_of_pow_eq (hf : 1 ≤ f)
    {d : AlgebraicClosure (GaloisField p (2 * f))} (hd : d ^ p ^ f = d) :
    ∃ c : GaloisField p (2 * f), algebraMap _ _ c = d ∧ frobQ p f c = c := by
  have h1 : d ^ Nat.card (GaloisField p (2 * f)) = d := by
    rw [card_galoisField_two_mul' p f hf]
    change d ^ ((p ^ f) ^ 2) = d
    rw [sq, pow_mul, hd, hd]
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_card_eq h1
  refine ⟨c, hc, ?_⟩
  apply (algebraMap (GaloisField p (2 * f)) (AlgebraicClosure (GaloisField p (2 * f)))).injective
  rw [frobQ_apply, map_pow, hc, hd]

end Phi

section RootGroup

variable (p f : ℕ) [Fact p.Prime]

theorem map_twistedRootGroup_fixed (hp2 : p ≠ 2) (hf : 1 ≤ f) {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) (hfix : rho β = β) :
    (twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (proj β)).map
        (twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f)))) =
      fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) β)
        (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
          (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))) := by
  classical
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set F := frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) with hF
  set Φ := twistedE6Phi p f k with hΦ
  have hΦR : ∀ g : twistedE6Group p f, Φ g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k) F := by
    intro g
    have h1 : Φ g ∈ Φ.range := ⟨g, rfl⟩
    rw [hΦ, range_twistedE6Phi p f hp2 hf] at h1
    refine Subgroup.commutator_le.2 (fun a ha b hb => ?_) h1
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.E6.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p hf (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p f))
      (diagramMap_pow_order TwistTag.E6 k)
  set S := fixedPointsIn (rootSubgroup TwistTag.E6.tag k β) F with hS
  have hSle : S ≤ fixedPointsIn (adjointGroup TwistTag.E6.tag k) F :=
    inf_le_inf_right _ (rootSubgroup_le_adjointGroup β)
  have hSfin : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSle)
  set T := (twistedRootGroup K0 (frobQ p f) (proj β)).map Φ with hT
  have hTS : T ≤ S := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed (frobQ p f) hβ rfl hfix g).1 hg
    have hg' : g = xFixed (frobQ p f) hβ hfix c hc := Subtype.ext hgc
    refine mem_fixedPointsIn.2 ⟨?_, (mem_fixedPointsIn.1 (hΦR g)).2⟩
    rw [hg', hΦ, twistedE6Phi_xFixed]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hTfin : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hTS)
  have hSq : Nat.card S ≤ p ^ f := card_fixedPointsIn_rootSubgroup_le p TwistTag.E6 hf hβ hfix
  have hFq : Nat.card (frobeniusFixedField k p f) = p ^ f := card_frobeniusFixedField (by omega)
  have hex : ∀ d : frobeniusFixedField k p f,
      ∃ c : K0, algebraMap K0 k c = d ∧ frobQ p f c = c := fun d =>
    exists_eq_algebraMap_of_pow_eq p f hf (mem_frobeniusFixedField.1 d.2)
  choose c hc1 hc2 using hex
  let ψ : frobeniusFixedField k p f → T := fun d =>
    ⟨Φ (xFixed (frobQ p f) hβ hfix (c d) (hc2 d)),
      Subgroup.mem_map_of_mem _ (xFixed_mem (frobQ p f) hβ hfix _ _)⟩
  have hψ : Function.Injective ψ := by
    intro d d' h
    have h1 := congrArg Subtype.val h
    simp only [ψ] at h1
    rw [hΦ, twistedE6Phi_xFixed, twistedE6Phi_xFixed, hc1, hc1] at h1
    have h2 := pinnedX_injective _ _ _ h1
    exact Subtype.ext (mul_left_cancel₀ (e6Sign_ne_zero β) h2)
  have hcard : p ^ f ≤ Nat.card T := by
    calc p ^ f = Nat.card (frobeniusFixedField k p f) := hFq.symm
      _ ≤ Nat.card T := Nat.card_le_card_of_injective _ hψ
  exact Subgroup.eq_of_le_of_card_ge hTS (hSq.trans hcard)

end RootGroup

section Longest

open CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem iform_proj_eq_four_of_rho_eq {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (h : rho α = α) : iform (proj α) (proj α) = 4 := by
  have key : ∀ α ∈ rootFinset .E6, rho α = α → iform (proj α) (proj α) = 4 := by
    decide +kernel
  exact key α (mem_rootFinset.2 hα) h

theorem isLongestRoot_twistedDatum_of_iform_eq_four {K : Type} [Field K] (θ : K →+* K)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (h : iform γ γ = 4) :
    CFSG.ClassicalInvolution.Generic.IsLongestRoot (twistedDatum K θ) γ := by
  have hγ' : γ ∈ (twistedDatum K θ).roots := by
    rw [twistedDatum_roots]
    exact hγ
  rcases hγ' with ⟨w, j, rfl⟩ | ⟨w, j, hj, rfl⟩
  · have hinv := iform_weylAction (isFiniteType_cartan .F4) w (Pi.single j 1)
    have h' : iform (weylAction (isFiniteType_cartan .F4) w (Pi.single j 1))
        (weylAction (isFiniteType_cartan .F4) w (Pi.single j 1)) = 4 := h
    rw [hinv] at h'
    exact (isLongest_single_F4 rfl _ (lt_two_of_iform_single_F4 h')).map_weylAction w
  · exact absurd hj (Set.notMem_empty j)

theorem isLongestRoot_twistedDatum_proj {K : Type} [Field K] (θ : K →+* K)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (h : rho α = α) :
    CFSG.ClassicalInvolution.Generic.IsLongestRoot (twistedDatum K θ) (proj α) :=
  isLongestRoot_twistedDatum_of_iform_eq_four θ (isRoot_proj hα)
    (iform_proj_eq_four_of_rho_eq hα h)

end Longest

end CFSG.ClassicalInvolution.ModelFacts
