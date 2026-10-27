module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChangeModels
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.SurvTwist

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc TensorProduct

section Generic

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Finite G] [Fact p.Prime]
  {D : CurtisDatum G cs p} {π : Ĝ →* G} (C : CentralCoverData D π p)

theorem heckeT_datum_comp {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (s : B) (v : V) :
    C.datum.heckeT (ρ.comp π) s v = D.heckeT ρ s v := by
  have := Fintype.ofFinite (D.X s)
  have : Fintype ↥(C.datum.X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  refine Fintype.sum_equiv (show ↥(C.datum.X s) ≃ ↥(D.X s) from C.lXEquiv s) _ _ fun x => ?_
  show ρ (π ((x : Ĝ) * C.nhat s)) v = ρ ((π x : G) * D.n s) v
  rw [map_mul, C.hn]

end Generic

theorem isSimpleRep_comp_of_surjective {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {Ĝ G : Type*} [Group Ĝ] [Group G] (π : Ĝ →* G) (hπ : Function.Surjective π)
    {ρ : Representation k G V} (hρ : IsSimpleRep ρ) : IsSimpleRep (ρ.comp π) := by
  refine ⟨hρ.1, fun W hW => hρ.2 W fun g w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  exact hW x w hw

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem isCoverType_comp {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(graphFixedRootGroup TwistTag.E6 K σ) V} {y : V}
    {χ : ↥(graphFixedRootGroup TwistTag.E6 K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsTwType 2 e6LongestData (surjective_of_finite σ) (card_orbitField_e6 hf hK σ hσ) ρ y χ J) :
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) (ρ.comp (coverHom hf hK σ hσ)) y
      (χ ∘ coverHom hf hK σ hσ) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst (K := K) σ
  have hfin : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
    have : Finite (ModGL TwistTag.E6.tag K) := inferInstance
    infer_instance
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨?_, h2, fun h hh => h3 _ hh, fun a => ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro x hx
    exact ((twistedE6Datum hf hK σ hσ).mem_fixU _).1 h1 _ hx.1
  · rw [heckeT_datum_comp (twistedE6CoverData hf hK σ hσ)]
    refine (h4 a).trans ?_
    refine and_congr (forall_congr' fun u => ?_) Iff.rfl
    show χ (hC TwistTag.E6 K σ a u) = 1 ↔ χ (coverHom hf hK σ hσ (hatH hf hK σ hσ a u)) = 1
    rw [coverHom_hatH]

include hf hK hσ in
theorem twE6_iso_78 {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {V : Type}
    [AddCommGroup V] [Module k V] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (h78 : Tw78Type hf K hK σ hσ k χ J) :
    ∃ (b : ℕ) (β : (k ⊗[K] RootModule TwistTag.E6.tag K) ≃ₗ[k] FrobTwist (frobAut k b) V),
      ∀ (g : ↥(TwistedE6.fixedGroup K σ)) (v : k ⊗[K] RootModule TwistTag.E6.tag K),
        β (((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) g v) =
          twistRep (frobAut k b) ρ g (β v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst (K := K) σ
  obtain ⟨hJ, b, hb, hχ⟩ := h78
  refine ⟨b, ?_⟩
  set θ := frobAut k b with hθ
  have htm : IsCoverType (twistedE6CoverRankOne hf hK σ hσ)
      ((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) (bcVec k (rootVec TwistTag.E6.tag K e6Theta))
      ((fun g => algebraMap K k (twChiAdj σ g)) ∘ coverHom hf hK σ hσ) (Finset.univ.erase twN3) :=
    isCoverType_comp hf hK σ hσ (twAdj_bc_isTwType hf hK σ hσ (k := k))
  have hsm := isSimpleRep_comp_of_surjective (coverHom hf hK σ hσ)
    (isCentralCover_coverHom hf hK σ hσ).surj (isSimpleRep_bc_twAdj hf hK σ hσ (k := k))
  have htw : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) (twistRep θ ρ)
      (show FrobTwist θ V from y) (fun g => θ.symm (χ g)) J :=
    IsTypeGen.twist θ (twistedE6CoverData hf hK σ hσ).datum
      (show IsTypeGen (twistedE6CoverData hf hK σ hσ).datum ρ y χ J _
        (fun s => (orbitField TwistTag.E6 K σ s)ˣ) (twistedE6CoverRankOne hf hK σ hσ).hh from ht)
  have hJmem : ∀ a, a ≠ twN3 → a ∈ J := fun a ha => hJ ▸ Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩
  have hne0 : twN0 ≠ twN3 := by decide
  have hne1 : twN1 ≠ twN3 := by decide
  have hd : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (u : (orbitField TwistTag.E6 K σ a)ˣ),
      θ.symm (χ (hatH hf hK σ hσ a u)) =
        ((fun g => algebraMap K k (twChiAdj σ g)) ∘ coverHom hf hK σ hσ) (hatH hf hK σ hσ a u) := by
    intro a u
    by_cases ha : a = twN3
    · subst ha
      rw [hχ u, frobAut_symm_pow]
      show _ = algebraMap K k (twChiAdj σ (coverHom hf hK σ hσ (hatH hf hK σ hσ twN3 u)))
      rw [coverHom_hatH]
      exact (congrArg (algebraMap K k) (twChiAdj_hC_a1 σ u)).symm
    · have h1 : χ (hatH hf hK σ hσ a u) = 1 := ((ht.2.2.2 a).1 (hJmem a ha)).1 u
      rw [h1, map_one]
      show _ = algebraMap K k (twChiAdj σ (coverHom hf hK σ hσ (hatH hf hK σ hσ a u)))
      rw [coverHom_hatH,
        twChiAdj_theta_fix σ (twAdj_hC_theta σ a ha u), map_one]
  have hH := chi_eq_on_Hcover hf hK σ hσ htw htm (hJmem _ hne0) (hJmem _ hne1)
    (by rw [Finset.mem_erase]; exact ⟨hne0, Finset.mem_univ _⟩)
    (by rw [Finset.mem_erase]; exact ⟨hne1, Finset.mem_univ _⟩) hd
  have htw' : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) (twistRep θ ρ)
      (show FrobTwist θ V from y)
      ((fun g => algebraMap K k (twChiAdj σ g)) ∘ coverHom hf hK σ hσ) (Finset.univ.erase twN3) := by
    obtain ⟨h1, h2, h3, h4⟩ := htw
    subst hJ
    refine ⟨h1, h2, fun h hh => (h3 h hh).trans ?_, fun a => ?_⟩
    · have e : θ.symm (χ h) = ((fun g => algebraMap K k (twChiAdj σ g)) ∘ coverHom hf hK σ hσ) h :=
        hH h hh
      exact congrArg (fun c => c • (show FrobTwist θ V from y)) e
    · rw [h4 a]
      refine and_congr (forall_congr' fun u => ?_) Iff.rfl
      show θ.symm (χ (hatH hf hK σ hσ a u)) = 1 ↔ _
      rw [hd a u]
      exact Iff.rfl
  exact twisted_iso_of_isCoverType hf hK σ hσ hsm (isSimpleRep_twistRep θ hρ) htm htw'

include hf hK hσ in
theorem tw78CentreTrivial_holds : Tw78CentreTrivial hf K hK σ hσ := by
  intro k _ _ _ _ m ρ y χ J hρ ht h78 x hx
  obtain ⟨b, β, hβ⟩ := twE6_iso_78 hf hK σ hσ hρ ht h78
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, hv⟩ := β.surjective (show FrobTwist (frobAut k b) (Fin m → k) from w)
  have h1 := hβ x v
  have e : ((bcRep k (twAdj σ)).comp (coverHom hf hK σ hσ)) x = 1 := by
    show bcRep k (twAdj σ) (coverHom hf hK σ hσ x) = 1
    rw [hx, map_one]
  rw [e, Module.End.one_apply, hv] at h1
  exact h1.symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
