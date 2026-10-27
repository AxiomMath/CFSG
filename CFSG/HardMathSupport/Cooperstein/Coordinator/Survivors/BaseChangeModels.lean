module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.BaseChange
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjE7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.TwAdj78

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw TensorProduct

section E7_56

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type*} [Field k] [Algebra K k]
  [CharP k 2]

theorem isSimpleRep_bc_adj132 : IsSimpleRep (bcRep k (adj132 K)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isSimpleRep_bc (e7Datum (K := K)) (adj132 K) adj132Y adj132Y_ne_zero
    (fun _ hx => fixU_le_line132 hx) orbitSpan_adj132

theorem adj132_bc_isChevType :
    IsChevType .E7 K 2 exists_weyl_neg_E7 (bcRep k (adj132 K))
      (bcVec k (adj132Y : RootModule .E7 K ⧸ e7Z K)) (fun g => algebraMap K k (adjChi132 K g))
      (Finset.univ.erase e7node10) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsTypeGen.baseChange (chevDatum .E7 K 2 exists_weyl_neg_E7)
    (show IsTypeGen (chevDatum .E7 K 2 exists_weyl_neg_E7) (adj132 K) adj132Y (adjChi132 K)
      (Finset.univ.erase e7node10) _ (fun s => Kˣ) (fun i t => dC .E7 K i t)
        from adj132_isChevType)

end E7_56

section Tw27

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  {k : Type*} [Field k] [Algebra K k] [CharP k 2]

include hf hK hσ in
theorem isSimpleRep_bc_twRep27 : IsSimpleRep (bcRep k (twRep27 σ)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst σ
  isSimpleRep_bc (twistedE6CoverData hf hK σ hσ).datum (twRep27 σ) e6Y27 e6Y27_ne_zero
    (fun _ hx => fixU_le_line_tw hf hK σ hσ hx) (orbitSpan_twRep27 hf hK σ hσ)

include hf hK hσ in
theorem twRep27_bc_isCoverType :
    IsCoverType (twistedE6CoverRankOne hf hK σ hσ) (bcRep k (twRep27 σ))
      (bcVec k (e6Y27 : Fin e6Data.d →₀ K)) (fun g => algebraMap K k (twChi27 σ g))
      (Finset.univ.erase twA0) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst σ
  IsTypeGen.baseChange (twistedE6CoverData hf hK σ hσ).datum
    (show IsTypeGen (twistedE6CoverData hf hK σ hσ).datum (twRep27 σ) e6Y27 (twChi27 σ)
      (Finset.univ.erase twA0) _ (fun s => (orbitField TwistTag.E6 K σ s)ˣ)
      (twistedE6CoverRankOne hf hK σ hσ).hh from twRep27_isCoverType hf hK σ hσ)

include hf hK hσ in
theorem twisted_iso_27_bc {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} (hρ : IsSimpleRep ρ) {y : V}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y
      (fun g => algebraMap K k (twChi27 σ g)) (Finset.univ.erase twA0)) :
    ∃ β : (k ⊗[K] (Fin e6Data.d →₀ K)) ≃ₗ[k] V, ∀ (g : ↥(TwistedE6.fixedGroup K σ))
      (v : k ⊗[K] (Fin e6Data.d →₀ K)), β (bcRep k (twRep27 σ) g v) = ρ g (β v) :=
  twisted_iso_of_isCoverType hf hK σ hσ (isSimpleRep_bc_twRep27 hf hK σ hσ) hρ
    (twRep27_bc_isCoverType hf hK σ hσ) ht

end Tw27

section TwAdjBc

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  {k : Type*} [Field k] [Algebra K k] [CharP k 2]

include hf hK hσ in
theorem isSimpleRep_bc_twAdj : IsSimpleRep (bcRep k (twAdj σ)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst σ
  have hfin : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
    have : Finite (ModGL TwistTag.E6.tag K) := inferInstance
    infer_instance
  isSimpleRep_bc (twistedE6Datum hf hK σ hσ) (twAdj σ) (rootVec TwistTag.E6.tag K e6Theta)
    rootVec_theta_ne_zero (fun _ hx => fixU_le_line_adjTw hf hK σ hσ hx)
    (orbitSpan_twAdj hf hK σ hσ)

include hf hK hσ in
theorem twAdj_bc_isTwType :
    IsTwType 2 e6LongestData (surjective_of_finite σ) (card_orbitField_e6 hf hK σ hσ)
      (bcRep k (twAdj σ)) (bcVec k (rootVec TwistTag.E6.tag K e6Theta))
      (fun g => algebraMap K k (twChiAdj σ g)) (Finset.univ.erase twA1) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_fixedGroup_inst σ
  have hfin : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
    have : Finite (ModGL TwistTag.E6.tag K) := inferInstance
    infer_instance
  IsTypeGen.baseChange (twistedE6Datum hf hK σ hσ)
    (show IsTypeGen (twistedE6Datum hf hK σ hσ) (twAdj σ) (rootVec TwistTag.E6.tag K e6Theta)
      (twChiAdj σ) (Finset.univ.erase twA1) _
      (fun s => (orbitField TwistTag.E6 K σ s)ˣ) (fun a u => hC TwistTag.E6 K σ a u)
        from twAdj_isTwType hf hK σ hσ)

end TwAdjBc

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
