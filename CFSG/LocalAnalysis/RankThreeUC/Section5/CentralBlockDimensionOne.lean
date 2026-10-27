module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryDecomposition
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockCovariance
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryHyperplaneFreeOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PFixedLineDimension
public import CFSG.LinearAlgebra.CoprimeActions.FixedLineFreeOrbitDimensionOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockDimensionOne

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

@[expose] noncomputable def tau (hc : BinaryActionRankCounterexample G p P T B e ρ) : Representation (ZMod p) B (Space hc) :=
  (sigma hc).comp ((conjOnP P hc.faithfulBinaryIrreducibleAction.normal).comp B.subtype)

theorem orbit_independent (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) (K : BinaryRepresentations.hyperplanes 2 (X hc)) :
    iSupIndep (fun b : B => (E hc K.val).map (tau hc b)) := by
  have he : Odd e := (PrimeB.prime_order hc hr).2.2.1
  have hdec := (CentralBinaryDecomposition.decomposition hc he hXne).1
  let f : B → BinaryRepresentations.hyperplanes 2 (X hc) := fun b =>
    ⟨K.val.map (MulAut.conj (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val)).toMonoidHom,
      CentralBlockCovariance.conjugate_hyperplane hc he K b⟩
  have hf : Function.Injective f := fun b₁ b₂ h =>
    BinaryHyperplaneFreeOrbit.conj_injective hc hr K b₁ b₂ (congrArg Subtype.val h)
  have := hdec.comp hf
  convert this using 2 with b
  exact CentralBlockCovariance.covariance hc K.val b

theorem invariants_tau (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Representation.invariants (tau hc) = Qline hc := by
  ext v
  rw [Representation.mem_invariants]
  unfold Qline E
  rw [BinaryRepresentations.mem_fixedSpace_iff, PFixedLineDimension.Bstar_eq_map hc]
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    exact h ⟨b, hb⟩
  · intro h b
    exact h _ ⟨b.val, b.2, rfl⟩

theorem finrank_eq_one (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) (K : BinaryRepresentations.hyperplanes 2 (X hc)) (hEne : E hc K.val ≠ ⊥) :
    Module.finrank (ZMod p) (E hc K.val) = 1 := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  haveI : Fintype B := Fintype.ofFinite B
  haveI : FiniteDimensional (ZMod p) (Space hc) := inferInstance
  refine CFSG.LinearAlgebra.CoprimeActions.FixedLineFreeOrbitDimensionOne.finrank_eq_one (tau hc) (E hc K.val) hEne
    (orbit_independent hc hr hXne K) ?_
  rw [invariants_tau hc]
  exact PFixedLineDimension.finrank_eq_one hc

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockDimensionOne
