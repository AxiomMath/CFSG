module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE

variable {τ : Tag}

theorem exists_unit_orderOf_card_sub_one_alg (K L : Type) [Field K] [Finite K] [Field L]
    [Algebra K L] : ∃ ζ : Lˣ, orderOf ζ = Nat.card K - 1 ∧ ζ ^ (Nat.card K - 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  let φ : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (algebraMap K L).injective
  refine ⟨φ g, ?_, ?_⟩
  · rw [orderOf_injective φ hφ g, hord]
  · rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]

theorem exists_unit_orderOf_card_add_one_alg (K L : Type) [Field K] [Finite K] [Field L]
    [Algebra K L] [IsAlgClosed L] :
    ∃ ζ : Lˣ, orderOf ζ = Nat.card K + 1 ∧ ζ ^ (Nat.card K + 1) = 1 := by
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  haveI : NeZero (((Nat.card K + 1 : ℕ)) : L) := ⟨by
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one]
    exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card K + 1)
  set ζu : Lˣ := (hζ.isUnit (by omega)).unit with hζu
  have hζu' : IsPrimitiveRoot ζu (Nat.card K + 1) :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  exact ⟨ζu, hζu'.eq_orderOf.symm, hζu'.pow_eq_one⟩

section Split

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_le_twistedTorus_card_one {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : 1 ≤ q) {ζ : Lˣ} (hζ : ζ ^ (q - 1) = 1) :
    ∃ H₀ : Subgroup (ModGL τ L), H₀ ≤
        twistedTorusOf (canonicalRep (coxeterSystem τ) L (1 : WeylGroup τ))
          (Units.map (entrywiseHom Fr)) ∧
      Nat.card H₀ = orderOf ζ ^ τ.rank := by
  classical
  let ψ : (Fin τ.rank → Subgroup.zpowers ζ) →* ModGL τ L :=
    (rootDiagUnitHom τ L).comp ((Subgroup.zpowers ζ).subtype.compLeft (Fin τ.rank))
  have hψ : ∀ a, ψ a = rootDiagUnit τ (fun i => (a i : Lˣ)) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    funext i
    exact Subtype.ext (congrFun (rootDiagUnit_injective hab) i)
  refine ⟨ψ.range, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [mem_twistedTorusOf_iff_negPhi, hψ]
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [negPhi_rootDiagUnit_gen_pow Fr 1 hFr, weylTuple_one]
    congr 1
    funext i
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (a i).2
    show ((a i : Lˣ)) ^ q = (a i : Lˣ)
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : ζ ^ q = ζ := by
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      rw [pow_succ, show m = m + 1 - 1 by omega, hζ, one_mul]
    rw [this]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, Nat.card_zpowers,
      Nat.card_eq_fintype_card, Fintype.card_fin]

end Split

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
