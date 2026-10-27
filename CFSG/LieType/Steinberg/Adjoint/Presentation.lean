module

public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.ExtraPairs
public import CFSG.LieType.Steinberg.Conclusion
public import CFSG.LieType.Chevalley.RootOps.All
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal

universe w

theorem neighbour_F4 :
    ∀ i : Fin (Tag.rank .F4), ∃ l, Tag.cartan .F4 i l = -1 ∧ Tag.cartan .F4 l i = -1 := by
  intro i
  fin_cases i <;> decide

theorem neighbour_E8 :
    ∀ i : Fin (Tag.rank .E8), ∃ l, Tag.cartan .E8 i l = -1 ∧ Tag.cartan .E8 l i = -1 := by
  intro i
  fin_cases i <;> decide

@[expose] def cartanInvF4 : Matrix (Fin (Tag.rank .F4)) (Fin (Tag.rank .F4)) ℤ :=
  !![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2]

theorem cartan_mul_cartanInvF4 : Tag.cartan .F4 * cartanInvF4 = 1 := by
  decide +kernel

@[expose] def cartanInvE8 : Matrix (Fin (Tag.rank .E8)) (Fin (Tag.rank .E8)) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem cartan_mul_cartanInvE8 : Tag.cartan .E8 * cartanInvE8 = 1 := by
  decide +kernel

variable (K : Type) [Field K]

abbrev f4Datum : UniversalRootDatum ↥(adjointGroup .F4 K) :=
  adjDatum (rootOperatorFamily .F4) K

abbrev f4Par : (Fin (Tag.rank .F4) → ℤ) → K → ↥(adjointGroup .F4 K) :=
  xPar (rootOperatorFamily .F4)

theorem f4_isCTGroupDatum :
    CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (f4Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (f4Datum K).isFiniteType) (f4Datum K).roots
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K) :=
  adjDatum_isCTGroupDatum _ K

theorem f4_steinbergExtras :
    SteinbergExtras (f4Datum K) (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K) :=
  adjDatum_steinbergExtras f4Data_valid noG2_F4 (fun i => (neighbour_F4 i).imp fun _ h => h.1)
    cartan_mul_cartanInvF4

theorem f4_isParametrization :
    IsParametrization (Φ := RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible)
      (f4Datum K).rootGroup (f4Par K) :=
  adjDatum_isParametrization (F := rootOperatorFamily .F4) (K := K) _ (adjDatum_roots _ K)

theorem f4_commutatorFormula
    (O : CommOrder (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible)) :
    ∃ C : (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible).roots,
        ∀ β ∈ (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible).roots,
          ∀ p ∈ expPairs (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible)
            α β, (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
        CommutatorFormula (f4Par K) O C :=
  ⟨commC (rootOperatorFamily .F4) f4Data_valid,
    fun _ hα _ hβ _ hp => commC_natAbs noG2_F4 (adjDatum_roots _ K) hα hβ hp,
    commutatorFormula_commC f4Data_valid noG2_F4 _ (adjDatum_roots _ K) O⟩

theorem f4_chevalleyExtras
    (O : CommOrder (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible))
    (C : (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (f4Par K) O C) : ChevalleyExtras (f4Datum K) K (f4Par K) C O :=
  adjDatum_chevalleyExtras _ K f4Data_valid noG2_F4 neighbour_F4 O C hC

theorem f4_conclusionA : ConclusionA.{0, w} (f4Datum K) :=
  conclusionA_of (f4_isCTGroupDatum K) (f4_steinbergExtras K)

theorem f4_conclusionB [Finite K] : ConclusionB (f4Datum K) K (f4Par K) :=
  conclusionB_of rfl (f4_isCTGroupDatum K) (f4_steinbergExtras K)
    (f4_isParametrization K) (f4_commutatorFormula K)
    (f4_chevalleyExtras K)

abbrev e8Datum : UniversalRootDatum ↥(adjointGroup .E8 K) :=
  adjDatum (rootOperatorFamily .E8) K

abbrev e8Par : (Fin (Tag.rank .E8) → ℤ) → K → ↥(adjointGroup .E8 K) :=
  xPar (rootOperatorFamily .E8)

theorem e8_isCTGroupDatum :
    CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (e8Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (e8Datum K).isFiniteType) (e8Datum K).roots
      (e8Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .E8 K) (torus (τ := .E8) K) :=
  adjDatum_isCTGroupDatum _ K

theorem e8_steinbergExtras :
    SteinbergExtras (e8Datum K) (CFSG.LieType.Chevalley.weylElement .E8 K) (torus (τ := .E8) K) :=
  adjDatum_steinbergExtras e8Data_valid noG2_E8 (fun i => (neighbour_E8 i).imp fun _ h => h.1)
    cartan_mul_cartanInvE8

theorem e8_isParametrization :
    IsParametrization (Φ := RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible)
      (e8Datum K).rootGroup (e8Par K) :=
  adjDatum_isParametrization (F := rootOperatorFamily .E8) (K := K) _ (adjDatum_roots _ K)

theorem e8_commutatorFormula
    (O : CommOrder (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible)) :
    ∃ C : (Fin (Tag.rank .E8) → ℤ) → (Fin (Tag.rank .E8) → ℤ) → ℕ × ℕ → ℤ,
      (∀ α ∈ (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible).roots,
        ∀ β ∈ (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible).roots,
          ∀ p ∈ expPairs (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible)
            α β, (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
        CommutatorFormula (e8Par K) O C :=
  ⟨commC (rootOperatorFamily .E8) e8Data_valid,
    fun _ hα _ hβ _ hp => commC_natAbs noG2_E8 (adjDatum_roots _ K) hα hβ hp,
    commutatorFormula_commC e8Data_valid noG2_E8 _ (adjDatum_roots _ K) O⟩

theorem e8_chevalleyExtras
    (O : CommOrder (RootSystem.ofCartan (e8Datum K).isFiniteType (e8Datum K).divisible))
    (C : (Fin (Tag.rank .E8) → ℤ) → (Fin (Tag.rank .E8) → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (e8Par K) O C) : ChevalleyExtras (e8Datum K) K (e8Par K) C O :=
  adjDatum_chevalleyExtras _ K e8Data_valid noG2_E8 neighbour_E8 O C hC

theorem e8_conclusionA : ConclusionA.{0, w} (e8Datum K) :=
  conclusionA_of (e8_isCTGroupDatum K) (e8_steinbergExtras K)

theorem e8_conclusionB [Finite K] : ConclusionB (e8Datum K) K (e8Par K) :=
  conclusionB_of rfl (e8_isCTGroupDatum K) (e8_steinbergExtras K)
    (e8_isParametrization K) (e8_commutatorFormula K)
    (e8_chevalleyExtras K)

end CFSG.LieType.Steinberg.Adjoint
