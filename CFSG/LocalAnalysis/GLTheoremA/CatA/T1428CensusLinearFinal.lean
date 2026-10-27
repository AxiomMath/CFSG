module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusParity
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem census_linear
    (d : TauCeti.ValidLieTypeIndex) {n : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = TauCeti.LieTypeIndex.A n q) (hchar : d.1.characteristic = 2) :
    ∀ η : MulAut (TauCeti.CFSGIndex.lie d).Group,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (TauCeti.CFSGIndex.lie d).Group →
      η ^ 3 = 1 → η ≠ 1 → ∀ r : ℕ, Odd r → 1 < r →
      ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        CFSG.Open.IsComponentOf J₁ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₃ (fixSubgroup η) →
        J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
        catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
        catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
        catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) →
        (catalogIs (TauCeti.CFSGIndex.lie d).Group (S10.isU6n r) ∧
          ∀ M : Subgroup (TauCeti.CFSGIndex.lie d).Group,
            CFSG.Open.IsComponentOf M (fixSubgroup η) →
              catalogIs (↥M ⧸ Subgroup.center ↥M) (S10.isL2n r)) ∨
        catalogIs (TauCeti.CFSGIndex.lie d).Group (isD4n r) := by
  intro η hη hη3 hηne r hr _hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  obtain ⟨k, hkfield, hkfin, e, A, c, K₁, K₂, K₃,
    hcardk, hchark, hA3, hK₁, hK₂, hK₃, hK12, hK13, hK23, hL1', hL2', hL3'⟩ :=
    census_linear_reduce d hd hchar η hη hη3 hηne r hr J₁ J₂ J₃
      hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  letI : Field k := hkfield
  letI : Fintype k := hkfin
  letI : CharP k 2 := hchark
  have hpq : q.p = 2 := by
    have := hchar
    rw [hd, TauCeti.LieTypeIndex.characteristic_A] at this
    exact this
  have hk2 : Nat.card k = 2 ^ q.exponent := by
    rw [hcardk, TauCeti.PrimePower.card_def, hpq]
  by_cases hpe : Even q.exponent
  · exact (linear_no_l2_component_of_even_exponent hA3 ⟨q.exponent, hk2, hpe⟩ hK₁ hr hL1').elim
  · have hpo : Odd q.exponent := Nat.not_even_iff_odd.mp hpe
    have hcop : Nat.Coprime 3 (Nat.card k - 1) := by
      rw [hk2]
      exact coprime_three_two_pow_sub_one_of_odd hpo
    exact (linear_not_three_components hcop hA3 hK₁ hK₂ hK₃ hK12 hK13 hK23).elim

end CFSG.LocalAnalysis.GLTheoremA.T1428
