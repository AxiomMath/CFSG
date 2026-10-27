module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Core

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.A5.Kc3G2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie

theorem isoInv_g2ev (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3G2Ev X) :
    Kc3G2Ev Y :=
  let ⟨f, hf, hev, hm⟩ := h
  ⟨f, hf, hev, chevalleyExceptionalModel_of_mulEquiv e hm⟩

theorem g2_rt2
    (G : Type) [Group G] [Finite G] (K : Subgroup G) (h : Kc3G2Ev ↥K) :
    BT2 K ∧ Lat2 K := by
  obtain ⟨f, hf, -, hmodel⟩ := h
  refine ⟨bt2_of_holds K (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hmodel),
    lat2_of_lattice K ?_⟩
  intro U' hU'
  obtain ⟨K0, hF, hFin, hcp, φ, hcard, -, hres, -⟩ := even_rank_two_residual_G2 hmodel hU'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K0) := finite_modGL
  refine ⟨fun j => ((parabolicSubgroup Tag.G2 K0 {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K0)).map φ.symm.toMonoidHom,
    fun j => ((parabolicRadical Tag.G2 K0 {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K0)).map φ.symm.toMonoidHom, hres, fun j => ?_⟩
  have hPC : ∀ i : Fin Tag.G2.rank,
      parabolicSubgroup Tag.G2 K0 {i} ≤ adjointGroup Tag.G2 K0 := fun i =>
    parabolicSubgroup_le_adjointGroup _ _ _
  have hQC : ∀ i : Fin Tag.G2.rank,
      parabolicRadical Tag.G2 K0 {i} ≤ adjointGroup Tag.G2 K0 := fun i =>
    ((parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})).trans
      (hPC i)
  have key : ∀ i : Fin Tag.G2.rank,
      ParabolicFacts (parabolicSubgroup Tag.G2 K0 {i}) (parabolicRadical Tag.G2 K0 {i}) →
      ParabolicFacts (((parabolicSubgroup Tag.G2 K0 {i}).subgroupOf
          (adjointGroup Tag.G2 K0)).map φ.symm.toMonoidHom)
        (((parabolicRadical Tag.G2 K0 {i}).subgroupOf
          (adjointGroup Tag.G2 K0)).map φ.symm.toMonoidHom) := by
    intro i hi
    refine ParabolicFacts.map ?_ φ.symm.toMonoidHom φ.symm.injective
    refine ParabolicFacts.of_map (adjointGroup Tag.G2 K0).subtype
      (adjointGroup Tag.G2 K0).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (hPC i), Subgroup.map_subgroupOf_eq_of_le (hQC i)]
    exact hi
  refine key (g2Index j) ?_
  rcases G2.fin_two_cases (g2Index j) with h | h
  · rw [h]
    exact G2.parabolicFacts_zero hcard hf
  · rw [h]
    exact G2.parabolicFacts_one hcard hf

theorem kc3ForS'_g2_even
    : Kc3ForS' Kc3G2Ev :=
  kc3ForS'_of_rt2 fun G _ _ K h => g2_rt2 G K h

theorem kc3For_g2_even
    : Kc3For Kc3G2Ev :=
  kc3For_of_simple' isoInv_g2ev kc3ForS'_g2_even

end CFSG.QuasithinUnique.A5
