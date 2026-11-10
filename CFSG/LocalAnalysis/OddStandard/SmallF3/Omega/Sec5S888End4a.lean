module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End2

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

abbrev Mbar {X : Type} [Group X] (M : Subgroup X) : Type :=
  ↥M ⧸ goldschmidtOddCore ↥M

@[expose] def mbarMk {X : Type} [Group X] (M : Subgroup X) : ↥M →* Mbar M :=
  QuotientGroup.mk' (goldschmidtOddCore ↥M)

structure XData {X : Type} [Group X] [Finite X] (S : Sylow 2 X) (V : Subgroup X)
    (W : Fin 4 → Subgroup X) (ρ : Fin 4 → X) : Prop where
  planes : IsPlaneData V W ρ
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq : ∀ a ∈ V, a * a = 1
  le_S : V ≤ (S : Subgroup X)
  normS : ∀ s ∈ (S : Subgroup X), ∀ v ∈ V, s * v * s⁻¹ ∈ V
  closed : ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ V
  centS : ∀ s ∈ (S : Subgroup X), (∀ v ∈ V, s * v = v * s) → s ∈ V
  perm : ∀ g ∈ normalizer (V : Set X), ∀ i, ∃ j, ∀ w ∈ W i, g * w * g⁻¹ ∈ W j

structure IsCaseB {X : Type} [Group X] [Finite X] (S : Sylow 2 X) (V M : Subgroup X) : Prop where
  layer : goldschmidtLayer (Mbar M) = ⊤
  o2 : CFSG.Open.pCore 2 (Mbar M) = ⊥
  comps : ∀ K : Subgroup (Mbar M), IsComponentOf K ⊤ →
    goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K)
  syl : ∃ Ts : Sylow 2 (Mbar M),
    (Ts : Subgroup (Mbar M)) = ((S : Subgroup X).subgroupOf M).map (mbarMk M) ∧
      (V.subgroupOf M).map (mbarMk M) = Omega1 (Ts : Subgroup (Mbar M))
  inj : ∀ x ∈ (S : Subgroup X).subgroupOf M, ∀ y ∈ (S : Subgroup X).subgroupOf M,
    mbarMk M x = mbarMk M y → x = y

theorem xdata_dichotomy (hGold : GoldStmt) {X : Type} [Group X] [Finite X] {S : Sylow 2 X}
    {V : Subgroup X} {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X} (hX : XData S V W ρ) :
    (∃ Nn : Subgroup X, Nn.Normal ∧ Odd (Nat.card Nn) ∧ (V ⊔ Nn).Normal) ∨
      IsCaseB S V (Subgroup.normalClosure (V : Set X)) := by
  have hirr : ∀ U : Subgroup X, U ≤ V →
      (∀ g ∈ normalizer (V : Set X), ∀ u ∈ U, g⁻¹ * u * g ∈ U) → U = ⊥ ∨ U = V :=
    fun U hUV hU => irr_of_planes hX.planes hX.comm U hUV hU
  rcases gold_dichotomy hGold S V hX.le_S hX.comm hX.sq hX.closed hirr with
    h | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4, h5⟩

end CFSG.OddStandard.SmallF3.Omega
