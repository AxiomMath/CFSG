module

public import CFSG.HardMathSupport.Lang.Triality.HeightLayers
public import CFSG.HardMathSupport.Lang.E27Lie.CocycleCount
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def layerN (k : ℕ) : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  layerSub TwistTag.D4 σ.toRingHom (k + 1)

abbrev LayerCoord (k : ℕ) : Type :=
  Multiplicative (↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)) → K)

@[expose] def layerPhi (k : ℕ) : layerN σ k →* LayerCoord (K := K) k :=
  layerHom TwistTag.D4 σ.toRingHom (k + 1) (by positivity)

@[expose] def layerTau (k : ℕ) : LayerCoord (K := K) k →* LayerCoord (K := K) k :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft σ.toAddMonoidHom
    (↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ))))

@[expose] def betaAut (u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ

theorem mem_layerN {k : ℕ} {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} :
    x ∈ layerN σ k ↔
      (x : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K ((k + 1 : ℕ) : ℤ) :=
  Iff.rfl

theorem layerN_chain (k : ℕ) : layerN σ (k + 1) ≤ layerN σ k := by
  intro x hx
  rw [mem_layerN] at hx ⊢
  unfold heightSeries at hx ⊢
  refine rootSpan_mono (S := {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧
      ((k + 1 + 1 : ℕ) : ℤ) ≤ height γ}) (T := {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧
      ((k + 1 : ℕ) : ℤ) ≤ height γ}) ?_ hx
  intro γ hγ
  refine ⟨hγ.1, hγ.2.1, ?_⟩
  have := hγ.2.2
  push_cast at this ⊢
  linarith

theorem layerN_bot :
    layerN σ (maxHeight TwistTag.D4.tag).toNat = ⊥ := by
  have hdz : (((maxHeight TwistTag.D4.tag).toNat : ℕ) : ℤ) = maxHeight TwistTag.D4.tag :=
    Int.toNat_of_nonneg (by linarith [one_le_maxHeight (τ := TwistTag.D4.tag)])
  have h1 : heightSeries TwistTag.D4.tag K ((((maxHeight TwistTag.D4.tag).toNat + 1 : ℕ)) : ℤ) =
      ⊥ := by
    have := heightSeries_maxHeight_add_one (τ := TwistTag.D4.tag) (R := K)
    push_cast
    rw [hdz]
    exact this
  ext x
  rw [mem_layerN, h1, Subgroup.mem_bot, Subgroup.mem_bot]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem coe_betaAut (u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ((betaAut σ u x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) =
      (u : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom σ.toRingHom)
        (x : ModGL TwistTag.D4.tag K) * (u : ModGL TwistTag.D4.tag K)⁻¹ := rfl

theorem betaAut_mem_layerN {u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K) (k : ℕ)
    {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hx : x ∈ layerN σ k) :
    betaAut σ u x ∈ layerN σ k := by
  rw [mem_layerN] at hx ⊢
  rw [coe_betaAut]
  have hg : Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K ((k + 1 : ℕ) : ℤ) :=
    map_heightSeries_le (Units.map (entrywiseHom σ.toRingHom)) id (fun γ hγ => hγ) (fun γ => rfl)
      (fun γ _ c => ⟨σ c, Units.ext (entrywise_pinnedX σ.toRingHom γ c)⟩) _ hx
  exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hu) _).1 hg

theorem layerN_zero_mem {g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hg : g ∈ layerN σ 0) : (g : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K := by
  rw [mem_layerN] at hg
  have : ((0 + 1 : ℕ) : ℤ) = 1 := by norm_num
  rw [this, heightSeries_one] at hg
  exact hg

theorem layerPhi_conj {k : ℕ} {g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hg : g ∈ layerN σ 0) (x : layerN σ k) :
    ∃ hx : g * (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) * g⁻¹ ∈ layerN σ k,
      layerPhi σ k ⟨g * (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) * g⁻¹, hx⟩ =
        layerPhi σ k x := by
  have hgU := layerN_zero_mem σ hg
  have hx := x.2
  rw [mem_layerN] at hx
  have hmem : g * (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) * g⁻¹ ∈ layerN σ k := by
    rw [mem_layerN]
    exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K _ hgU) _).1 hx
  refine ⟨hmem, ?_⟩
  refine congrArg Multiplicative.ofAdd (funext fun O => ?_)
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  exact rootCoord_conj ⟨hrep.1, by rw [hrep.2.1]; positivity⟩ hgU
    (mem_heightSeries_of_height_eq TwistTag.D4 hrep.2.1 hx)

theorem layerPhi_act {u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K) (k : ℕ)
    (x : layerN σ k) :
    layerPhi σ k ⟨betaAut σ u x, betaAut_mem_layerN σ hu k x.2⟩ =
      layerTau σ k (layerPhi σ k x) := by
  refine congrArg Multiplicative.ofAdd (funext fun O => ?_)
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  exact rootCoord_conj_fieldActor TwistTag.D4 σ σ u hu x _
    ⟨hrep.1, by rw [hrep.2.1]; positivity⟩
    (mem_heightSeries_of_height_eq TwistTag.D4 hrep.2.1 x.2)

theorem layerPhi_triv {k : ℕ} (x : layerN σ k)
    (hx : (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ layerN σ (k + 1)) :
    layerPhi σ k x = 1 := by
  refine congrArg Multiplicative.ofAdd (funext fun O => ?_)
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  rw [mem_layerN] at hx
  have hlt : 0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) := by
    rw [hrep.2.1]; positivity
  have hker : (x : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (coordKerRoots (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)) := by
    refine heightSeries_succ_le_coordKer _ ?_
    rw [hrep.2.1]
    simpa using hx
  exact rootCoord_of_mem_coordKer ⟨hrep.1, hlt⟩ hker

theorem layerPhi_ker {k : ℕ} (x : layerN σ k) (hx : layerPhi σ k x = 1) :
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ layerN σ (k + 1) := by
  have := layerHom_ker_le TwistTag.D4 σ.toRingHom (k + 1) (by positivity)
  exact this ⟨x, hx, rfl⟩

theorem cocycleData_layers {u : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hu : (u : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K) (b : ℕ → ℕ)
    (hb : ∀ k, k < (maxHeight TwistTag.D4.tag).toNat →
      Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
        a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1} ≤ b k) :
    CocycleData (betaAut σ u) (layerN σ) (maxHeight TwistTag.D4.tag).toNat
      (layerPhi σ) (layerTau σ) b where
  chain := layerN_chain σ
  bot := layerN_bot σ
  stable := fun k x hx => betaAut_mem_layerN σ hu k hx
  conj := fun k _ g hg x => layerPhi_conj σ hg x
  act := fun k _ x => layerPhi_act σ hu k x
  triv := fun k _ x hx => layerPhi_triv σ x hx
  ker := fun k _ x hx => layerPhi_ker σ x hx
  bound := hb

end CFSG.HardMathSupport.Lang.E27Lie
