module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideKFacts

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Open

structure E27Config (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X) : Prop where
  normal : K.Normal
  simple : IsSimpleGroup K
  nonab : ∃ a b : K, a * b ≠ b * a
  catalog : IsCatalogGroup K
  faithful : Subgroup.centralizer (K : Set X) = ⊥
  elem : IsElemAbelian 3 R
  card_R : Nat.card R = 27
  T_le_R : T ≤ R
  T_le_K : T ≤ K
  card_T : Nat.card T = 9
  z_mem : z ∈ R
  z_not_mem : z ∉ T
  fus : ∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set X), n * r * n⁻¹ ∈ Subgroup.zpowers z
  trans : ∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (R : Set X),
    n * z * n⁻¹ = z ∧ (∀ x ∈ T, n * x * n⁻¹ ∈ T) ∧ n * t * n⁻¹ = s
  sylow : ∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set X)),
    (S : Subgroup _).map (Subgroup.centralizer ({z} : Set X)).subtype = R
  perfect : ∀ D : Subgroup X, D ≤ Subgroup.centralizer ({z} : Set X) → ⁅D, D⁆ = D →
    ¬ 3 ∣ Nat.card D
  central : ∀ t ∈ T, t ≠ 1 → ∃ S : Sylow 3 X, (S : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X)
  dvd81 : 81 ∣ Nat.card X

theorem kFactMSideAlmostSimpleE27_of_config
    (h : ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X),
      E27Config X K R T z → False) :
    CFSG.AGLEmbedding.KFactMSideAlmostSimpleE27 :=
  fun X _ _ K hn hs hna hc hC R T z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    h X K R T z ⟨hn, hs, hna, hc, hC, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

@[expose] def E27AltSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z →
    ∀ n : ℕ, 5 ≤ n → Nonempty (↥K ≃* alternatingGroup (Fin n)) → False

@[expose] def E27LieSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

@[expose] def E27SporSlice : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z →
    ∀ s : TauCeti.SporadicName, Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

theorem kFactMSideAlmostSimpleE27_of_slices (hA : E27AltSlice) (hL : E27LieSlice)
    (hS : E27SporSlice) : CFSG.AGLEmbedding.KFactMSideAlmostSimpleE27 := by
  refine kFactMSideAlmostSimpleE27_of_config fun X _ _ K R T z hc => ?_
  obtain ⟨i, ⟨e⟩⟩ := hc.catalog
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hc.nonab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact hA X K R T z hc n hn ⟨e⟩
  | lie d => exact hL X K R T z hc d ⟨e⟩
  | sporadic s => exact hS X K R T z hc s ⟨e⟩

end CFSG.HardMathSupport.Foote.E27
