module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Bar

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

@[expose] def DSet (Ω : Set (Subgroup G)) (W : Subgroup G) : Set (Subgroup G) :=
  {T | (∃ J ∈ Ω, IsSylowOf 2 T J) ∧ T ≤ normalizer (W : Set G)}

@[expose] def MGrp (Ω : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  ⨆ (T : Subgroup G) (_ : T ∈ DSet Ω W), T

@[expose] def IsZOf (T : Subgroup G) (z : G) : Prop :=
  ∃ V : Subgroup G, IsDihedralRot V T ∧ z ∈ V ∧ z ≠ 1 ∧ z * z = 1

@[expose] def IsBarOf (W T : Subgroup G) (d : NBar W) : Prop :=
  ∃ V : Subgroup G, IsDihedralRot V T ∧
    ∃ t : normalizer (W : Set G), (t : G) ∈ T ∧ (t : G) ∉ V ∧ d = (t : NBar W)

@[expose] def omegaOne (W : Subgroup G) : Set G :=
  {w | w ∈ W ∧ w * w = 1}

@[expose] def zZero (Ω : Set (Subgroup G)) (W R : Subgroup G) (z : G) : Set G :=
  {x | ∃ T ∈ DSet Ω W, ∃ zT : G, IsZOf T zT ∧
    (∀ r s : NBar W, IsBarOf W R r → IsBarOf W T s → r * s = s * r) ∧ x = z * zT}

structure Sec4Hyp (Ω : Set (Subgroup G)) : Prop where
  h22 : Asc76Lemma22
  hΩ : Assumption41 Ω
  hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R

@[expose] def Lemma411 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Sec4Hyp Ω →
    ∀ S : Subgroup G, IsSylowOf 2 S ⊤ →
      ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected →
      ∀ R : Subgroup G, R ∈ DSet Ω (sec4W Ω S) → ∀ z : G, IsZOf R z →
      (∀ T₁ ∈ DSet Ω (sec4W Ω S), ∀ T₂ ∈ DSet Ω (sec4W Ω S),
          ∃ m ∈ MGrp Ω (sec4W Ω S), T₂ = rightConjugate T₁ m) ∧
        ({w | ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m} =
            omegaOne (sec4W Ω S) \ zZero Ω (sec4W Ω S) R z ∧
          ∀ x ∈ zZero Ω (sec4W Ω S) R z, ∀ m ∈ MGrp Ω (sec4W Ω S), m * x = x * m) ∧
        ∀ t ∈ normalizer (sec4W Ω S : Set G), t * t = 1 →
          ∃ m ∈ MGrp Ω (sec4W Ω S), t * (m⁻¹ * z * m) = m⁻¹ * z * m * t

end CFSG.ComponentClassification.Asc76.Sec4
