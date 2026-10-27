module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

section Vocabulary

variable {G : Type} [Group G]

@[expose] def sec3B (A₁ : Subgroup G) (x : G) : Subgroup G :=
  (normalClosure ((A₁.subgroupOf (centralizer ({x} : Set G)) :
    Subgroup ↥(centralizer ({x} : Set G))) : Set ↥(centralizer ({x} : Set G)))).map
      (centralizer ({x} : Set G)).subtype

@[expose] def sec3F (Q₁ : Subgroup G) : Subgroup G :=
  Quasithin.perfectCore (normalizer (Q₁ : Set G))

end Vocabulary

section Coords


open CFSG.Blueprint.Chevalley in
@[expose] def Sec3Coords {G : Type} [Group G] (A A₁ : Subgroup G) (x : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧
    ∃ φ : ↥A ≃* ↥(adjointGroup .G2 K),
      (A₁.subgroupOf A).map φ.toMonoidHom =
        (RankTwoExceptional.g2LongA2 K).subgroupOf (adjointGroup .G2 K) ∧
      ((zpowers x).subgroupOf A).map φ.toMonoidHom =
        (RankTwoExceptional.g2TorusR K).subgroupOf (adjointGroup .G2 K)

end Coords

@[expose] def Sec3Below (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < n →
    (RankTwoHypNF G' A' → ∀ m : ℕ, 2 ≤ m →
      StatedClassicalModel (rankTwoQuot A') .PSL 3 2 m →
        (standardComponentOddCore G' = ⊥ → m = 2) ∧
        (m = 2 →
          (NativeSporadic.IsSporadic (rankTwoX A' ⧸ center (rankTwoX A')) .Suz ∧
              Nat.card (center (rankTwoX A')) ∣ 3) ∨
            (Nonempty (center A' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A') .He)) ∧
        (standardComponentOddCore G' = ⊥ →
          NativeSporadic.IsSporadic (rankTwoX A') .Suz ∨
            (Nonempty (center A' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
              NativeSporadic.IsSporadic (rankTwoX A') .He))) ∧
    (RankTwoHypNF G' A' → standardComponentOddCore G' = ⊥ →
      RankTwoExceptionalEvenType (rankTwoQuot A') →
        ChevalleyExceptionalModel A' .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A') .Co1)

theorem center_eq_bot_of_rankTwoHypNF {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hH : RankTwoHypNF G A) (hO : standardComponentOddCore G = ⊥) : center G = ⊥ := by
  by_cases hodd : Odd (Nat.card (center G))
  · have h : center G ≤ standardComponentOddCore G := le_sSup ⟨inferInstance, hodd⟩
    rw [hO] at h
    exact le_bot_iff.mp h
  · exfalso
    apply hH.not_normal
    have htight := AS76b.tightlyEmbedded_centralizer hH.standard
    rw [← normalizer_eq_top_iff, ← AS76b.normalizer_centralizer_eq hH.standard, eq_top_iff]
    intro g _
    by_contra hg
    have h := htight.2 g hg
    have hZK : center G ≤ Subgroup.centralizer (A : Set G) := fun z hz =>
      mem_centralizer_iff.mpr fun a _ => (mem_center_iff.mp hz a)
    have hle : center G ≤ Subgroup.centralizer (A : Set G) ⊓
        rightConjugate (Subgroup.centralizer (A : Set G)) g := by
      refine le_inf hZK fun z hz => (mem_rightConjugate_iff _ _ _).mpr ?_
      rw [mem_center_iff.mp hz g, mul_inv_cancel_right]
      exact hZK hz
    exact hodd (h.of_dvd_nat (Subgroup.card_dvd_of_le hle))

theorem card_centralizer_lt_of_rankTwoHypNF {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hH : RankTwoHypNF G A) (hO : standardComponentOddCore G = ⊥) {Q : Subgroup G}
    (hQ : Q ≠ ⊥) : Nat.card (Subgroup.centralizer (Q : Set G)) < Nat.card G := by
  have hZ := center_eq_bot_of_rankTwoHypNF hH hO
  have hne : Subgroup.centralizer (Q : Set G) ≠ ⊤ := by
    intro htop
    apply hQ
    rw [eq_bot_iff, ← hZ]
    intro q hq
    rw [mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (Q : Set G) := htop ▸ mem_top g
    exact (mem_centralizer_iff.mp hg q hq).symm
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)

structure Sec3Pre (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (x : G) : Prop where
  base : Base G A
  le : A₁ ≤ A
  quasisimple : Open.IsQuasisimple A₁
  typeA₁ : TypeL34 (↥A₁ ⧸ center ↥A₁)
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  elemR : IsElemAbelian 2 R
  four_le : 4 ≤ Nat.card R
  type : TypeG24 (rankTwoQuot A)
  center_eq : center A = ⊥
  ne : A₁ ≠ A
  order_x : orderOf x = 3
  center_A₁ : centerIn A₁ = zpowers x
  below : Sec3Below (Nat.card G)
  layer : AS76b.layerCentralizer A (zpowers x) = A₁
  config : ∃ (D : RankTwoExceptional.ExcModel A) (g₀ : G) (T₀ : Subgroup G),
    RankTwoExceptional.Config814 D g₀ R T₀ (zpowers x)
  coords : Sec3Coords A A₁ x

structure Sec3Setting (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) (x : G) : Prop extends Sec3Pre G A A₁ R x where
  frame : Frame G A A₁ R g E F

@[expose] def Step31Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (x : G), Sec3Pre G A A₁ R x →
    standardComponentIsStandard (A₁.subgroupOf (centralizer ({x} : Set G))) ∧
      ¬ (A₁.subgroupOf (centralizer ({x} : Set G))).Normal

@[expose] def Step31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (x : G), Sec3Pre G A A₁ R x →
    centerIn (sec3B A₁ x) = zpowers x ∧ commutator ↥(sec3B A₁ x) = ⊤ ∧
      IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz

structure Sec3Suz (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) (x : G) (Zs P T Q B₀ : Subgroup G) (z y : G) : Prop where
  setting : Sec3Setting G A A₁ R g E F x
  R_le : R ≤ sec3B A₁ x
  Zs_eq : Zs = sec2Z A₁ E F
  Zs_card : Nat.card Zs = 4
  P_eq : P = pCoreOf 2 (sec3B A₁ x ⊓ normalizer (E : Set G))
  T_le : T ≤ sec3B A₁ x
  T_two : IsPGroup 2 T
  P_le : P ≤ T
  F_le : F ≤ T
  Q_le : Q ≤ T
  q8 : IsQ8Cube Q
  Q_center : centerIn Q = zpowers z
  T_center : centerIn T = zpowers z
  z_mem : z ∈ Zs
  y_Q : y ∈ normalizer (Q : Set G)
  Q_unique : ∀ Q' : Subgroup G, IsQ8Cube Q' → Q' ≤ T → y ∈ normalizer (Q' : Set G) → Q' = Q
  B₀_eq : B₀ = ⁅sec3B A₁ x ⊓ centralizer ({z} : Set G), sec3B A₁ x ⊓ centralizer ({z} : Set G)⁆
  y_mem : y ∈ sec3B A₁ x ⊓ normalizer (R : Set G)
  y_three : ∃ k : ℕ, y ^ 3 ^ k = 1
  y_trans : ∀ r ∈ R, r ≠ 1 → y⁻¹ * r * y ≠ r
  P_cover : ∀ e ∈ E, e ∉ A₁ → ∃ p ∈ P, e ∈ rightConjugate R p
  P_cent : P ≤ centralizer ((E ⊓ A₁ : Subgroup G) : Set G)
  P_cE : P ⊓ centralizer (E : Set G) = E
  P_card : Nat.card P = 2 ^ 10
  P_comm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ E ⊓ A₁
  T_P : T ≤ normalizer (P : Set G)
  T_PF : T ≤ normalizer ((P ⊔ F : Subgroup G) : Set G)
  T_Q : T ≤ normalizer (Q : Set G)
  B_suz : IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz
  B_center : centerIn (sec3B A₁ x) = zpowers x
  T_card : Nat.card T = 2 ^ 13
  Q_EA : (E ⊓ A₁ ⊓ Q).relIndex (E ⊓ A₁) = 2
  B_perf : commutator ↥(sec3B A₁ x) = ⊤

@[expose] def Step3Suz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (x : G),
    Sec3Pre G A A₁ R x → centerIn (sec3B A₁ x) = zpowers x →
    commutator ↥(sec3B A₁ x) = ⊤ → IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz →
      ∃ (g' : G) (E' F' : Subgroup G) (Zs P T Q B₀ : Subgroup G) (z y : G),
        Sec3Suz G A A₁ R g' E' F' x Zs P T Q B₀ z y

@[expose] def Step18G24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z₀ y : G), Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z₀ y →
    ∀ z ∈ E, orderOf z = 2 →
      (∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ centralizer ({z} : Set G)) →
      (∀ h : G, z ∉ rightConjugate R h) →
        AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥

structure Sec3D (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) (x : G) (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U : Subgroup G) :
    Prop where
  suz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y
  D_eq : D = pCoreOf 2 (A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G))
  J_le : J ≤ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)
  J_iso : Nonempty (↥J ≃* SL(2, GaloisField 2 2))
  J_comm : J ≤ centralizer ({x} : Set G)
  T₁_sylow : IsSylowOf 2 (T ⊓ J) J
  I_eq : A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) = D ⊔ (J ⊔ zpowers x)
  center_D : E ⊓ A = centerIn D
  D_elem : ∀ d ∈ D, ∀ d' ∈ D, d * d ∈ E ⊓ A ∧ d * d' * d⁻¹ * d'⁻¹ ∈ E ⊓ A
  D_card : (E ⊓ A).relIndex D = 4 ^ 3
  U_le : U ≤ D
  center_DJ : ∀ d ∈ D ⊔ J, (∀ j ∈ D ⊔ J, d * j * d⁻¹ * j⁻¹ ∈ E ⊓ A) ↔ d ∈ U ⊔ (E ⊓ A)
  comm_DU : ⁅D, U⁆ = E ⊓ A

@[expose] def Step32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G), Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y →
      ∃ D J U : Subgroup G, Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U

structure Sec3Q0 (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) (x : G) (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G) :
    Prop where
  dData : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U
  V₀_eq : (V₀ : Set G) = {d | d ∈ D ∧ ∀ t ∈ T ⊓ J, d * t * d⁻¹ * t⁻¹ ∈ E ⊓ A}
  V_eq : V = ⁅V₀, zpowers x⁆
  Q₀_le : Q₀ ≤ V
  x_Q₀ : x ∈ normalizer (Q₀ : Set G)
  Q₀_iso : Nonempty (↥Q₀ ≃* QuaternionGroup 2)
  center_Q₀ : centerIn Q₀ = centerIn Q
  unique : ∀ Q' : Subgroup G, Q' ≤ V → x ∈ normalizer (Q' : Set G) →
    Nonempty (↥Q' ≃* QuaternionGroup 2) → centerIn Q' = centerIn Q → Q' = Q₀

@[expose] def Step36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U : Subgroup G),
    Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U →
      ∃ V₀ V Q₀ : Subgroup G, Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀

@[expose] def Step37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      T ≤ centralizer (Q₀ : Set G) ∧ CFSG.IsExtraspecialPGroup 2 ↥(Q₀ ⊔ Q) ∧
      Nat.card ↥(Q₀ ⊔ Q) = 2 ^ 9 ∧ IsSylowOf 2 Q₀ (centralizer (Q : Set G)) ∧
      B₀ ≤ centralizer (Q₀ : Set G)

@[expose] def Step38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q) ∧
      (∃ φ : ↥(sec3F (Q₀ ⊔ Q)) →* ↥(timmesfeldOmegaPlus 4), Function.Surjective φ ∧
        φ.ker = ((Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
          centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))).subgroupOf (sec3F (Q₀ ⊔ Q))) ∧
      ∀ B : Subgroup G, zpowers z ≤ B → B < Q₀ ⊔ Q →
        sec3F (Q₀ ⊔ Q) ≤ normalizer (B : Set G) → ∀ n : ℕ,
          ∃ k ∈ (derivedSeries ↥(sec3F (Q₀ ⊔ Q)) n).map (sec3F (Q₀ ⊔ Q)).subtype,
            ∃ w ∈ Q₀ ⊔ Q, k⁻¹ * w * k * w⁻¹ ∉ B

@[expose] def Step39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
    AS76b.oddCoreIn (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) = ⊥ →
      ∃ φ : ↥(normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) →* ↥(timmesfeldOmegaPlus 4),
        Function.Surjective φ ∧
        φ.ker = ((Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G))).subgroupOf
          (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G))

@[expose] def Step312 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      (∀ h ∈ centralizer ({z} : Set G),
        1 < Open.pRank 2 ((Q₀ ⊔ Q) ⊓ rightConjugate (Q₀ ⊔ Q) h) →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q) ∧
      ∃ T' : Subgroup G, IsSylowOf 2 T' (centralizer ({z} : Set G)) ∧ Q₀ ⊔ Q ≤ T' ∧
        ∀ h ∈ centralizer ({z} : Set G), rightConjugate (Q₀ ⊔ Q) h ≤ T' →
          rightConjugate (Q₀ ⊔ Q) h = Q₀ ⊔ Q

@[expose] def Sec3ZNotPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
    centralizer ({z} : Set G) ≤
      normalizer ((Q₀ ⊔ Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) →
      ∀ h : G, z ∉ rightConjugate R h

@[expose] def OmegaPlus8Simple : Prop :=
  IsSimpleGroup ↥(timmesfeldOmegaPlus 4) ∧
    ∃ a b : ↥(timmesfeldOmegaPlus 4), a * b ≠ b * a

end CFSG.ComponentClassification.AS81
