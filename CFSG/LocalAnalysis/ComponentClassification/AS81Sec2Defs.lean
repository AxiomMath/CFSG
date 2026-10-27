module

public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Vocabulary

variable {G : Type} [Group G]

@[expose] def oUpperTwo (X : Subgroup G) : Subgroup G :=
  closure {x | x ∈ X ∧ Odd (orderOf x)}

@[expose] def centralizerMod (X Y Z : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ normalizer (Z : Set G) ∧ ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ Z}
  mul_mem' := by
    rintro a b ⟨haX, haN, ha⟩ ⟨hbX, hbN, hb⟩
    refine ⟨X.mul_mem haX hbX, Subgroup.mul_mem _ haN hbN, fun y hy => ?_⟩
    have h1 := hb y hy
    have h2 := (mem_normalizer_iff.mp (inv_mem hbN) _).mp (ha y hy)
    have : y⁻¹ * (a * b)⁻¹ * y * (a * b) =
        (y⁻¹ * b⁻¹ * y * b) * (b⁻¹ * (y⁻¹ * a⁻¹ * y * a) * b⁻¹⁻¹) := by group
    rw [this]
    exact Z.mul_mem h1 h2
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haX, haN, ha⟩
    refine ⟨X.inv_mem haX, inv_mem haN, fun y hy => ?_⟩
    have h := (mem_normalizer_iff.mp haN _).mp (Z.inv_mem (ha y hy))
    have : y⁻¹ * a⁻¹⁻¹ * y * a⁻¹ = a * (y⁻¹ * a⁻¹ * y * a)⁻¹ * a⁻¹ := by group
    rw [this]
    exact h

theorem mem_centralizerMod {X Y Z : Subgroup G} {x : G} :
    x ∈ centralizerMod X Y Z ↔
      x ∈ X ∧ x ∈ normalizer (Z : Set G) ∧ ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ Z :=
  Iff.rfl

@[expose] def conjClosure (X P : Subgroup G) : Subgroup G :=
  ⨆ p : P, rightConjugate X p

@[expose] def conjSet (X P : Subgroup G) : Set (Subgroup G) :=
  {V | ∃ p ∈ P, V = rightConjugate X p}

@[expose] def IsElemQuot (X Y : Subgroup G) (n : ℕ) : Prop :=
  Y ≤ X ∧ Y.relIndex X = n ∧ ∀ a ∈ X, ∀ b ∈ X, a * a ∈ Y ∧ a * b * a⁻¹ * b⁻¹ ∈ Y

@[expose] def planes (E F : Subgroup G) : Set (Subgroup G) :=
  {V | ∃ h : G, V = rightConjugate E h ∨ V = rightConjugate F h}

@[expose] def InducesA5 (N : Subgroup G) (Ps : Set (Subgroup G)) : Prop :=
  Nat.card Ps = 5 ∧ (∀ n ∈ N, ∀ V ∈ Ps, rightConjugate V n ∈ Ps) ∧
    Nat.card {σ : Equiv.Perm Ps |
      ∃ n ∈ N, ∀ V : Ps, ((σ V : Ps) : Subgroup G) = rightConjugate (V : Subgroup G) n} = 60

@[expose] def IsQ8Cube [Finite G] (Q : Subgroup G) : Prop :=
  CFSG.IsExtraspecialPGroup 2 Q ∧ Nat.card Q = 2 ^ 7 ∧
    ¬ ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian 2 U ∧ Nat.card U = 16

@[expose] def ActsAsF4Scalar (x : G) (S Z : Subgroup G) : Prop :=
  x ∈ normalizer (S : Set G) ∧ x ∈ normalizer (Z : Set G) ∧
    ∀ s ∈ S, s * (x⁻¹ * s * x) * (x⁻¹ * x⁻¹ * s * x * x) ∈ Z

end Vocabulary

@[expose] def qMinus (v : Fin 6 → ZMod 2) : ZMod 2 :=
  v 0 * v 1 + v 2 * v 3 + v 4 * v 4 + v 4 * v 5 + v 5 * v 5

structure Sec2Setting (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F : Subgroup G) : Prop where
  frame : Frame G A A R g E F
  type : TypeL34 (rankTwoQuot A)
  odd : Odd (Nat.card (center A))
  below : L34GeneralBelow (Nat.card G)

section Notation

variable {G : Type} [Group G]

@[expose] def sec2Z (A E F : Subgroup G) : Subgroup G := A ⊓ centerIn (E ⊔ F)

@[expose] def sec2P (E : Subgroup G) : Subgroup G :=
  ABGTheoremB.pCoreIn 2 (normalizer (E : Set G))

@[expose] def sec2S (A R E F : Subgroup G) : Subgroup G :=
  F ⊔ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)

@[expose] def sec2H (E F : Subgroup G) : Subgroup G := sec2P E ⊔ sec2P F

@[expose] def sec2F0 (A E : Subgroup G) (x : G) : Subgroup G :=
  (E ⊓ A) ⊔ (rightConjugate E x ⊓ sec2P E)

@[expose] def sec2K (E : Subgroup G) : Subgroup G := oUpperTwo (normalizer (sec2P E : Set G))

@[expose] def sec2T (E T₀ : Subgroup G) : Subgroup G := T₀ ⊓ sec2K E

@[expose] def sec2M (Q T : Subgroup G) : Subgroup G :=
  ⨆ n : normalizer (Q : Set G), rightConjugate T n

@[expose] def Sec2UY (A R E F : Subgroup G) (u y : G) : Prop :=
  u ∈ A ⊓ normalizer (sec2S A R E F : Set G) ∧ orderOf u = 3 ∧ (∃ e ∈ E, u⁻¹ * e * u ≠ e) ∧
    y ∈ sec2H E F ⊓ normalizer (R : Set G) ⊓ centralizer ({u} : Set G) ∧ orderOf y = 3

end Notation

structure Sec2Data (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F T₀ : Subgroup G) (u y : G) : Prop where
  setting : Sec2Setting G A R g E F
  le : sec2P E ⊔ sec2S A R E F ≤ T₀
  sylow : IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G))
  uy : Sec2UY A R E F u y

structure Sec2Q (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F T₀ Q : Subgroup G) (u y z : G) : Prop where
  data : Sec2Data G A R g E F T₀ u y
  order : orderOf z = 2
  center : centerIn (sec2T E T₀) = zpowers z
  q8 : IsQ8Cube Q
  le : Q ≤ sec2T E T₀
  mem_normalizer : y ∈ normalizer (Q : Set G)
  unique : ∀ Q' : Subgroup G, IsQ8Cube Q' → Q' ≤ sec2T E T₀ → y ∈ normalizer (Q' : Set G) →
    Q' = Q
  le_HT : Q ≤ sec2H E F ⊔ sec2T E T₀
  HT_le : sec2H E F ⊔ sec2T E T₀ ≤ normalizer (Q : Set G)
  index : (E ⊓ A ⊓ Q).relIndex (E ⊓ A) = 2

@[expose] def Step21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (sec2P E ⊔ F) ⊓ centralizer (E : Set G) = E ∧
      IsElemQuot (sec2P E) E 16 ∧
      AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (sec2P E : Set G) ∧
      sec2P E ⊓ AS76b.oddCoreIn (centralizer (E : Set G)) = ⊥ ∧
      sec2P E ⊔ AS76b.oddCoreIn (centralizer (E : Set G)) ≤ normalizer (E : Set G) ∧
      normalizer (E : Set G) ≤
        normalizer ((sec2P E ⊔ AS76b.oddCoreIn (centralizer (E : Set G)) : Subgroup G) : Set G) ∧
      normalizer (E : Set G) = sec2P E ⊔ AS76b.oddCoreIn (centralizer (E : Set G)) ⊔
        (normalizer (E : Set G) ⊓ normalizer (R : Set G)) ∧
      ((sec2P E ⊔ AS76b.oddCoreIn (centralizer (E : Set G))) ⊓ centralizer (E : Set G)).relIndex
        (sec2P E ⊔ AS76b.oddCoreIn (centralizer (E : Set G))) = 16 ∧
      IsElemQuot (sec2S A R E F ⊓ sec2P E) E 4 ∧
      IsElemQuot (sec2S A R E F) E 16

@[expose] def Step22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (sec2P E ⊔ sec2S A R E F) ⊓ normalizer (F : Set G) = sec2S A R E F ∧
      Nat.card (conjSet F (sec2P E)) = 4 ∧
      IsSylowOf 2 (sec2S A R E F)
        (centralizer (sec2Z A E F : Set G) ⊓ centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓
          normalizer (E : Set G) ⊓ normalizer (F : Set G))

@[expose] def Step22iv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F → 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))

@[expose] def Step23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F → ∀ x ∈ sec2P F, x ∉ sec2S A R E F →
      rightConjugate E x ⊓ E = sec2Z A E F ∧ sec2S A R E F = E ⊔ rightConjugate E x ∧
      sec2P E ⊓ sec2S A R E F = E ⊔ sec2F0 A E x ∧
      IsElemAbelian 2 (sec2F0 A E x) ∧ Nat.card (sec2F0 A E x) = 64 ∧
      (∀ U : Subgroup G, U ≤ sec2P E ⊓ sec2S A R E F → IsElemAbelian 2 U →
        U ≤ E ∨ U ≤ sec2F0 A E x) ∧
      conjSet F (sec2H E F) = insert (sec2F0 A E x) (conjSet F (sec2P E)) ∧
      conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)) ∧
      {V | V ∈ planes E F ∧ V ≤ sec2S A R E F} = conjSet F (sec2H E F) ∪ conjSet E (sec2H E F) ∧
      (∀ n ∈ normalizer (sec2S A R E F : Set G),
        (fun V => rightConjugate V n) '' conjSet F (sec2H E F) = conjSet F (sec2H E F) ∨
          (fun V => rightConjugate V n) '' conjSet F (sec2H E F) = conjSet E (sec2H E F)) ∧
      InducesA5 (sec2H E F) (conjSet E (sec2H E F))

@[expose] def Step24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      Nat.card (sec2Z A E F) = 4 ∧ centerIn (sec2S A R E F) = sec2Z A E F ∧
      ⁅sec2S A R E F, sec2S A R E F⁆ = sec2Z A E F ∧
      ∀ s ∈ sec2S A R E F, s * s ∈ sec2Z A E F

@[expose] def Step25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      {x | x ∈ sec2P E ⊔ sec2S A R E F ∧ ∀ y ∈ sec2P E ⊔ sec2S A R E F,
        x⁻¹ * y⁻¹ * x * y ∈ sec2Z A E F} = ((E ⊓ A : Subgroup G) : Set G)

@[expose] def Step26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (∀ s ∈ sec2S A R E F, s ∉ sec2Z A E F →
        {c | ∃ t ∈ sec2S A R E F, c = s⁻¹ * t⁻¹ * s * t} = (sec2Z A E F : Set G)) ∧
      sec2S A R E F ≤ sec2H E F ∧
      (∃ φ : ↥(sec2H E F) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
        φ.ker = (sec2S A R E F).subgroupOf (sec2H E F)) ∧
      sec2H E F ⊓ centralizer (sec2S A R E F : Set G) = sec2Z A E F ∧
      IsSylowOf 2 (sec2Z A E F) (centralizer (sec2S A R E F : Set G)) ∧
      IsSylowOf 2 (sec2S A R E F)
        (centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F) (sec2Z A E F)) ∧
      (∃ φ : ↥(sec2H E F) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ φ.ker = (sec2S A R E F).subgroupOf (sec2H E F) ∧
        ∃ (S₂ S₃ : Subgroup G) (ψ₂ ψ₃ : G → (Fin 5 → ZMod 2)),
          S₂ ⊔ S₃ = sec2S A R E F ∧ S₂ ⊓ S₃ = sec2Z A E F ∧
          ∀ i ∈ ({(S₂, ψ₂), (S₃, ψ₃)} : Set (Subgroup G × (G → (Fin 5 → ZMod 2)))),
            sec2Z A E F ≤ i.1 ∧ i.1 ≤ sec2S A R E F ∧
            (∀ a ∈ i.1, ∀ b ∈ i.1, i.2 (a * b) = i.2 a + i.2 b) ∧
            (∀ a ∈ i.1, i.2 a = 0 ↔ a ∈ sec2Z A E F) ∧
            (∀ a ∈ i.1, ∑ k, i.2 a k = 0) ∧
            (∀ v : Fin 5 → ZMod 2, ∑ k, v k = 0 → ∃ a ∈ i.1, i.2 a = v) ∧
            ∀ h : ↥(sec2H E F), ∀ a ∈ i.1, (h : G) * a * (h : G)⁻¹ ∈ i.1 ∧
              i.2 ((h : G) * a * (h : G)⁻¹) =
                fun k => i.2 a (((φ h : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ k)) ∧
      sec2H E F ≤ normalizer (sec2S A R E F : Set G) ∧
      normalizer (sec2S A R E F : Set G) ≤ normalizer (sec2H E F : Set G)

@[expose] def Step26ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (∀ t ∈ normalizer (sec2S A R E F : Set G), t ∉ sec2S A R E F → t * t ∈ sec2S A R E F →
        16 ≤ Nat.card (⁅sec2S A R E F, zpowers t⁆ ⊔ sec2Z A E F : Subgroup G)) ∧
      (∀ D : Subgroup G, D ≤ normalizer (sec2S A R E F : Set G) →
        (∀ a ∈ D, ∀ b ∈ D, a * a ∈ sec2S A R E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2S A R E F) →
        4 ≤ (D ⊓ sec2S A R E F).relIndex D →
        ∃ d ∈ D, 64 ≤ Nat.card (⁅sec2S A R E F, zpowers d⁆ ⊔ sec2Z A E F : Subgroup G)) ∧
      ∀ D : Subgroup G, D ≤ normalizer (sec2S A R E F : Set G) →
        (∀ a ∈ D, ∀ b ∈ D, a * a ∈ sec2S A R E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2S A R E F) →
        (D ⊓ sec2S A R E F).relIndex D ≤ 8

@[expose] def Step27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      (∃ u y : G, Sec2UY A R E F u y) ∧
      ∀ u y : G, Sec2UY A R E F u y → ∃ x : G, orderOf x = 3 ∧ (u = x * y ∨ u = x * y⁻¹) ∧
        ActsAsF4Scalar x (sec2S A R E F) (sec2Z A E F) ∧
        closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * x⁻¹ * w * x} = sec2Z A E F ∧
        x ∈ normalizer (sec2H E F : Set G) ∧
        ∀ h ∈ sec2H E F, x⁻¹ * h⁻¹ * x * h ∈ sec2S A R E F

@[expose] def Step28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F → ∀ T₀ : Subgroup G,
      IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G)) →
      (∀ U : Subgroup G, sec2Z A E F ≤ U → U ≤ T₀ →
        (∀ a ∈ U, ∀ b ∈ U, a * a ∈ sec2Z A E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2Z A E F) →
        Nat.card (sec2S A R E F) ≤ Nat.card U → U = sec2S A R E F) ∧
      IsSylowOf 2 T₀ ⊤ ∧ normalizer (T₀ : Set G) ≤ normalizer (sec2Z A E F : Set G)

@[expose] def Step29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F → ∀ x ∈ sec2P F, x ∉ sec2S A R E F →
      {V | V ∈ planes E F ∧ V ≤ sec2P E} =
        insert E (conjSet (sec2F0 A E x) (normalizer (E : Set G) ⊓ normalizer (sec2P E : Set G))) ∧
      Nat.card {V | V ∈ planes E F ∧ V ≤ sec2P E} = 6 ∧
      IsSylowOf 2 (sec2P E) (centralizer ((E ⊓ A : Subgroup G) : Set G)) ∧
      ∀ V₁ ∈ {V | V ∈ planes E F ∧ V ≤ sec2P E}, ∀ V₂ ∈ {V | V ∈ planes E F ∧ V ≤ sec2P E},
        ∃ n ∈ normalizer (sec2P E : Set G), rightConjugate V₁ n = V₂

@[expose] def Step211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ≤ sec2K E ∧
      (sec2P E ⊔ AS76b.oddCoreIn (sec2K E)).relIndex (sec2K E) = 1080 ∧
      ⁅sec2K E, sec2K E⁆ ⊔ (sec2P E ⊔ AS76b.oddCoreIn (sec2K E)) = sec2K E ∧
      (∀ u y : G, Sec2UY A R E F u y → ∀ k ∈ sec2K E,
        y⁻¹ * k⁻¹ * y * k ∈ sec2P E ⊔ AS76b.oddCoreIn (sec2K E)) ∧
      (∀ u y : G, Sec2UY A R E F u y → ∀ r ∈ R, r ≠ 1 → y⁻¹ * r * y ≠ r) ∧
      centralizerMod (sec2K E) (sec2P E) (E ⊓ A) = sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ∧
      (∀ B : Subgroup G, E ⊓ A ≤ B → B ≤ sec2P E → sec2K E ≤ normalizer (B : Set G) →
        B = E ⊓ A ∨ B = sec2P E) ∧
      (∃ φ : ↥(sec2K E) →* alternatingGroup (Fin 6), Function.Surjective φ ∧
        φ.ker = (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E)) ∧
      ∀ B : Subgroup G, B ≤ E ⊓ A → sec2K E ≤ normalizer (B : Set G) → B = ⊥ ∨ B = E ⊓ A

@[expose] def Step211Natural : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
      ∃ (φ : ↥(sec2K E) →* alternatingGroup (Fin 6)) (θ : (Fin 6 → ZMod 2) → G),
        Function.Surjective φ ∧
        φ.ker = (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)).subgroupOf (sec2K E) ∧
        (∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → θ (v + w) = θ v * θ w) ∧
        (∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → θ v ∈ E ⊓ A) ∧
        (∀ a ∈ E ⊓ A, ∃ v : Fin 6 → ZMod 2, ∑ i, v i = 0 ∧ θ v = a) ∧
        (∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → (θ v = 1 ↔ v = 0 ∨ v = fun _ => 1)) ∧
        ∀ k : ↥(sec2K E), ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
          (k : G) * θ v * (k : G)⁻¹ =
            θ (fun i => v (((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))⁻¹ i))

@[expose] def Step212 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec2Setting G A R g E F →
    (∃ T₀ : Subgroup G, sec2P E ⊔ sec2S A R E F ≤ T₀ ∧
      IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G))) ∧
    ∀ T₀ : Subgroup G, sec2P E ⊔ sec2S A R E F ≤ T₀ →
    IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G)) →
      IsSylowOf 2 T₀ ⊤ ∧
      sec2P E ⊔ sec2S A R E F ≤ sec2T E T₀ ∧
      (∃ x : G, orderOf x = 3 ∧ ActsAsF4Scalar x (sec2S A R E F) (sec2Z A E F) ∧
        closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * x⁻¹ * w * x} = sec2Z A E F ∧
        x ∈ normalizer (sec2H E F : Set G) ∧
        (∀ h ∈ sec2H E F, x⁻¹ * h⁻¹ * x * h ∈ sec2S A R E F) ∧
        ∃ φ : ↥(sec2H E F ⊔ zpowers x ⊔ sec2T E T₀) →*
            Equiv.Perm (Fin 3) × alternatingGroup (Fin 5),
          Function.Surjective φ ∧
            φ.ker = (sec2S A R E F).subgroupOf (sec2H E F ⊔ zpowers x ⊔ sec2T E T₀)) ∧
      (Subgroup.upperCentralSeries (sec2T E T₀) 2).map (sec2T E T₀).subtype = sec2Z A E F ∧
      centerIn (sec2T E T₀) ≠ sec2Z A E F ∧
      T₀ ≤ normalizer (sec2P E : Set G)

@[expose] def Sec2LocalQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ : Subgroup G) (u y : G),
    Sec2Data G A R g E F T₀ u y →
      ∃ Q : Subgroup G, IsQ8Cube Q ∧ Q ≤ sec2T E T₀ ∧ y ∈ normalizer (Q : Set G) ∧
        (∀ Q' : Subgroup G, IsQ8Cube Q' → Q' ≤ sec2T E T₀ → y ∈ normalizer (Q' : Set G) →
          Q' = Q) ∧
        Q ≤ sec2H E F ⊔ sec2T E T₀ ∧ sec2H E F ⊔ sec2T E T₀ ≤ normalizer (Q : Set G) ∧
        (E ⊓ A ⊓ Q).relIndex (E ⊓ A) = 2

@[expose] def Step215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ Q : Subgroup G)
    (u y z : G), Sec2Q G A R g E F T₀ Q u y z →
      IsSylowOf 2 (sec2T E T₀) (sec2K E) ∧
      E ⊓ A ⊓ Q = (Subgroup.upperCentralSeries (sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓ (E ⊓ A) ∧
      sec2K E ⊓ centralizer ({z} : Set G) ≤ normalizer (Q : Set G)

@[expose] def Step216 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ Q : Subgroup G)
    (u y z : G), Sec2Q G A R g E F T₀ Q u y z →
      ∃ (ψ : G → (Fin 6 → ZMod 2))
        (ρ : ↥(sec2M Q (sec2T E T₀)) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))),
        (∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b) ∧
        (∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v) ∧
        (∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z) ∧
        (∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) ∧
        (∀ m : ↥(sec2M Q (sec2T E T₀)), ∀ a ∈ Q, ψ ((m : G) * a * (m : G)⁻¹) = ρ m (ψ a)) ∧
        ρ.range = timmesfeldOmega qMinus ∧
        ρ.ker = (Q ⊔ AS76b.oddCoreIn (sec2M Q (sec2T E T₀) ⊓ centralizer (Q : Set G))).subgroupOf
          (sec2M Q (sec2T E T₀))

@[expose] def Step218 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ Q : Subgroup G)
    (u y z : G), Sec2Q G A R g E F T₀ Q u y z →
      ∀ c ∈ centralizer ({z} : Set G), 1 < Open.pRank 2 (Q ⊓ rightConjugate Q c) →
        rightConjugate Q c = Q

@[expose] def Step219 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ Q : Subgroup G)
    (u y z : G), Sec2Q G A R g E F T₀ Q u y z →
      ∀ c ∈ centralizer ({z} : Set G), rightConjugate Q c ≤ normalizer (Q : Set G) →
        rightConjugate Q c = Q

@[expose] def SuzRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    S.width = 3 → (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q → IsSporadic G .Suz

end CFSG.ComponentClassification.AS81
