module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.Sporadic.Bridge.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.Sporadic.Bridge

@[expose] def OneClass (G : Type) [Group G] : Prop :=
  ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v

@[expose] def Balanced (G : Type) [Group G] : Prop :=
  ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥

@[expose] def SylowBal (N : Type) [Group N] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) → Balanced G →
    ∀ (S : Sylow 2 G) (T : Sylow 2 N),
      Nonempty ((S : Subgroup G) ≃* (T : Subgroup N)) → Nonempty (G ≃* N)

@[expose] def StageB1 (N Cm : Type) [Group N] [Group Cm] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) → Balanced G →
    ∀ (S : Sylow 2 G) (T : Sylow 2 N),
      Nonempty ((S : Subgroup G) ≃* (T : Subgroup N)) →
      OneClass G ∧ ∃ f : G, orderOf f = 2 ∧ Nonempty (centralizer ({f} : Set G) ≃* Cm)

@[expose] def StageB2 (N Cm : Type) [Group N] [Group Cm] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) → OneClass G →
    ∀ f : G, orderOf f = 2 → Nonempty (centralizer ({f} : Set G) ≃* Cm) → Nonempty (G ≃* N)

@[expose] def StageB2Loc (Cm : Type) [Group Cm] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) → OneClass G →
    ∀ f : G, orderOf f = 2 → Nonempty (centralizer ({f} : Set G) ≃* Cm) →
      ∃ x : ℕ → G, (∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters, wordProd x v = 1) ∧
        x 5 = f

theorem onanSylowInputBal_of_stages {N Cm : Type} [Group N] [Group Cm] (h1 : StageB1 N Cm)
    (h2 : StageB2 N Cm) : SylowBal N := by
  intro G _ _ _ hna hbal S T e
  obtain ⟨hone, f, hf, c⟩ := h1 G hna hbal S T e
  exact h2 G hna hone f hf c

structure AlpFrame {G : Type*} [Group G] (v1 v2 v3 s t : G) : Prop where
  v1_four : v1 ^ 4 = 1
  v2_four : v2 ^ 4 = 1
  v3_four : v3 ^ 4 = 1
  t_two : t ^ 2 = 1
  c12 : v1 * v2 = v2 * v1
  c13 : v1 * v3 = v3 * v1
  c23 : v2 * v3 = v3 * v2
  s_four : s ^ 4 = v1 * v3
  s_t : t⁻¹ * s * t = s⁻¹
  s_v1 : s⁻¹ * v1 * s = v2
  s_v2 : s⁻¹ * v2 * s = v3
  s_v3 : s⁻¹ * v3 * s = v1 * v2⁻¹ * v3
  t_v1 : t⁻¹ * v1 * t = v3⁻¹
  t_v2 : t⁻¹ * v2 * t = v2⁻¹
  t_v3 : t⁻¹ * v3 * t = v1⁻¹

@[expose] def alpV {G : Type*} [Group G] (v1 v2 v3 : G) : Subgroup G := closure {v1, v2, v3}

@[expose] def alpW {G : Type*} [Group G] (v1 v2 v3 : G) : Subgroup G :=
  closure {v1 ^ 2, v2 ^ 2, v3 ^ 2}

@[expose] def alpP {G : Type*} [Group G] (v1 v2 v3 s t : G) : Subgroup G :=
  closure {v1, v2, v3, s, t}

@[expose] def StageA5 (N : Type) [Group N] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (T : Sylow 2 N),
    Nonempty ((S : Subgroup G) ≃* (T : Subgroup N)) →
    ∃ v1 v2 v3 s t : G, AlpFrame v1 v2 v3 s t ∧ alpP v1 v2 v3 s t = (S : Subgroup G) ∧
      orderOf (v1 ^ 2 * v3 ^ 2) = 2

@[expose] def relsM : Set (FreeGroup (Fin 6)) :=
  let a := FreeGroup.of (0 : Fin 6); let b := FreeGroup.of (1 : Fin 6)
  let c := FreeGroup.of (2 : Fin 6); let d := FreeGroup.of (3 : Fin 6)
  let f := FreeGroup.of (4 : Fin 6); let g := FreeGroup.of (5 : Fin 6)
  {a ^ 2, b ^ 2, c ^ 2, d ^ 2, f ^ 2, (a * b) ^ 3, (b * c) ^ 3, (c * d) ^ 8, (a * c) ^ 2,
    (a * d) ^ 2, (a * f) ^ 2, (b * d) ^ 2, (b * f) ^ 2, (c * f) ^ 2, (d * f) ^ 2, g ^ 4,
    (a * f)⁻¹ * g ^ 2, (a * f)⁻¹ * (c * d) ^ 4,
    c * ((d * g * d * g)⁻¹ * c * (d * g * d * g)),
    d * ((c * g * c * g)⁻¹ * d * (c * g * c * g)), (b * c * d * g) ^ 5,
    g * b * (c⁻¹ * g * c) * (b⁻¹ * g * b) * (c⁻¹ * g * c), f⁻¹ * (d * g) ^ 4}

abbrev CModel : Type := PresentedGroup relsM

@[expose] def zIn {G : Type*} [Group G] (x : G) : centralizer ({x} : Set G) :=
  ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

instance zpowers_zIn_normal {G : Type*} [Group G] (x : G) : (zpowers (zIn x)).Normal :=
  normal_of_le_center <| zpowers_le.2 <| Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)

@[expose] def StageB1Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ v1 v2 v3 s t : G, AlpFrame v1 v2 v3 s t → orderOf (v1 ^ 2 * v3 ^ 2) = 2 →
      (∃ P : Sylow 2 G, (P : Subgroup G) = alpP v1 v2 v3 s t) →
      (∀ u w : G, orderOf u = 2 → orderOf w = 2 → IsConj u w) ∧
        ∃ T : Sylow 2 (centralizer ({v1 * v2 ^ 2 * v3⁻¹} : Set G) ⧸
            zpowers (zIn (v1 * v2 ^ 2 * v3⁻¹))),
          Nonempty (↥(T : Subgroup (centralizer ({v1 * v2 ^ 2 * v3⁻¹} : Set G) ⧸
            zpowers (zIn (v1 * v2 ^ 2 * v3⁻¹)))) ≃* GH74.GLS.Bg.TwoGroups.SylSL3_4)

@[expose] def StageB1Ident : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Balanced G → OneClass G →
    ∀ v1 v2 v3 s t : G, AlpFrame v1 v2 v3 s t → orderOf (v1 ^ 2 * v3 ^ 2) = 2 →
      (∃ P : Sylow 2 G, (P : Subgroup G) = alpP v1 v2 v3 s t) →
      Nonempty (centralizer ({v1 ^ 2 * v3 ^ 2} : Set G) ≃* CModel)

theorem stageB1_of_parts {N : Type} [Group N] (hA : StageA5 N) (hL : StageB1Local)
    (hI : StageB1Ident) : StageB1 N CModel := by
  intro G _ _ _ hna hbal S T e
  obtain ⟨v1, v2, v3, s, t, hfr, hP, hf2⟩ := hA G S T e
  have hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = alpP v1 v2 v3 s t := ⟨S, hP.symm⟩
  obtain ⟨hone, -⟩ := hL G hna v1 v2 v3 s t hfr hf2 hSyl
  exact ⟨hone, v1 ^ 2 * v3 ^ 2, hf2, hI G hna hbal hone v1 v2 v3 s t hfr hf2 hSyl⟩

structure OnNativeFacts (N : Type) [Group N] : Prop where
  simple : IsSimpleGroup N
  bridge : Nonempty (N ≃* TauCeti.Sporadic.onanPresentation.Group)
  oneClass : OneClass N
  card_cent : ∀ z : N, orderOf z = 2 → Nat.card (centralizer ({z} : Set N)) = 161280

structure CentFacts (Cm : Type) [Group Cm] : Prop where
  card : Nat.card Cm = 161280
  normal2 : ∀ S : Subgroup Cm, IsPGroup 2 S → S.Normal → Nat.card S ≤ 4
  noncentral : ∃ u : Cm, orderOf u = 2 ∧ u ∉ Subgroup.center Cm

end CFSG.OddStandard.ONanRec
