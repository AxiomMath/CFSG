module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def LabelUniqAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K : Subgroup G) (lab₁ lab₂ : GLALabel), 4 ≤ evenRank ↥K → LabelOf K lab₁ → LabelOf K lab₂ →
    lab₁ = lab₂ ∨ ((lab₁.tag = .B ∨ lab₁.tag = .C) ∧ (lab₂.tag = .B ∨ lab₂.tag = .C) ∧
      lab₁.rank = lab₂.rank ∧ lab₁.n = lab₂.n)

@[expose] def ETable (lab : GLALabel) (c : Prop) (e : ℕ) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .D) → 2 ≤ lab.n → e = lab.rank) ∧
  (lab.tag = .F4 → 2 ≤ lab.n → e = 4) ∧ (lab.tag = .E7 → 2 ≤ lab.n → e = 7) ∧ (lab.tag = .E8 → 2 ≤ lab.n → e = 8) ∧
  (lab = ⟨.A, 5, 2⟩ → c → e = 4) ∧ (lab = ⟨.E6, 0, 2⟩ → c → e = 5) ∧
  (lab = ⟨.A, 8, 1⟩ → e = 4) ∧ (lab = ⟨.E6, 0, 1⟩ → e = 4) ∧
  ((lab.tag = .twA ∧ lab.rank = 5) → 2 ≤ lab.n → c → e = 4) ∧ (lab.tag = .twE6 → 2 ≤ lab.n → c → e = 5) ∧
  ((lab.tag = .A ∧ lab.rank = 6) → 2 ≤ lab.n → 5 ≤ e)

@[expose] def ETableAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K : Subgroup G) (lab : GLALabel), LabelOf K lab → ETable lab (Subgroup.center ↥K = ⊥) (evenRank ↥K)

@[expose] def I61At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K : Subgroup G) (lab : GLALabel), IsChev2 K → LabelOf K lab →
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) → 3 ∣ Nat.card (Subgroup.center ↥K) →
      (2 ≤ lab.n → Nat.card (Subgroup.center ↥K) = 3) ∧ Odd lab.n) ∧
    ((∃ p : ℕ, List110 p lab (Subgroup.center ↥K = ⊥)) → Subgroup.center ↥K ≠ ⊥ →
      ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) ∧ 3 ∣ Nat.card (Subgroup.center ↥K))

@[expose] def FieldRel (p : ℕ) (labK labJ : GLALabel) : Prop :=
  labK.n ∣ labJ.n ∨ (labK.n = p * labJ.n ∧ ((labK.tag = labJ.tag ∧ labK.rank = labJ.rank) ∨
    (p = 3 ∧ labK.tag = .D ∧ labK.rank = 4 ∧ labJ.tag = .triD4)))

@[expose] def canonLabel (lab : GLALabel) : GLALabel :=
  match lab.tag with
  | .C => ⟨.B, lab.rank, lab.n⟩
  | .D => if lab.rank = 3 then ⟨.A, 3, lab.n⟩ else lab
  | .twD => if lab.rank = 3 then ⟨.twA, 3, lab.n⟩ else if lab.rank = 2 then ⟨.A, 1, 2 * lab.n⟩ else lab
  | .B2der => ⟨.B, 2, 1⟩
  | .G2der => ⟨.G2, 0, 1⟩
  | .twF4der => ⟨.twF4, 0, 1⟩
  | _ => lab

@[expose] def I1441At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (K J : Subgroup G) (y : G) (labK labJ : GLALabel), p.Prime → p ≠ 2 → IsChev2 K → IsChev2 J →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ p = 1 →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J → LabelOf K labK → LabelOf J labJ →
      FieldRel p (canonLabel labK) (canonLabel labJ)

@[expose] def I14Neg (p : ℕ) (labK labJ : GLALabel) : Prop :=
  (labK = ⟨.twA, 5, 2⟩ → p = 5 → ¬ (labJ.tag = .A ∧ labJ.rank = 3 ∧ labJ.n = 2)) ∧
  ((labK.tag = .twA ∧ labK.rank = 5) → labJ.tag ≠ .B ∧ labJ.tag ≠ .C ∧ labJ.tag ≠ .D) ∧
  (((labK.tag = .D ∨ labK.tag = .B ∨ labK.tag = .C) ∧ labK.rank = 5) → ¬ (labJ.tag = .twD ∧ labJ.rank = 5)) ∧
  (labK = ⟨.E6, 0, 2⟩ → ¬ (labJ.tag = .twD ∧ labJ.rank = 5))

@[expose] def I14NegAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (K J : Subgroup G) (y : G) (labK labJ : GLALabel), p.Prime → p ≠ 2 → IsChev2 K → IsChev2 J →
    y ∈ Subgroup.normalizer (K : Set G) → y ^ p = 1 →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J → LabelOf K labK → LabelOf J labJ → I14Neg p labK labJ

@[expose] def I1416Chev2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p p' : ℕ) (X K J : Subgroup G) (y : G), p.Prime → p ≠ 2 → p'.Prime → p' ≠ 2 → p ≠ p' → CFSG.Open.IsKGroup ↥X →
    GLAPComponent p' X K → GLAPComponent p X K → y ∈ Subgroup.normalizer (K : Set G) → y ^ p = 1 →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J → IsChev2 J → CFSG.Open.IsQuasisimple ↥J →
    Odd (Nat.card (Subgroup.center ↥J)) → 6 ≤ twoRank ↥J → IsChevSimple 2 (PSimple p' K)

@[expose] def I142At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p' : ℕ) (X K E Y : Subgroup G), p'.Prime → p' ≠ 2 → CFSG.Open.IsKGroup ↥X → GLAPComponent p' X K →
    IsChevSimple 2 (PSimple p' K) → IsElemAbelian p' E → E ≤ Subgroup.normalizer (K : Set G) →
    Y ≤ K ⊓ Subgroup.centralizer (E : Set G) → GLAPLayer p' Y ≠ ⊥ → GLAPLayer p' (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥

end CFSG.LocalAnalysis.GLTheoremA
