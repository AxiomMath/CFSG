module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04F
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Chain
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def isPOmegaPlus8 (q : ℕ) : TauCeti.LieTypeIndex → Prop
  | .D 4 qq => qq.card = q
  | _ => False

@[expose] def IsPOmegaPlus8 (S : Type) [Group S] (q : ℕ) : Prop :=
  catalogIs S (onLie (isPOmegaPlus8 q))

@[expose] def KD26bcLinUni : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (n q : ℕ) (lin : Bool), IsLnEps S n q lin → ∀ p : ℕ, p.Prime → p ≠ 2 →
      p ∣ Nat.gcd n (qEps lin q) → p ^ 2 ∣ Nat.gcd n (qEps lin q) →
      ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

@[expose] def KD26bcD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ q : ℕ, IsPOmegaPlus8 S q → ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D →
      Nat.card D = 3 ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

@[expose] def KD26bcE6 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (q : ℕ) (lin : Bool), IsE6Eps S q lin → 3 ∣ qEps lin q →
      ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

theorem kd26bcE6_of_fE6 (h : YS04F.KD26fE6) : KD26bcE6 := by
  intro S _ _ hs hna q lin hE h3 D hD hcard hinn
  exfalso
  have h1 := h S hs hna q lin hE h3 D hD
  rw [hinn, Subgroup.card_bot, hcard] at h1
  norm_num at h1

theorem card_le_outer_of_inf_eq_bot {S : Type} [Group S] [Finite S] (D : Subgroup (MulAut S))
    (hD : D ⊓ inner S = ⊥) : Nat.card D ≤ Nat.card (Outer S) := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  refine Nat.card_le_card_of_injective (fun x : D => (QuotientGroup.mk (x : MulAut S) : Outer S)) ?_
  intro x y hxy
  have h1 : (x : MulAut S)⁻¹ * (y : MulAut S) ∈ inner S := (QuotientGroup.eq).1 hxy
  have h2 : (x : MulAut S)⁻¹ * (y : MulAut S) ∈ D := D.mul_mem (D.inv_mem x.2) y.2
  have h3 : (x : MulAut S)⁻¹ * (y : MulAut S) ∈ D ⊓ inner S := ⟨h2, h1⟩
  rw [hD, Subgroup.mem_bot, inv_mul_eq_one] at h3
  exact Subtype.ext h3

theorem false_of_outer_le {S : Type} [Group S] [Finite S] {p c : ℕ} (hp3 : 3 ≤ p)
    (hc : Nat.card (Outer S) ≤ c) (hc9 : c < 9) (D : Subgroup (MulAut S))
    (hcard : Nat.card D = p ^ 2) (hinn : D ⊓ inner S = ⊥) : False := by
  have h1 := card_le_outer_of_inf_eq_bot D hinn
  rw [hcard] at h1
  nlinarith

theorem false_of_le_mul {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {D I : Subgroup G}
    [Finite G] (hcard : Nat.card D = p ^ 2) (hinn : D ⊓ I = ⊥)
    (hle : Nat.card D ≤ p * Nat.card ↥(D ⊓ I)) : False := by
  rw [hinn, Subgroup.card_bot, hcard] at hle
  have := hp.two_le
  nlinarith

theorem false_of_outPChain {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hO : CFSG.RankThree.PartOne.OutStructure.OutPChain p S) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) (hinn : D ⊓ inner S = ⊥) : False := by
  obtain ⟨x, hx, hx1⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.meets_inner_of_outPChain hp hO D hD hcard
  have hx' : x ∈ D ⊓ inner S := hx
  rw [hinn, Subgroup.mem_bot] at hx'
  exact hx1 hx'

theorem false_of_cyclic {S : Type} [Group S] (q : ℕ) (e : S ≃* Multiplicative (ZMod q))
    (hna : ∃ a b : S, a * b ≠ b * a) : False := by
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem false_of_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) {p : ℕ} (hp3 : 3 ≤ p) (D : Subgroup (MulAut S))
    (hcard : Nat.card D = p ^ 2) (hinn : D ⊓ inner S = ⊥) : False := by
  have h4 : Nat.card (Outer S) ∣ 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
  exact false_of_outer_le hp3 (Nat.le_of_dvd (by norm_num) h4) (by norm_num) D hcard hinn

end CFSG.LocalAnalysis.GLTheoremA
