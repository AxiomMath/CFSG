module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossSL2
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction

public section

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Hex
open scoped commutatorElement IsMulCommutative

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FrattiniRep

variable {E X : Type*} [Group E] [Group X] [Finite X] [MulDistribMulAction E X] {p : ℕ}
  [Fact p.Prime] [Fact (IsPGroup p X)]

instance instIsElementaryAbelianFrattiniQuotientOdd87 : IsElementaryAbelian p (X ⧸ frattini X) :=
  isElementaryAbelian_quotient_frattini (p := p) (R := X)

omit [Finite X] [Fact p.Prime] [Fact (IsPGroup p X)] in
theorem isInvariant_frattini : IsInvariant E X (frattini X) := by
  refine ⟨fun a x => ?_⟩
  have h := Subgroup.characteristic_iff_comap_eq.mp (frattini_characteristic (G := X))
    (MulDistribMulAction.toMulAut E X a)
  constructor
  · intro hx
    rw [← h] at hx
    exact hx
  · intro hx
    rw [← h]
    exact hx

@[expose, reducible] noncomputable def frattiniQuotAct : MulDistribMulAction E (X ⧸ frattini X) :=
  quotientMulDistribMulAction (A := E) (G := X) (frattini X) (isInvariant_frattini (E := E) (X := X))

@[expose] noncomputable def frattiniRep' :
    Representation (ZMod p) E (Additive (X ⧸ frattini X)) :=
  letI := frattiniQuotAct (E := E) (X := X)
  Theory.Representation.ofElementaryAbelianAction (A := E) (G := X ⧸ frattini X) (p := p)

theorem frattiniRep'_apply_mk (e : E) (x : X) :
    frattiniRep' (p := p) (E := E) (X := X) e (Additive.ofMul (x : X ⧸ frattini X)) =
      Additive.ofMul ((e • x : X) : X ⧸ frattini X) := by
  let _ := frattiniQuotAct (E := E) (X := X)
  unfold frattiniRep'
  rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul (A := E)
    (G := X ⧸ frattini X) (p := p) e _]
  rfl

end FrattiniRep

section Ambient

variable {A : Type} [Group A] [Finite A] {E : Type} [Group E] {p : ℕ} [Fact p.Prime]

@[expose, reducible] def conjActOfHom (ι : E →* A) (X : Subgroup A)
    (hnorm : ∀ e, ι e ∈ normalizer (X : Set A)) : MulDistribMulAction E ↥X :=
  letI := Subgroup.conjMulDistribMulActionOfLeNormalizer ι.range X
    (fun a ha => by obtain ⟨e, rfl⟩ := ha; exact hnorm e)
  MulDistribMulAction.compHom ↥X ι.rangeRestrict

@[expose] noncomputable def frattiniRepOf (ι : E →* A) (X : Subgroup A) [Fact (IsPGroup p X)]
    (hnorm : ∀ e, ι e ∈ normalizer (X : Set A)) :
    Representation (ZMod p) E (Additive (↥X ⧸ frattini ↥X)) :=
  letI := conjActOfHom ι X hnorm
  frattiniRep' (E := E) (X := ↥X) (p := p)

@[expose] def conjX (ι : E →* A) (X : Subgroup A) (hnorm : ∀ e, ι e ∈ normalizer (X : Set A))
    (e : E) (x : X) : X := ⟨ι e * x * (ι e)⁻¹, ((mem_normalizer_iff.mp (hnorm e)) x).1 x.2⟩

theorem frattiniRepOf_apply_mk (ι : E →* A) (X : Subgroup A) [Fact (IsPGroup p X)]
    (hnorm : ∀ e, ι e ∈ normalizer (X : Set A)) (e : E) (x : X) :
    frattiniRepOf (p := p) ι X hnorm e (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) =
      Additive.ofMul ((conjX ι X hnorm e x : X) : ↥X ⧸ frattini ↥X) := by
  unfold frattiniRepOf
  let _ := conjActOfHom ι X hnorm
  exact frattiniRep'_apply_mk (p := p) (E := E) (X := ↥X) e x

theorem frattiniRepOf_neg (ι : E →* A) (X : Subgroup A) [Fact (IsPGroup p X)]
    (hnorm : ∀ e, ι e ∈ normalizer (X : Set A)) {z : E} (hz2 : z * z = 1)
    (hcomm : ⁅X, Subgroup.zpowers (ι z)⁆ = X) (v : Additive (↥X ⧸ frattini ↥X)) :
    frattiniRepOf (p := p) ι X hnorm z v = -v := by
  have hTT : ∀ w, frattiniRepOf (p := p) ι X hnorm z (frattiniRepOf (p := p) ι X hnorm z w) = w := by
    intro w
    have : frattiniRepOf (p := p) ι X hnorm z * frattiniRepOf (p := p) ι X hnorm z = 1 := by
      rw [← map_mul, hz2, map_one]
    simpa using congrArg (fun f => f w) this
  let N : Submodule (ZMod p) (Additive (↥X ⧸ frattini ↥X)) :=
    LinearMap.range (LinearMap.id - frattiniRepOf (p := p) ι X hnorm z)
  have hgen : ∀ g ∈ ({g : A | ∃ g₁ ∈ X, ∃ g₂ ∈ Subgroup.zpowers (ι z), ⁅g₁, g₂⁆ = g} : Set A),
      ∃ y : X, (y : A) = g ∧ Additive.ofMul (y : ↥X ⧸ frattini ↥X) ∈ N := by
    rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · refine ⟨1, ?_, by simp⟩
      have : z ^ n = 1 := by
        rw [hk, zpow_mul, zpow_two, hz2, one_zpow]
      rw [← map_zpow, this, map_one]
      simp [commutatorElement_def]
    · refine ⟨⟨g₁, hg₁⟩ * (conjX ι X hnorm z ⟨g₁, hg₁⟩)⁻¹, ?_, ?_⟩
      · have : z ^ n = z := by
          rw [hk, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
        rw [← map_zpow, this]
        simp [conjX, commutatorElement_def, mul_assoc]
      · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv, ← sub_eq_add_neg,
          ← frattiniRepOf_apply_mk (p := p) ι X hnorm z ⟨g₁, hg₁⟩]
        exact ⟨Additive.ofMul (((⟨g₁, hg₁⟩ : X) : ↥X ⧸ frattini ↥X)), rfl⟩
  have hN : ∀ x : X, Additive.ofMul (x : ↥X ⧸ frattini ↥X) ∈ N := by
    intro x
    have hx : (x : A) ∈ Subgroup.closure
        {g : A | ∃ g₁ ∈ X, ∃ g₂ ∈ Subgroup.zpowers (ι z), ⁅g₁, g₂⁆ = g} := by
      rw [← Subgroup.commutator_def, hcomm]
      exact x.2
    have key : ∀ g (hg : g ∈ Subgroup.closure
        {g : A | ∃ g₁ ∈ X, ∃ g₂ ∈ Subgroup.zpowers (ι z), ⁅g₁, g₂⁆ = g}),
        ∃ y : X, (y : A) = g ∧ Additive.ofMul (y : ↥X ⧸ frattini ↥X) ∈ N := by
      intro g hg
      refine Subgroup.closure_induction (fun g hg => hgen g hg) ⟨1, by simp, by simp⟩ ?_ ?_ hg
      · rintro a b - - ⟨ya, rfl, hya⟩ ⟨yb, rfl, hyb⟩
        refine ⟨ya * yb, rfl, ?_⟩
        rw [QuotientGroup.mk_mul, ofMul_mul]
        exact N.add_mem hya hyb
      · rintro a - ⟨ya, rfl, hya⟩
        refine ⟨ya⁻¹, rfl, ?_⟩
        rw [QuotientGroup.mk_inv, ofMul_inv]
        exact N.neg_mem hya
    obtain ⟨y, hy, hyN⟩ := key _ hx
    have : y = x := Subtype.ext hy
    rwa [this] at hyN
  obtain ⟨x, hxv⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (x : ↥X ⧸ frattini ↥X) := by rw [hxv]; rfl
  obtain ⟨w, hw⟩ := hN x
  rw [hv, ← hw]
  simp [hTT]

end Ambient

section SL2Wrapper

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

omit [Finite A] in
theorem neg_one_mul_neg_one_sl2 {F : Type} [Field F] : (-1 : SL2 F) * (-1) = 1 := by
  apply Subtype.ext
  simp

theorem cross_sl2_frattini (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A) {X : Subgroup A} (hX : IsPGroup p X) (hX1 : X ≠ ⊥)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hcomm : ⁅X, Subgroup.zpowers (ι (-1))⁆ = X) :
    ∃ d : ℕ, Nat.card (↥X ⧸ frattini ↥X) = p ^ d ∧ (Nat.card F - 1) / 2 ≤ d ∧ Even d := by
  have : Fact (IsPGroup p X) := ⟨hX⟩
  have : Nontrivial (Additive (↥X ⧸ frattini ↥X)) := by
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hX1
    have hne : frattini ↥X ≠ ⊤ := by
      obtain h | ⟨M, hM, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥X)
      · exact absurd h bot_ne_top
      · intro htop
        exact hM.1 (top_le_iff.mp (htop ▸ frattini_le_coatom hM))
    have : Nontrivial (↥X ⧸ frattini ↥X) := (QuotientGroup.nontrivial_iff (N := frattini ↥X)).2 hne
    infer_instance
  have hz : ∀ v, frattiniRepOf (p := p) ι X hnorm (-1) v = -v :=
    frattiniRepOf_neg ι X hnorm neg_one_mul_neg_one_sl2 hcomm
  obtain ⟨h1, h2, -⟩ := sl2_neg_dim hp2 hodd hpq (frattiniRepOf (p := p) ι X hnorm) hz
  refine ⟨Module.finrank (ZMod p) (Additive (↥X ⧸ frattini ↥X)), ?_, h1, h2⟩
  have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (↥X ⧸ frattini ↥X))
  rw [Nat.card_zmod] at this
  rwa [Nat.card_congr (Additive.toMul : Additive (↥X ⧸ frattini ↥X) ≃ _)] at this

theorem le_padicValNat_of_sl2 (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A) {X : Subgroup A} (hX : IsPGroup p X) (hX1 : X ≠ ⊥)
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) (hcomm : ⁅X, Subgroup.zpowers (ι (-1))⁆ = X) :
    (Nat.card F - 1) / 2 ≤ padicValNat p (Nat.card X) := by
  obtain ⟨d, hd, h1, -⟩ := cross_sl2_frattini hp2 hodd hpq ι hX hX1 hnorm hcomm
  have hdvd : p ^ d ∣ Nat.card X := hd ▸ Subgroup.card_quotient_dvd_card (frattini ↥X)
  exact h1.trans ((padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd)

theorem le_padicValNat_of_sl2_of_le (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A) {X K : Subgroup A}
    (hXK : X ≤ K) (hX : IsPGroup p X) (hX1 : X ≠ ⊥) (hnorm : ∀ g, ι g ∈ normalizer (X : Set A))
    (hcomm : ⁅X, Subgroup.zpowers (ι (-1))⁆ = X) :
    (Nat.card F - 1) / 2 ≤ padicValNat p (Nat.card K) := by
  refine (le_padicValNat_of_sl2 hp2 hodd hpq ι hX hX1 hnorm hcomm).trans ?_
  exact (padicValNat_dvd_iff_le Nat.card_pos.ne').1
    ((pow_padicValNat_dvd (p := p) (n := Nat.card X)).trans (Subgroup.card_dvd_of_le hXK))

end SL2Wrapper

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
