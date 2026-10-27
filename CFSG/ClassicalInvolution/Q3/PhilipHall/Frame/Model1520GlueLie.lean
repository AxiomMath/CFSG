module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueModels
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSL
public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

@[expose] def Model1520Covered : StatedLieTag → ℕ → Prop
  | .POmegaOdd, n => 3 ≤ n
  | .POmegaPlus, n => 5 ≤ n
  | .POmegaMinus, n => 4 ≤ n
  | .PSp, n => n = 2
  | .PSL, n => n = 4
  | _, _ => False


theorem model1520_of_modelUniv (tag : StatedLieTag) (n : ℕ) (hcov : Model1520Covered tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  cases tag with
  | POmegaOdd =>
    exact model1520_of_modelUniv_odd ⟨Nat.prime_three, le_rfl, hcov, by norm_num⟩ ψ hψ hker hR e
  | POmegaPlus =>
    exact model1520_of_modelUniv_plus ⟨Nat.prime_three, le_rfl, by simp only [Model1520Covered] at hcov; omega⟩ hcov ψ hψ hker hR e
  | POmegaMinus =>
    exact model1520_of_modelUniv_minus ⟨Nat.prime_three, le_rfl, hcov⟩ ψ hψ hker hR e
  | PSp =>
    obtain rfl : n = 2 := hcov
    exact Model1520Sp.model1520_psp_aux ψ hψ hker e
      (isLongRootSp2_sl2Inv ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩ hR e)
  | PSL =>
    obtain rfl : n = 4 := hcov
    exact Model1520L.model1520_psl_aux ψ hψ hker e
      (isLongRootSL2_sl2Inv_four hR e)
  | _ => exact hcov.elim

theorem covered_facts {tag : StatedLieTag} {n : ℕ} (hcov : Model1520Covered tag n) :
    StatedLieAdmissible tag n 3 1 ∧ ModelFacts.IsFundTag tag ∧ tag ≠ .G2 ∧ tag ≠ .trialityD4 := by
  cases tag with
  | POmegaOdd => exact ⟨⟨Nat.prime_three, le_rfl, hcov, by norm_num⟩, trivial, by decide, by decide⟩
  | POmegaPlus =>
    exact ⟨⟨Nat.prime_three, le_rfl, by simp only [Model1520Covered] at hcov; omega⟩, trivial,
      by decide, by decide⟩
  | POmegaMinus => exact ⟨⟨Nat.prime_three, le_rfl, hcov⟩, trivial, by decide, by decide⟩
  | PSp =>
    obtain rfl : n = 2 := hcov
    exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, trivial, by decide, by decide⟩
  | PSL =>
    obtain rfl : n = 4 := hcov
    exact ⟨⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩, trivial, by decide,
      by decide⟩
  | _ => exact hcov.elim

theorem model1520_of_modelUniv_member (tag : StatedLieTag) (n : ℕ) (hcov : Model1520Covered tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    {L : Subgroup ↥X} (hLR : L = R.map ψ) (hL24 : Nat.card L = 24) {t : ↥X}
    (hLt : IsClassicalMember3 L t) : Model1520 X (t : G) := by
  obtain ⟨hadm, hfund, hG2, hD4⟩ := covered_facts hcov
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := tag) hfund
    hadm hG2 hD4 hR
  have hfin : Finite (Generic.modelUniv tag n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (t := tag) hp2 Nat.prime_three hfund hadm
  have hcard : Nat.card (R.map ψ) = 24 := hLR ▸ hL24
  obtain ⟨hu, -⟩ := uniqueInvolution_map3 ψ e hcard
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hLt.orderOf_eq_two, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    have := hLt.orderOf_eq_two
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htz : t = ψ (sl2Inv e) :=
    (hu.unique t (hLR ▸ hLt.mem) htsq).resolve_left ht1
  rw [htz]
  exact model1520_of_modelUniv tag n hcov ψ hψ hker hR e

theorem model1520_of_lieSystem3 {G : Type} [Group G] [Finite G] (X : Subgroup G) {ι : Type}
    {Φ : Set (Subgroup ↥X)} (D : LieSystemData3 ι ↥X Φ) (i : ι) (hi : ∀ j, j = i)
    (tag : StatedLieTag) (n : ℕ) (hcov : Model1520Covered tag n)
    (hk : D.kind i = CompData.model tag n) {L : Subgroup ↥X} (hL : L ∈ Φ) {t : ↥X}
    (hLt : IsClassicalMember3 L t) : Model1520 X (t : G) := by
  have hrange : (D.hom i).range = ⊤ := by
    rw [eq_top_iff, ← D.generate]
    exact iSup_le fun j => by rw [hi j]
  obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
  have hj : j = i := hi j
  subst hj
  have key : ∀ (c : CompData) (hc : c = CompData.model tag n) (φ : c.G →* ↥X)
      (hsurj : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center c.G) (R : Subgroup c.G),
      R ∈ c.fund → L = R.map φ → Model1520 X (t : G) := by
    intro c hc φ hsurj hker R hR hLR
    subst hc
    exact model1520_of_modelUniv_member tag n hcov φ hsurj hker hR hLR (D.card_eq L hL) hLt
  exact key (D.kind j) hk (D.hom j) (MonoidHom.range_eq_top.mp hrange) (D.ker_le_center j) R hR hLR

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
