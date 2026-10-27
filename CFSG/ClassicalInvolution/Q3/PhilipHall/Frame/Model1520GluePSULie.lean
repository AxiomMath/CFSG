module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GluePSU
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueLie
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem model1520_of_modelUniv_psu (hadm : StatedLieAdmissible .PSU 4 3 1)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).D)
    (e₂ : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e₂) : ↥X) : G) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨e, hfund⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) hp2 hadm
  obtain ⟨i, hi⟩ := (hfund R).mp hR
  have hord : orderOf (e (sl2Inv e₂)) = 2 := by
    rw [MulEquiv.orderOf_eq e]
    exact orderOf_eq_prime (by rw [pow_two]; exact sl2Inv_mul_self hodd e₂)
      (sl2Inv_ne_one hodd e₂)
  have hie : e (sl2Inv e₂) = i :=
    hi.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂)) hord
  obtain ⟨g, -, hig⟩ := hi
  let ψ' : Su (GaloisField 3 (2 * 1)) 3 1 4 →* ↥X :=
    (ψ.comp e.symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom
  have hψ' : Function.Surjective ψ' := fun x => by
    obtain ⟨k, rfl⟩ := hψ x
    exact ⟨g⁻¹ * e k * g, by simp [ψ']; group⟩
  have hker' : ψ'.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
    intro x hx
    have hx' : e.symm (g * x * g⁻¹) ∈ Subgroup.center _ := hker hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    have h1 := hx' (e.symm (g * y * g⁻¹))
    have h2 : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) := by
      generalize g * y * g⁻¹ = a at h1 ⊢
      generalize g * x * g⁻¹ = b at h1 ⊢
      apply e.symm.injective
      rw [map_mul e.symm a b, map_mul e.symm b a]
      exact h1
    have h3 : y * x = x * y := by
      have := congrArg (fun z => g⁻¹ * z * g) h2
      simpa [mul_assoc] using this
    exact h3
  have key := Model1520U.model1520_su4_std hK (by norm_num) hp2 ψ' hψ' hker'
  have hrt : ψ' (rootInvSU (GaloisField 3 (2 * 1)) 3 1 (show 2 ≤ 4 by norm_num)) =
      ψ (sl2Inv e₂) := by
    show ψ (e.symm (g * rootInvSU (GaloisField 3 (2 * 1)) 3 1 (show 2 ≤ 4 by norm_num) * g⁻¹)) = _
    rw [← hig, ← hie, MulEquiv.symm_apply_apply]
  rw [hrt] at key
  exact key

@[expose] def Model1520CoveredAll (tag : StatedLieTag) (n : ℕ) : Prop :=
  Model1520Covered tag n ∨ (tag = .PSU ∧ n = 4)

theorem covered_facts_all {tag : StatedLieTag} {n : ℕ} (hcov : Model1520CoveredAll tag n) :
    StatedLieAdmissible tag n 3 1 ∧ ModelFacts.IsFundTag tag ∧ tag ≠ .G2 ∧ tag ≠ .trialityD4 := by
  rcases hcov with h | ⟨rfl, rfl⟩
  · exact covered_facts h
  · exact ⟨⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩, trivial, by decide, by decide⟩

theorem model1520_of_modelUniv_all (tag : StatedLieTag) (n : ℕ) (hcov : Model1520CoveredAll tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  rcases hcov with h | ⟨rfl, rfl⟩
  · exact model1520_of_modelUniv tag n h ψ hψ hker hR e
  · exact model1520_of_modelUniv_psu ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩ ψ hψ hker hR e

theorem model1520_of_modelUniv_member_all (tag : StatedLieTag) (n : ℕ) (hcov : Model1520CoveredAll tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    {L : Subgroup ↥X} (hLR : L = R.map ψ) (hL24 : Nat.card L = 24) {t : ↥X}
    (hLt : IsClassicalMember3 L t) : Model1520 X (t : G) := by
  obtain ⟨hadm, hfund, hG2, hD4⟩ := covered_facts_all hcov
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
  exact model1520_of_modelUniv_all tag n hcov ψ hψ hker hR e

theorem model1520_of_lieSystem3_all {G : Type} [Group G] [Finite G] (X : Subgroup G) {ι : Type}
    {Φ : Set (Subgroup ↥X)} (D : LieSystemData3 ι ↥X Φ) (i : ι) (hi : ∀ j, j = i)
    (tag : StatedLieTag) (n : ℕ) (hcov : Model1520CoveredAll tag n)
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
    exact model1520_of_modelUniv_member_all tag n hcov φ hsurj hker hR hLR (D.card_eq L hL) hLt
  exact key (D.kind j) hk (D.hom j) (MonoidHom.range_eq_top.mp hrange) (D.ker_le_center j) R hR hLR

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
