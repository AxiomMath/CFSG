module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZA2
public import CFSG.ClassicalInvolution.Asc77.AscIH8Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open scoped commutatorElement

namespace T8ZZ

section Perfect

variable {K : Type*} [Group K]

theorem commutator_mul_central {c d : K} (a b : K) (hc : c ∈ Subgroup.center K)
    (hd : d ∈ Subgroup.center K) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have key : ∀ (z x : K), z ∈ Subgroup.center K → z * x * z⁻¹ = x := fun z x hz => by
    have := Subgroup.mem_center_iff.mp hz x
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]
  have hd' := Subgroup.mem_center_iff.mp hd
  calc ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (b⁻¹ * d⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = (a * (d * b) * a⁻¹) * (b⁻¹ * d⁻¹) := by rw [key c _ hc]
    _ = d * (a * b * a⁻¹) * (b⁻¹ * d⁻¹) := by
        have : a * (d * b) * a⁻¹ = d * (a * b * a⁻¹) :=
          calc a * (d * b) * a⁻¹ = (a * d) * b * a⁻¹ := by group
            _ = (d * a) * b * a⁻¹ := by rw [hd' a]
            _ = d * (a * b * a⁻¹) := by group
        rw [this]
    _ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := key d _ hd
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]

theorem mem_center_of_forall_commutator_mem_center (hperf : Group.IsPerfect K) {ω : K}
    (h : ∀ k : K, ⁅ω, k⁆ ∈ Subgroup.center K) : ω ∈ Subgroup.center K := by
  have hle : commutator K ≤ Subgroup.centralizer ({ω} : Set K) := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ea : ω * a * ω⁻¹ = ⁅ω, a⁆ * a := by simp [commutatorElement_def]
    have eb : ω * b * ω⁻¹ = ⁅ω, b⁆ * b := by simp [commutatorElement_def]
    have e : ω * ⁅a, b⁆ * ω⁻¹ = ⁅a, b⁆ := by
      calc ω * ⁅a, b⁆ * ω⁻¹ = ⁅ω * a * ω⁻¹, ω * b * ω⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅⁅ω, a⁆ * a, ⁅ω, b⁆ * b⁆ := by rw [ea, eb]
        _ = ⁅a, b⁆ := commutator_mul_central a b (h a) (h b)
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  have htop : commutator K = ⊤ := Group.isPerfect_def.mp hperf
  rw [htop, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at hle
  exact hle (Set.mem_singleton ω)

end Perfect

variable {p f : ℕ} [Fact p.Prime]

structure PlusModelFacts (p f : ℕ) [Fact p.Prime] : Prop where
  finite : Finite (modelUniv .POmegaPlus 4 p f Fact.out).K
  perfect : Group.IsPerfect (modelUniv .POmegaPlus 4 p f Fact.out).K
  card_center : Nat.card (Subgroup.center (modelUniv .POmegaPlus 4 p f Fact.out).K) ≤ 4
  meet_center : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D,
    ∀ r ∈ R, r ∈ Subgroup.center (modelUniv .POmegaPlus 4 p f Fact.out).K → r = 1
  prod_central : ∀ R₁ ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 p f Fact.out).D,
    ∀ R₂ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D,
      Commutes R₁ R₂ → ∀ ζ₁ ζ₂, InvOf R₁ ζ₁ → InvOf R₂ ζ₂ →
        ζ₁ * ζ₂ ∈ Subgroup.center (modelUniv .POmegaPlus 4 p f Fact.out).K

theorem plusModelFacts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : PlusModelFacts p f := by
  have hn3 : 3 ≤ 4 := by norm_num
  have e := modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, le_refl 4⟩
  have hY := yData_plus (p := p) (f := f) (le_refl 4) hadm (by omega)
  refine ⟨?_, hY.perfK, ?_, hY.central, ?_⟩
  · rw [e]
    exact ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  · rw [e]
    exact plus_card_center_le
  · rw [e]
    intro R₁ h₁ R₂ h₂ hc ζ₁ ζ₂ hζ₁ hζ₂
    exact plus_prod_central hp2 hq h₁ h₂ hc hζ₁ hζ₂

section Datum

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {e : ℕ}


theorem datum_center_le_map_center (M : Ih8Model p f Φ .POmegaPlus 4 e)
    (hF : PlusModelFacts p e) :
    Subgroup.center X ≤ (Subgroup.center (modelUniv .POmegaPlus 4 p e Fact.out).K).map M.ψ := by
  intro x hx
  obtain ⟨ω, rfl⟩ := M.surj x
  refine ⟨ω, mem_center_of_forall_commutator_mem_center hF.perfect fun k => ?_, rfl⟩
  apply M.ker_le_center
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have h := Subgroup.mem_center_iff.mp hx (M.ψ k)
  simp only [commutatorElement_def]
  calc M.ψ ω * M.ψ k * (M.ψ ω)⁻¹ * (M.ψ k)⁻¹ = (M.ψ k * M.ψ ω) * (M.ψ ω)⁻¹ * (M.ψ k)⁻¹ := by
        rw [h]
    _ = 1 := by group

theorem datum_card_center_le [Finite X] (M : Ih8Model p f Φ .POmegaPlus 4 e)
    (hF : PlusModelFacts p e) : Nat.card (Subgroup.center X) ≤ 4 := by
  have := hF.finite
  have h1 := Subgroup.card_le_of_le (datum_center_le_map_center M hF)
  have h2 := Nat.le_of_dvd Nat.card_pos
    (Subgroup.card_map_dvd (H := Subgroup.center (modelUniv .POmegaPlus 4 p e Fact.out).K) M.ψ)
  exact h1.trans (h2.trans hF.card_center)

theorem datum_exists_involution_lift (M : Ih8Model p f Φ .POmegaPlus 4 e) (hF : PlusModelFacts p e)
    {R : Subgroup (modelUniv .POmegaPlus 4 p e Fact.out).K} (hR : R ∈ M.cls) {z : X}
    (hz : IsUniqueInvolution (R.map M.ψ) z) : ∃ ζ, InvOf R ζ ∧ M.ψ ζ = z := by
  obtain ⟨r, hrR, hrz⟩ := hz.mem
  have hsq : r * r = 1 := by
    have h1 : r * r ∈ Subgroup.center (modelUniv .POmegaPlus 4 p e Fact.out).K := by
      apply M.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, hrz]
      exact hz.sq
    exact hF.meet_center R (M.cls_sub hR) (r * r) (R.mul_mem hrR hrR) h1
  have hne : r ≠ 1 := fun h => hz.ne_one (by rw [← hrz, h, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hne⟩, hrz⟩

theorem datum_mul_mem_center (M : Ih8Model p f Φ .POmegaPlus 4 e) (hF : PlusModelFacts p e)
    {R₁ R₂ : Subgroup (modelUniv .POmegaPlus 4 p e Fact.out).K} (h₁ : R₁ ∈ M.cls)
    (h₂ : R₂ ∈ M.cls) (hc : Commutes R₁ R₂) {ζ₁ ζ₂ : (modelUniv .POmegaPlus 4 p e Fact.out).K}
    (hζ₁ : InvOf R₁ ζ₁) (hζ₂ : InvOf R₂ ζ₂) : M.ψ ζ₁ * M.ψ ζ₂ ∈ Subgroup.center X := by
  have h := hF.prod_central R₁ (M.cls_sub h₁) R₂ (M.cls_sub h₂) hc ζ₁ ζ₂ hζ₁ hζ₂
  rw [← map_mul]
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := M.surj y
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp h k)]

end Datum

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
