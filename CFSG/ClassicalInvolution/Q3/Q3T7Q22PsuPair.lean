module

public import CFSG.ClassicalInvolution.Asc77.AscC22G13
public import CFSG.ClassicalInvolution.Q3.Q3WASTLift

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G

open CFSG
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.C22G CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement

namespace PsuPair

section Lifts

variable {U G : Type} [Group U] [Group G]

theorem commuting_lifts3 (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U) {R₁ R₂ : Subgroup U}
    (hc : Commutes R₁ R₂) {a₀ b₀ ε c₁ c₂ : U} (hc₁ : c₁ ∈ R₁) (hb₀ : b₀ ∈ R₂)
    (hε : ε ∈ Subgroup.center U) (hc₁a : c₁ = a₀ * a₀) (h : ψ c₂ = ψ (a₀ * b₀ * ε)) :
    c₁ * c₂ = c₂ * c₁ := by
  set τ : U := a₀ * b₀ * ε with hτ
  have hκ : c₂⁻¹ * τ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hκc : c₂⁻¹ * τ ∈ Subgroup.center U := hker hκ
  have h1 : c₁ * a₀ = a₀ * c₁ := by rw [hc₁a]; group
  have h2 : c₁ * b₀ = b₀ * c₁ := hc c₁ hc₁ b₀ hb₀
  have h3 : c₁ * ε = ε * c₁ := Subgroup.mem_center_iff.mp hε c₁
  have hcτ : c₁ * τ = τ * c₁ := by
    calc c₁ * τ = c₁ * a₀ * b₀ * ε := by rw [hτ]; group
      _ = a₀ * c₁ * b₀ * ε := by rw [h1]
      _ = a₀ * (c₁ * b₀) * ε := by group
      _ = a₀ * (b₀ * c₁) * ε := by rw [h2]
      _ = a₀ * b₀ * (c₁ * ε) := by group
      _ = a₀ * b₀ * (ε * c₁) := by rw [h3]
      _ = τ * c₁ := by rw [hτ]; group
  have hτeq : τ = c₂ * (c₂⁻¹ * τ) := by group
  have hκc' : c₁ * (c₂⁻¹ * τ) = (c₂⁻¹ * τ) * c₁ := Subgroup.mem_center_iff.mp hκc c₁
  have key : c₁ * c₂ * (c₂⁻¹ * τ) = c₂ * c₁ * (c₂⁻¹ * τ) := by
    calc c₁ * c₂ * (c₂⁻¹ * τ) = c₁ * τ := by group
      _ = τ * c₁ := hcτ
      _ = c₂ * (c₂⁻¹ * τ) * c₁ := by rw [← hτeq]
      _ = c₂ * ((c₂⁻¹ * τ) * c₁) := by group
      _ = c₂ * (c₁ * (c₂⁻¹ * τ)) := by rw [hκc']
      _ = c₂ * c₁ * (c₂⁻¹ * τ) := by group
  exact mul_right_cancel key

end Lifts

section Model

theorem admissible : StatedLieAdmissible .PSU 4 3 1 :=
  ⟨Fact.out, Nat.one_pos, by norm_num, by simp⟩

theorem perfect_model : Group.IsPerfect (modelUniv .PSU 4 3 1 Fact.out).K := by
  obtain ⟨φ, -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) admissible
  have hperf : Group.IsPerfect (Phan.Su (GaloisField 3 2) 3 1 4) :=
    Q3.Q3W.isPerfect_su3 (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective

theorem psu_dichotomy3 {R₁ R₂ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (h₁ : R₁ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    {c₁ c₂ : (modelUniv .PSU 4 3 1 Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁) :
    R₁ = R₂ ∨ Commutes R₁ R₂ ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have hn3 : 3 ≤ 4 := by norm_num
  have hn : 2 ≤ 4 := by norm_num
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 hf
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) hp2 admissible
  obtain ⟨i₁, hi₁⟩ := (hφ R₁).mp h₁
  obtain ⟨i₂, hi₂⟩ := (hφ R₂).mp h₂
  have e₁ : φ c₁ = i₁ := hi₁.eq_of_orderOf_eq_two hF hp2 ⟨c₁, hc₁, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₁)
  have e₂ : φ c₂ = i₂ := hi₂.eq_of_orderOf_eq_two hF hp2 ⟨c₂, hc₂, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₂)
  have hcφ : Commute i₁ i₂ := by
    show i₁ * i₂ = i₂ * i₁
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hne : i₁ = i₂
  · left
    have h12 : R₁.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by
      rw [hi₁.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2),
        hi₂.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2), hne]
    exact Subgroup.map_injective φ.injective h12
  · rcases commute_or_unitaryBlockStandardPair hF hp2 hn3 hi₁ hi₂ hcφ hne with h | ⟨-, h⟩
    · refine Or.inr (Or.inl fun x hx y hy => φ.injective ?_)
      rw [map_mul, map_mul]
      exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · have h' := unitaryBlockStandardPair_map h φ.symm.toMonoidHom φ.symm.injective
      have hmap : ∀ R : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K,
          (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := fun R => by
        rw [Subgroup.map_map]
        have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
          ext x
          simp
        rw [this, Subgroup.map_id]
      rw [hmap, hmap] at h'
      exact Or.inr (Or.inr ⟨_, h'⟩)

end Model

end PsuPair

section Pair

theorem psuLayer_pair3 {X : Type} [Group X] {Φ : Set (Subgroup X)} (P : PSULayer 3 1 Φ)
    {K K' L : Subgroup X}
    {RK RK' RL : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ) {z t e a b : X}
    (hzK : IsUniqueInvolution K z) (htL : IsUniqueInvolution L t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (he : e ∈ omegaGen Φ)
    (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e) (hne : K ≠ L)
    (hnc : ¬ Commutes K L) :
    (∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RK RL) ∧
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K L := by
  subst hKR hKR' hLR
  have have_perf := PsuPair.perfect_model
  have hU : (⊤ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K),
        (⊤ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K)⁆ :=
    (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K))).ge
  have hker : P.ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 3 1 Fact.out).K := P.ker_le
  have hcop : ∀ x ∈ P.ψ.ker, ¬ 3 ∣ orderOf x :=
    Q3.Q3W.ker_not_dvd_three_model (show IsFundTag .PSU from trivial) PsuPair.admissible P.ψ hker
  obtain ⟨eK⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (t := .PSU) (n := 4) (by trivial) PsuPair.admissible (by decide) (by decide) hRK
  obtain ⟨eL⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (t := .PSU) (n := 4) (by trivial) PsuPair.admissible (by decide) (by decide) hRL
  obtain ⟨c₁, hc₁R, hc₁o, -, hzc₁, hinjK, hP3⟩ :=
    Q3.Q3W.exists_lift_central_involution3 P.ψ hker hcop eK hzK
  obtain ⟨c₂, hc₂R, hc₂o, -, htc₂, -, -⟩ :=
    Q3.Q3W.exists_lift_central_involution3 P.ψ hker hcop eL htL
  have hcRR : Commutes RK RK' := by
    have h := Q3.Q3W.commutes_of_map_commute_exponent3 P.ψ hker hcop (A := RK') (L := RK) hP3
      (fun a' ha' l hl => (hcomm _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm)
    exact fun x hx y hy => (h y hy x hx).symm
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  obtain ⟨ε, hε, hψε⟩ := T7Z.exists_central_lift P.ψ hker hU (P.range_eq ▸ he)
    (fun y hy => hec y (P.range_eq ▸ hy))
  have hc₁a : c₁ = a₀ * a₀ := by
    have h1 : (a₀ * a₀)⁻¹ * c₁ = 1 := by
      refine hinjK _ (RK.mul_mem (RK.inv_mem (RK.mul_mem ha₀ ha₀)) hc₁R) ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, haa, hzc₁, inv_mul_cancel]
    exact (inv_mul_eq_one.mp h1).symm
  have h : P.ψ c₂ = P.ψ (a₀ * b₀ * ε) := by
    rw [← htc₂, htab, map_mul, map_mul, hψε]
  have hcc : c₁ * c₂ = c₂ * c₁ := PsuPair.commuting_lifts3 P.ψ hker hcRR hc₁R hb₀ hε hc₁a h
  rcases PsuPair.psu_dichotomy3 hRK hRL hc₁R hc₂R hc₁o hc₂o hcc with h' | h' | ⟨W, hW⟩
  · exact absurd (by rw [h']) hne
  · exact absurd (fun x hx y hy => by
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h' x hx y hy]) hnc
  · exact ⟨⟨W, hW⟩, _, Q3.Q3W.unitaryBlockStandardPair_map3 hW P.ψ hker⟩

end Pair

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G
