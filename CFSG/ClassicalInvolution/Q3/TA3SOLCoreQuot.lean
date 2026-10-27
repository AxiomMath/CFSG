module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreAct
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQ8
public import CFSG.GH74.Filter.Lie.Q8Cube

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem datum_conj_mem_oddCoreImg (hD : TightDatum R S t) {g o : X}
    (hg : g ∈ Subgroup.centralizer ({t} : Set X)) (ho : o ∈ oddCoreImg R) :
    g * o * g⁻¹ ∈ oddCoreImg R :=
  (OddByQuat.of_quaternion S hD.quat hD.mem hD.order hD.cent hD.normal hD.twoGroup).conj_mem_O hg
    ho

theorem datum_oddCore_normal (hD : TightDatum R S t) :
    ((oddCoreImg R).subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using datum_conj_mem_oddCoreImg hD g.2 hn

theorem eq_one_of_mem_oddCoreImg {x : X} (hx : x ∈ oddCoreImg R) (h8 : orderOf x ∣ 8) : x = 1 := by
  have hdvd := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime 8 (Nat.card (oddCoreImg R)) :=
    Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr (odd_natCard_oddCoreImg R))
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h8 hdvd))

theorem orderOf_q8_dvd (x : QuaternionGroup 2) : orderOf x ∣ 8 := by
  have := orderOf_dvd_natCard x
  rwa [Nat.card_eq_fintype_card, QuaternionGroup.card] at this

section Quot

variable (hD : TightDatum R S t)
include hD

theorem datum_lift_injective (φ : QuaternionGroup 2 →* X)
    (hφ : ∀ x, φ x ∈ Subgroup.centralizer ({t} : Set X)) (hi : Function.Injective φ) :
    haveI := datum_oddCore_normal hD
    Function.Injective ((QuotientGroup.mk' ((oddCoreImg R).subgroupOf
      (Subgroup.centralizer ({t} : Set X)))).comp (φ.codRestrict _ hφ)) := by
  have := datum_oddCore_normal hD
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx
  have h1 : φ x = 1 := eq_one_of_mem_oddCoreImg hx ((orderOf_map_dvd φ x).trans (orderOf_q8_dvd x))
  exact hi (h1.trans (map_one φ).symm)

theorem datum_commute_mk {h r : X} (hh : h ∈ Subgroup.centralizer ({t} : Set X))
    (hr : r ∈ Subgroup.centralizer ({t} : Set X)) (hc : ⁅h, r⁆ ∈ oddCoreImg R) :
    haveI := datum_oddCore_normal hD
    Commute (QuotientGroup.mk' ((oddCoreImg R).subgroupOf
      (Subgroup.centralizer ({t} : Set X))) ⟨h, hh⟩) (QuotientGroup.mk' _ ⟨r, hr⟩) := by
  have := datum_oddCore_normal hD
  show QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hg : (h * r)⁻¹ ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ hh hr)
  have h1 := datum_conj_mem_oddCoreImg hD hg ((oddCoreImg R).inv_mem hc)
  have e : (h * r)⁻¹ * ⁅h, r⁆⁻¹ * (h * r)⁻¹⁻¹ = (h * r)⁻¹ * (r * h) := by
    rw [commutatorElement_def]; group
  rw [e] at h1
  simpa using h1

theorem datum_not_fourGenerated {H₁ H₂ : Subgroup X}
    (h₁ : H₁ ≤ Subgroup.centralizer ({t} : Set X)) (h₂ : H₂ ≤ Subgroup.centralizer ({t} : Set X))
    [Group.IsPerfect H₁] [Group.IsPerfect H₂] (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a)
    (φ₁ φ₂ : QuaternionGroup 2 →* X) (hi₁ : Function.Injective φ₁) (hi₂ : Function.Injective φ₂)
    (hr₁ : ∀ x, φ₁ x ∈ H₁) (hr₂ : ∀ x, φ₂ x ∈ H₂) : ¬ TwoSubgroupsFourGenerated X := by
  intro hF
  have := datum_oddCore_normal hD
  set C := Subgroup.centralizer ({t} : Set X) with hCdef
  set N := (oddCoreImg R).subgroupOf C with hNdef
  obtain ⟨φ₀, hi₀, hr₀, -⟩ := datum_exists_q8 hD
  have hC₀ : ∀ x, φ₀ x ∈ C := fun x => hD.cent (hr₀ x)
  have hC₁ : ∀ x, φ₁ x ∈ C := fun x => h₁ (hr₁ x)
  have hC₂ : ∀ x, φ₂ x ∈ C := fun x => h₂ (hr₂ x)
  let ψ : Fin 3 → QuaternionGroup 2 →* C ⧸ N :=
    ![(QuotientGroup.mk' N).comp (φ₀.codRestrict C hC₀),
      (QuotientGroup.mk' N).comp (φ₁.codRestrict C hC₁),
      (QuotientGroup.mk' N).comp (φ₂.codRestrict C hC₂)]
  have hinj : ∀ i, Function.Injective (ψ i) := by
    intro i
    fin_cases i
    · exact datum_lift_injective hD φ₀ hC₀ hi₀
    · exact datum_lift_injective hD φ₁ hC₁ hi₁
    · exact datum_lift_injective hD φ₂ hC₂ hi₂
  have hc01 : ∀ x y, Commute (ψ 0 x) (ψ 1 y) := fun x y =>
    (datum_commute_mk hD (hC₁ y) (hC₀ x) (datum_commutator_mem hD h₁ _ (hr₁ y) _ (hr₀ x))).symm
  have hc02 : ∀ x y, Commute (ψ 0 x) (ψ 2 y) := fun x y =>
    (datum_commute_mk hD (hC₂ y) (hC₀ x) (datum_commutator_mem hD h₂ _ (hr₂ y) _ (hr₀ x))).symm
  have hc12 : ∀ x y, Commute (ψ 1 x) (ψ 2 y) := fun x y => by
    show QuotientGroup.mk' N _ * QuotientGroup.mk' N _ =
      QuotientGroup.mk' N _ * QuotientGroup.mk' N _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (hr₁ x) _ (hr₂ y))
  have hcomm' : ∀ i j, i ≠ j → ∀ x y, Commute (ψ i x) (ψ j y) := by
    intro i j hij x y
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hc01 x y
    · exact hc02 x y
    · exact (hc01 y x).symm
    · exact absurd rfl hij
    · exact hc12 x y
    · exact (hc02 y x).symm
    · exact (hc12 y x).symm
    · exact absurd rfl hij
  exact GH74.Filter.Lie.not_gen4_quotient_of_Q8_cube (P := C ⧸ N) ⊥ bot_le ψ hinj hcomm'
    (GH74.Gen4.quotient ⊥ (GH74.Gen4.quotient N (GH74.Gen4.subgroup C hF)))

end Quot

end CFSG.ClassicalInvolution.Q3.TA3
