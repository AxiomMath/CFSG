module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128A5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_oTwoRes_cent {Y0 : Type} [Group Y0] {τ0 : Y0} {X0 : Subgroup Y0}
    (hτ2 : τ0 * τ0 = 1) (hA5 : Nonempty (↥X0 ≃* ↥(alternatingGroup (Fin 5)))) (hτX : τ0 ∉ X0)
    (hcomm : ∀ x ∈ X0, τ0 * x = x * τ0)
    (hcases : ∀ y ∈ centralizer ({τ0} : Set Y0), y ∈ X0 ∨ ∃ x ∈ X0, y = τ0 * x) :
    oTwoRes (centralizer ({τ0} : Set Y0)) = X0 := by
  unfold oTwoRes
  have hset : {x : Y0 | x ∈ centralizer ({τ0} : Set Y0) ∧ Odd (orderOf x)} =
      {x : Y0 | x ∈ X0 ∧ Odd (orderOf x)} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyC, hodd⟩
      refine ⟨?_, hodd⟩
      rcases hcases y hyC with h | ⟨x, hx, rfl⟩
      · exact h
      · exfalso
        have hc : Commute τ0 x := hcomm x hx
        obtain ⟨k, hk⟩ := hodd
        have hpow : (τ0 * x) ^ orderOf (τ0 * x) = 1 := pow_orderOf_eq_one _
        rw [hc.mul_pow, hk, pow_succ, pow_mul, pow_two, hτ2, one_pow, one_mul] at hpow
        have hxm : x ^ (2 * k + 1) ∈ X0 := X0.pow_mem hx _
        apply hτX
        have h1 : τ0 = (x ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left hpow
        rw [h1]
        exact X0.inv_mem hxm
    · rintro ⟨hyX, hodd⟩
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hyX).symm, hodd⟩
  rw [hset]
  exact sec128_closure_odd_of_alt5 hA5

theorem sec128_oTwoRes_sub {M : Type} [Group M] {Y Xt : Subgroup M} {τ : M} (hτY : τ ∈ Y)
    (hXY : Xt ≤ Y) (hτ2 : τ * τ = 1)
    (hA5 : Nonempty (↥Xt ≃* ↥(alternatingGroup (Fin 5)))) (hτX : τ ∉ Xt)
    (hcomm : ∀ x ∈ Xt, τ * x = x * τ)
    (hcases : ∀ y ∈ Y, y * τ = τ * y → y ∈ Xt ∨ ∃ x ∈ Xt, y = τ * x) :
    oTwoRes (centralizer ({(⟨τ, hτY⟩ : ↥Y)} : Set ↥Y)) = Xt.subgroupOf Y := by
  have hX'A5 : Nonempty (↥(Xt.subgroupOf Y) ≃* ↥(alternatingGroup (Fin 5))) :=
    hA5.map fun e => (Subgroup.subgroupOfEquivOfLe hXY).trans e
  refine sec128_oTwoRes_cent (Subtype.ext hτ2) hX'A5 (fun h => hτX (Subgroup.mem_subgroupOf.mp h))
    (fun x hx => Subtype.ext (hcomm x (Subgroup.mem_subgroupOf.mp hx))) ?_
  intro y hy
  have hyc : (y : M) * τ = τ * (y : M) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  rcases hcases y y.2 hyc with h | ⟨x, hx, hxy⟩
  · exact Or.inl (Subgroup.mem_subgroupOf.mpr h)
  · exact Or.inr ⟨⟨x, hXY hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxy⟩

theorem sec128_z2a5_hyps {M : Type} [Group M] {Y Xt : Subgroup M} {τ : M} (hτY : τ ∈ Y)
    (hXY : Xt ≤ Y) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hA5 : Nonempty (↥Xt ≃* ↥(alternatingGroup (Fin 5)))) (hτX : τ ∉ Xt)
    (hcomm : ∀ x ∈ Xt, τ * x = x * τ)
    (hcases : ∀ y ∈ Y, y * τ = τ * y → y ∈ Xt ∨ ∃ x ∈ Xt, y = τ * x)
    (hK : Nonempty (↥(Y ⊓ centralizer ({τ} : Set M)) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))))
    (hfus : ∀ y : M, ((∃ b ∈ Y, y = b * τ * b⁻¹) ∧ y ∈ centralizer ({τ} : Set M)) ↔
      ((∃ x ∈ Xt, y = τ * x) ∧ y * y = 1 ∧ y ≠ 1)) :
    orderOf (⟨τ, hτY⟩ : ↥Y) = 2 ∧
      Nonempty (↥(centralizer ({(⟨τ, hτY⟩ : ↥Y)} : Set ↥Y)) ≃*
        (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))) ∧
      ∀ y : ↥Y, (y ∈ conjClassIn ⊤ (⟨τ, hτY⟩ : ↥Y) ∧
          y ∈ centralizer ({(⟨τ, hτY⟩ : ↥Y)} : Set ↥Y)) ↔
        (∃ x ∈ oTwoRes (centralizer ({(⟨τ, hτY⟩ : ↥Y)} : Set ↥Y)),
          y = (⟨τ, hτY⟩ : ↥Y) * x ∧ y * y = 1) := by
  set τ' : ↥Y := ⟨τ, hτY⟩ with hτ'
  have hτ2' : τ' * τ' = 1 := Subtype.ext hτ2
  have hτ1' : τ' ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  have hO : oTwoRes (centralizer ({τ'} : Set ↥Y)) = Xt.subgroupOf Y :=
    sec128_oTwoRes_sub hτY hXY hτ2 hA5 hτX hcomm hcases
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hτ2') hτ1', ?_, ?_⟩
  · have hcen : centralizer ({τ'} : Set ↥Y) =
        (Y ⊓ centralizer ({τ} : Set M)).subgroupOf Y := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subtype.ext_iff, Subgroup.coe_mul]
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    rw [hcen]
    exact hK.map fun e => (Subgroup.subgroupOfEquivOfLe inf_le_left).trans e
  · intro y
    rw [hO]
    constructor
    · rintro ⟨⟨h, -, hyh⟩, hyc⟩
      have hyM : (y : M) = (h : M) * τ * (h : M)⁻¹ := congrArg Subtype.val hyh
      have hyc' : (y : M) ∈ centralizer ({τ} : Set M) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyc)
      obtain ⟨⟨x, hx, hxy⟩, hy2, -⟩ := (hfus y).mp ⟨⟨h, h.2, hyM⟩, hyc'⟩
      exact ⟨⟨x, hXY hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxy,
        Subtype.ext hy2⟩
    · rintro ⟨x, hx, hxy, hy2⟩
      have hxXt : (x : M) ∈ Xt := Subgroup.mem_subgroupOf.mp hx
      have hyM : (y : M) = τ * (x : M) := congrArg Subtype.val hxy
      have hy2M : (y : M) * (y : M) = 1 := congrArg Subtype.val hy2
      have hy1 : (y : M) ≠ 1 := by
        intro h
        apply hτX
        rw [hyM] at h
        have : τ = (x : M)⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [this]
        exact Xt.inv_mem hxXt
      obtain ⟨⟨b, hb, hyb⟩, hyc⟩ := (hfus y).mpr ⟨⟨x, hxXt, hyM⟩, hy2M, hy1⟩
      refine ⟨⟨⟨b, hb⟩, Subgroup.mem_top _, Subtype.ext hyb⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyc)

end CFSG.OddStandard.SmallF3.Omega
