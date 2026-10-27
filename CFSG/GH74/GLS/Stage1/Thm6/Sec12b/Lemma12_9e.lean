module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9d

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

namespace Ph0

theorem xax (H : Hyp129 G x z S T P Q Rd F) {a : G} (A : Ph0 G x z S T P a) :
    x * a * x = a * z := by
  calc x * a * x = a * (a⁻¹ * x * a) * x := by group
    _ = a * (x * z) * x := by rw [A.xa']
    _ = a * (x * z * x) := by group
    _ = a * (z * x * x) := by rw [(H.hz.z_central x H.base.x_mem_T).symm]
    _ = a * z := by rw [mul_assoc, H.base.x_sq, mul_one]

end Ph0

namespace Ph1

variable (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
  (B : Ph1 G x z T P Rd a V P₁ F')
include H A B

omit A in
theorem x_not_mem_P1 : x ∉ P₁ := by
  intro hx
  have : x ∈ P₁ ⊓ Subgroup.zpowers x := ⟨hx, Subgroup.mem_zpowers x⟩
  rw [B.inf_x, Subgroup.mem_bot] at this
  exact H.base.x_ne_one this

omit A in
theorem z_mem_P1 : z ∈ P₁ := B.P_le H.hz.z_mem_P

theorem case3a (hF : F' = Subgroup.zpowers x) : False := by
  have hxRd : x ∈ Rd := H.x_mem_Rd
  have hTRd : Rd = T := by
    have h1 := B.T_eq
    rw [hF] at h1
    exact (sup_eq_left.2 ((Subgroup.zpowers_le).2 hxRd)).symm.trans h1
  have hdecomp : ∀ t ∈ T, ∃ p ∈ P₁, t = p ∨ t = p * x := by
    intro t ht
    rw [← hTRd, ← B.sup_x] at ht
    obtain ⟨p, hp, c, hc, hpc⟩ := mem_sup_of_commute
      (comm_zpowers (fun u hu => H.base.x_central u (B.P1_le_T H hu))) ht
    rcases zpowers_sq_cases H.base.x_sq hc with h1 | h1
    · exact ⟨p, hp, Or.inl (by rw [hpc, h1, mul_one])⟩
    · exact ⟨p, hp, Or.inr (by rw [hpc, h1])⟩
  have hcos : ∀ s ∈ S, s ∉ T → a⁻¹ * s ∈ T := fun s hs hsT => H.coset_eq A.a_mem hs A.a_not hsT
  have hxcT : ∀ q ∈ T, x⁻¹ * q * x = q := by
    intro q hq
    have h1 := H.base.x_central q hq
    calc x⁻¹ * q * x = x⁻¹ * (q * x) := by group
      _ = x⁻¹ * (x * q) := by rw [h1]
      _ = q := by group
  have hxS : x ∈ S := H.base.T_le_S H.base.x_mem_T
  have hP₁S : P₁ ≤ S := (B.P1_le_T H).trans H.base.T_le_S
  have hxP₁ := B.x_not_mem_P1 H
  have caseII : ∀ p₀ ∈ P₁, a * a = p₀ * x → False := by
    intro p₀ hp₀ ha2
    have hcycT : ∀ t ∈ T, ∃ k : ℤ, (a ^ k)⁻¹ * t ∈ P₁ := by
      intro t ht
      obtain ⟨p, hp, h | h⟩ := hdecomp t ht
      · exact ⟨0, by rw [h]; simpa using hp⟩
      · refine ⟨2, ?_⟩
        rw [h, zpow_two, ha2]
        have hq : p₀⁻¹ * p ∈ T := T.mul_mem (T.inv_mem (B.P1_le_T H hp₀)) (B.P1_le_T H hp)
        have e : (p₀ * x)⁻¹ * (p * x) = x⁻¹ * (p₀⁻¹ * p) * x := by group
        rw [e, hxcT _ hq]
        exact P₁.mul_mem (P₁.inv_mem hp₀) hp
    have hcyc : ∀ t ∈ S, ∃ k : ℤ, (a ^ k)⁻¹ * t ∈ P₁ := by
      intro t ht
      by_cases htT : t ∈ T
      · exact hcycT t htT
      · obtain ⟨k', hk'⟩ := hcycT _ (hcos t ht htT)
        refine ⟨k' + 1, ?_⟩
        have e : (a ^ (k' + 1))⁻¹ * t = (a ^ k')⁻¹ * (a⁻¹ * t) := by group
        rw [e]; exact hk'
    exact B.x_transfer_false H A hP₁S (B.P1_normalS H A) (fun y hy _ => hy) hxP₁ A.a_mem
      hcyc
  have caseI : a * a ∈ P₁ → False := by
    intro ha2
    have hNorm : NormalIn P₁ S := ⟨hP₁S, B.P1_normalS H A⟩
    have hmemN : ∀ y ∈ P₁ ⊔ Subgroup.zpowers a, y ∈ P₁ ∨ ∃ p ∈ P₁, y = a * p := by
      intro y hy
      obtain ⟨a', ha', p, hp, hyd⟩ := mem_sup_zpowers_of_normalIn hNorm A.a_mem hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
      · left
        have e : a ^ (2 * m) = (a * a) ^ m := by rw [zpow_mul, zpow_two]
        rw [hyd, e]
        exact P₁.mul_mem (P₁.zpow_mem ha2 m) hp
      · right
        have e : a ^ (2 * m + 1) = a * (a * a) ^ m := by
          rw [zpow_add_one, zpow_mul, zpow_two]
          exact ((Commute.refl a).mul_right (Commute.refl a)).zpow_right m |>.symm.eq
        refine ⟨(a * a) ^ m * p, P₁.mul_mem (P₁.zpow_mem ha2 m) hp, ?_⟩
        rw [hyd, e, mul_assoc]
    have haN : a ∈ P₁ ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    have hPN : P₁ ≤ P₁ ⊔ Subgroup.zpowers a := le_sup_left
    have hNS : P₁ ⊔ Subgroup.zpowers a ≤ S := sup_le hP₁S ((Subgroup.zpowers_le).2 A.a_mem)
    have hxax : x * a * x⁻¹ = a * z := by
      have : x⁻¹ = x := inv_eq_of_mul_eq_one_right H.base.x_sq
      rw [this]; exact Ph0.xax H A
    have hzT : ∀ p ∈ T, p * z * p⁻¹ = z := by
      intro p hp
      have h1 := H.hz.z_central p hp
      calc p * z * p⁻¹ = (z * p) * p⁻¹ := by rw [h1]
        _ = z := by group
    have hconjP : ∀ p ∈ P₁, p * a * p⁻¹ ∈ P₁ ⊔ Subgroup.zpowers a := by
      intro p hp
      have h1 : a⁻¹ * p * a⁻¹⁻¹ ∈ P₁ := B.P1_normalS H A a⁻¹ (S.inv_mem A.a_mem) p hp
      have e : p * a * p⁻¹ = a * ((a⁻¹ * p * a⁻¹⁻¹) * p⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ haN (hPN (P₁.mul_mem h1 (P₁.inv_mem hp)))
    have hconjT : ∀ t ∈ T, t * a * t⁻¹ ∈ P₁ ⊔ Subgroup.zpowers a := by
      intro t ht
      obtain ⟨p, hp, h | h⟩ := hdecomp t ht
      · rw [h]; exact hconjP p hp
      · have e : (p * x) * a * (p * x)⁻¹ = (p * a * p⁻¹) * (p * z * p⁻¹) := by
          calc (p * x) * a * (p * x)⁻¹ = p * (x * a * x⁻¹) * p⁻¹ := by group
            _ = p * (a * z) * p⁻¹ := by rw [hxax]
            _ = (p * a * p⁻¹) * (p * z * p⁻¹) := by group
        rw [h, e, hzT p (B.P1_le_T H hp)]
        exact Subgroup.mul_mem _ (hconjP p hp) (hPN (B.z_mem_P1 H))
    have hNn : ∀ t ∈ S, ∀ q ∈ P₁ ⊔ Subgroup.zpowers a,
        t * q * t⁻¹ ∈ P₁ ⊔ Subgroup.zpowers a := by
      intro t ht
      have hle : P₁ ⊔ Subgroup.zpowers a ≤ Hconj t (P₁ ⊔ Subgroup.zpowers a) := by
        refine sup_le (fun c hc => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [mem_Hconj]
          exact hPN (B.P1_normalS H A t ht c hc)
        · rw [mem_Hconj]
          by_cases htT : t ∈ T
          · exact hconjT t htT
          · have ht' : a⁻¹ * t ∈ T := hcos t ht htT
            have e : t * a * t⁻¹ = a * ((a⁻¹ * t) * a * (a⁻¹ * t)⁻¹) * a⁻¹ := by group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN (hconjT _ ht')) (Subgroup.inv_mem _ haN)
      intro q hq
      exact mem_Hconj.1 (hle hq)
    have hNT : ∀ y ∈ P₁ ⊔ Subgroup.zpowers a, y ∈ T → y ∈ P₁ := by
      intro y hy hyT
      rcases hmemN y hy with h | ⟨p, hp, hyp⟩
      · exact h
      · exfalso
        apply A.a_not
        have : a = y * p⁻¹ := by rw [hyp]; group
        rw [this]
        exact T.mul_mem hyT (T.inv_mem (B.P1_le_T H hp))
    have hxN : x ∉ P₁ ⊔ Subgroup.zpowers a := by
      intro hx
      rcases hmemN x hx with h | ⟨p, hp, hxp⟩
      · exact hxP₁ h
      · apply A.a_not
        have : a = x * p⁻¹ := by rw [hxp]; group
        rw [this]
        exact T.mul_mem H.base.x_mem_T (T.inv_mem (B.P1_le_T H hp))
    have hcyc : ∀ t ∈ S, ∃ k : ℤ, (x ^ k)⁻¹ * t ∈ P₁ ⊔ Subgroup.zpowers a := by
      intro t ht
      by_cases htT : t ∈ T
      · obtain ⟨p, hp, h | h⟩ := hdecomp t htT
        · exact ⟨0, by rw [h]; simpa using hPN hp⟩
        · refine ⟨1, ?_⟩
          rw [h, zpow_one, ← mul_assoc, hxcT p (B.P1_le_T H hp)]
          exact hPN hp
      · obtain ⟨p, hp, h | h⟩ := hdecomp _ (hcos t ht htT)
        · refine ⟨0, ?_⟩
          have : t = a * p := by
            have e : t = a * (a⁻¹ * t) := by group
            rw [e, h]
          rw [this, zpow_zero]
          simpa using Subgroup.mul_mem _ haN (hPN hp)
        · refine ⟨1, ?_⟩
          have : t = a * (p * x) := by
            have e : t = a * (a⁻¹ * t) := by group
            rw [e, h]
          rw [this, zpow_one]
          have e2 : x⁻¹ * (a * (p * x)) = (x⁻¹ * a * x) * (x⁻¹ * p * x) := by group
          have hxinv : x⁻¹ * a * x = a * z := by
            rw [inv_eq_of_mul_eq_one_right H.base.x_sq]; exact Ph0.xax H A
          rw [e2, hxinv, hxcT p (B.P1_le_T H hp)]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN (hPN (B.z_mem_P1 H))) (hPN hp)
    exact B.x_transfer_false H A hNS hNn hNT hxN hxS hcyc
  obtain ⟨p₀, hp₀, h | h⟩ := hdecomp _ A.a_sq
  · exact caseI (by rw [h]; exact hp₀)
  · exact caseII p₀ hp₀ h

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
