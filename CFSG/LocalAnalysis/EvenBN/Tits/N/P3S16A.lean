module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16AK
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16ABur

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

namespace S16A

theorem sixNine {Γ : Type*} [Group Γ] [Finite Γ] {K V S : Subgroup Γ} {t : Γ}
    (hVab : IsElemAbelian 2 V) (hVK : V ≤ K) (hVc : ∀ v ∈ V, ∀ k ∈ K, v * k = k * v)
    (ht2 : t * t = 1) (htK : t ∉ K) (htNK : t ∈ normalizer (K : Set Γ))
    (htNV : t ∈ normalizer (V : Set Γ))
    (hVt : ∀ w ∈ V, t * w * t⁻¹ = w → ∃ v ∈ V, w = v * (t * v⁻¹ * t⁻¹))
    (hCle : Nat.card ↥(K ⊓ centralizer ({t} : Set Γ)) ≤
      2 * Nat.card ↥(V ⊓ centralizer ({t} : Set Γ)))
    (hS : fusionIsSylowIn 2 S K) (hSt : ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    K = oddCoreSub K ⊔ V ∨
      (Nat.card ↥(K ⊓ centralizer ({t} : Set Γ)) =
          2 * Nat.card ↥(V ⊓ centralizer ({t} : Set Γ)) ∧
        ∃ _ : (V.subgroupOf (S ⊔ zpowers t)).Normal,
          ((∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(S ⊔ zpowers t) ⧸ V.subgroupOf (S ⊔ zpowers t) ≃*
              DihedralGroup (2 ^ m))) ∨
            ∃ k : ℕ, 4 ≤ k ∧ Nonempty (↥(S ⊔ zpowers t) ⧸ V.subgroupOf (S ⊔ zpowers t) ≃*
              SemidihedralGroup k)) ∧
          {x | ∃ c ∈ K, c * t * c⁻¹ = x} ∩ (S ⊔ zpowers t : Subgroup Γ) =
            {x | ∃ s ∈ S, s * t * s⁻¹ = x} ∧
          ∃ b : Γ, (∃ s ∈ S, b = s * t) ∧ b * b = 1 ∧
            ∀ x : Γ, (∃ s ∈ S, x = s * t) → x * x = 1 →
              (∃ s ∈ S, s * t * s⁻¹ = x) ∨ ∃ s ∈ S, s * b * s⁻¹ = x) := by
  have h : KHyp K V S t := ⟨hVab, hVK, hVc, ht2, htK, htNK, htNV, hVt, hCle, hS, hSt⟩
  have hSP : S ≤ S ⊔ zpowers t := le_sup_left
  have htP : t ∈ S ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  by_cases hSV : S = V
  · left
    have h1 := eq_oddCoreSub_sup_of_cyclic hVK hVc h.V_pGroup hS (g := 1) (one_mem S)
      (by rw [zpowers_one_eq_bot, bot_sup_eq]; exact hSV)
    rwa [hSV] at h1
  · right
    have hP := h.pHyp
    haveI hVn : (V.subgroupOf (S ⊔ zpowers t)).Normal := hP.V_normal
    have hVP : V ≤ S ⊔ zpowers t := h.V_le_S.trans hSP
    have hne : S.subgroupOf (S ⊔ zpowers t) ≠ V.subgroupOf (S ⊔ zpowers t) := by
      intro heq
      apply hSV
      refine le_antisymm (fun s hs => ?_) h.V_le_S
      have h1 : (⟨s, hSP hs⟩ : ↥(S ⊔ zpowers t)) ∈ S.subgroupOf (S ⊔ zpowers t) :=
        Subgroup.mem_subgroupOf.2 hs
      rw [heq] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    have hSt' : ∀ x : Γ, (∃ s ∈ S, x = s * t) → ∃ x₀ : ↥(S ⊔ zpowers t), (x₀ : Γ) = x ∧
        x₀ ∉ S.subgroupOf (S ⊔ zpowers t) := by
      rintro x ⟨s, hs, rfl⟩
      have hxP : s * t ∈ S ⊔ zpowers t := mul_mem (hSP hs) htP
      refine ⟨⟨s * t, hxP⟩, rfl, fun hmem => h.t_notMem_S ?_⟩
      have := S.mul_mem (S.inv_mem hs) (Subgroup.mem_subgroupOf.1 hmem)
      simpa using this
    have hSt'' : ∀ x₀ : ↥(S ⊔ zpowers t), x₀ ∉ S.subgroupOf (S ⊔ zpowers t) →
        ∃ s ∈ S, (x₀ : Γ) = s * t := by
      intro x₀ hx₀
      rcases h.mem_P.1 x₀.2 with hx | hx
      · exact absurd (Subgroup.mem_subgroupOf.2 hx) hx₀
      · exact hx
    refine ⟨?_, hVn, dihedral_or_semidihedral hP hne, ?_, ?_⟩
    ·
      have h1 := card_centralizer_eq hP hne
      rw [card_subgroupOf_inf_centralizer hSP htP, card_subgroupOf_inf_centralizer hVP htP] at h1
      exact le_antisymm hCle
        (h1 ▸ Subgroup.card_le_of_le (inf_le_inf_right _ h.S_le))
    ·
      ext x
      constructor
      · rintro ⟨⟨c, hcK, rfl⟩, hxP⟩
        by_cases hcyc : IsCyclic ↥((S.subgroupOf (S ⊔ zpowers t)).map
            (QuotientGroup.mk' (V.subgroupOf (S ⊔ zpowers t))))
        · obtain ⟨g, hgS, hSg⟩ := h.exists_gen hcyc
          have hKS := eq_oddCoreSub_sup_of_cyclic hVK hVc h.V_pGroup hS hgS hSg
          have hSO : S ≤ normalizer ((oddCoreSub K : Subgroup Γ) : Set Γ) := fun s hs => by
            rw [mem_normalizer_iff]
            intro o
            refine ⟨fun ho => oddCoreSub_conj (Subgroup.le_normalizer (h.S_le hs)) ho, fun ho => ?_⟩
            have := oddCoreSub_conj (g := s⁻¹) (Subgroup.inv_mem _
              (Subgroup.le_normalizer (h.S_le hs))) ho
            simpa [mul_assoc] using this
          have hcK' : c ∈ ((oddCoreSub K ⊔ S : Subgroup Γ) : Set Γ) := hKS ▸ hcK
          rw [coe_mul_of_right_le_normalizer_left (oddCoreSub K) S hSO] at hcK'
          obtain ⟨o, ho, s, hs, rfl⟩ := hcK'
          set t' := s * t * s⁻¹ with ht'
          have ht'P : t' ∈ S ⊔ zpowers t := mul_mem (mul_mem (hSP hs) htP) (inv_mem (hSP hs))
          have ht'N : t' ∈ normalizer (K : Set Γ) :=
            mul_mem (mul_mem (Subgroup.le_normalizer (h.S_le hs)) h.t_normK)
              (inv_mem (Subgroup.le_normalizer (h.S_le hs)))
          have ht'2 : t' * t' = 1 := by
            calc t' * t' = s * (t * t) * s⁻¹ := by rw [ht']; group
              _ = 1 := by rw [h.t_sq]; group
          have ho1 : o * (t' * o⁻¹ * t'⁻¹) ∈ oddCoreSub K := by
            refine Subgroup.mul_mem _ ho ?_
            have := oddCoreSub_conj ht'N (Subgroup.inv_mem _ ho)
            simpa using this
          have hx : (o * s) * t * (o * s)⁻¹ = (o * (t' * o⁻¹ * t'⁻¹)) * t' := by
            rw [ht']; group
          rw [hx] at hxP ⊢
          have hmem : o * (t' * o⁻¹ * t'⁻¹) ∈ S ⊔ zpowers t := by
            have := mul_mem hxP (inv_mem ht'P)
            simpa using this
          have h1 := eq_one_of_mem_of_isPGroup h.isPGroup_P hmem ho1
          rw [h1, one_mul]
          exact ⟨s, hs, rfl⟩
        ·
          have hxS : (⟨c * t * c⁻¹, hxP⟩ : ↥(S ⊔ zpowers t)) ∉ S.subgroupOf (S ⊔ zpowers t) := by
            intro hmem
            have hmem' : c * t * c⁻¹ ∈ K := h.S_le (Subgroup.mem_subgroupOf.1 hmem)
            apply h.t_notMem
            have := mul_mem (mul_mem (inv_mem hcK) hmem') hcK
            simpa [mul_assoc] using this
          have hx2 : (⟨c * t * c⁻¹, hxP⟩ : ↥(S ⊔ zpowers t)) *
              (⟨c * t * c⁻¹, hxP⟩ : ↥(S ⊔ zpowers t)) = 1 := by
            apply Subtype.ext
            show c * t * c⁻¹ * (c * t * c⁻¹) = 1
            calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
              _ = 1 := by rw [h.t_sq]; group
          obtain ⟨u, hu, hux⟩ := one_class_of_not_cyclic hP hne hcyc hxS hx2
          exact ⟨u, Subgroup.mem_subgroupOf.1 hu, congrArg Subtype.val hux⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, h.S_le hs, rfl⟩, mul_mem (mul_mem (hSP hs) htP) (inv_mem (hSP hs))⟩
    ·
      by_cases hcyc : IsCyclic ↥((S.subgroupOf (S ⊔ zpowers t)).map
          (QuotientGroup.mk' (V.subgroupOf (S ⊔ zpowers t))))
      · obtain ⟨b, hb, hb2, hcl⟩ := two_classes_of_cyclic hP hne hcyc
        obtain ⟨s₀, hs₀, hbs⟩ := hSt'' b hb
        refine ⟨(b : Γ), ⟨s₀, hs₀, hbs⟩, congrArg Subtype.val hb2, fun x hx hx2 => ?_⟩
        obtain ⟨x₀, hx₀, hx₀S⟩ := hSt' x hx
        have hx₀2 : x₀ * x₀ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hx₀]; exact hx2)
        rcases hcl x₀ hx₀S hx₀2 with ⟨u, hu, hux⟩ | ⟨u, hu, hux⟩
        · left
          exact ⟨u, Subgroup.mem_subgroupOf.1 hu, by rw [← hx₀]; exact congrArg Subtype.val hux⟩
        · right
          exact ⟨u, Subgroup.mem_subgroupOf.1 hu, by rw [← hx₀]; exact congrArg Subtype.val hux⟩
      · refine ⟨t, ⟨1, S.one_mem, by rw [one_mul]⟩, h.t_sq, fun x hx hx2 => Or.inl ?_⟩
        obtain ⟨x₀, hx₀, hx₀S⟩ := hSt' x hx
        have hx₀2 : x₀ * x₀ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hx₀]; exact hx2)
        obtain ⟨u, hu, hux⟩ := one_class_of_not_cyclic hP hne hcyc hx₀S hx₀2
        exact ⟨u, Subgroup.mem_subgroupOf.1 hu, by rw [← hx₀]; exact congrArg Subtype.val hux⟩

end S16A

end CFSG.LocalAnalysis.EvenBN.Tits.N
