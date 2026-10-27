module

public import CFSG.Goldschmidt.Statements

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem topFor_of_coreFor (Y : Type) [Group Y] [Finite Y]
    (h : CoreFor (Y ⧸ goldschmidtOddCore Y)) : TopFor Y := by
  intro S A hAS hAab hcl htop
  obtain ⟨Sbar, hSbar, hclbar⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed S A (goldschmidtOddCore Y) hAS hcl
  have hAbar : A.map (QuotientGroup.mk' (goldschmidtOddCore Y)) ≤ Sbar := by
    rw [hSbar]
    exact Subgroup.map_mono hAS
  obtain ⟨h1, h2, h3⟩ := h Sbar _ hAbar (isMulCommutative_map hAab _) hclbar
    (normalClosure_map_eq_top htop _ (QuotientGroup.mk'_surjective _))
    (goldschmidtOddCore_quotient_eq_bot Y)
  refine ⟨h1, ?_, h3⟩
  rw [hSbar] at h2
  exact h2

theorem goldFor_of_topFor (X : Type) [Group X] [Finite X] (h : ∀ M : Subgroup X, TopFor M) :
    GoldFor X := by
  intro S A hAS hAab hcl
  set M : Subgroup X := Subgroup.normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hMn.isSubnormal
  have hPeq : (P : Subgroup M) = (S : Subgroup X).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hAP : A.subgroupOf M ≤ (P : Subgroup M) := by
    rw [hPeq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAS (Subgroup.mem_subgroupOf.1 hx))
  have hcl' := stronglyClosed_subgroupOf S hcl hAM P hAP
  have htop := normalClosure_subgroupOf_eq_top S hAS hcl (M := M) rfl
  have hC := h M P (A.subgroupOf M) hAP (isMulCommutative_subgroupOf hAab M) hcl' htop
  rw [hPeq] at hC
  exact hC

theorem N1 : S_N1 := by
  intro n hIH X _ _ hX
  have htop : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → TopFor Y := by
    intro Y _ _ hY
    have hle : Nat.card (Y ⧸ goldschmidtOddCore Y) ≤ Nat.card Y := by
      rw [← Subgroup.index_eq_card]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    exact topFor_of_coreFor Y (hIH _ (lt_of_le_of_lt hle hY))
  exact ⟨htop X hX, goldFor_of_topFor X fun M =>
    htop M (lt_of_le_of_lt (Subgroup.card_le_card_group M) hX)⟩

end CFSG.Goldschmidt
