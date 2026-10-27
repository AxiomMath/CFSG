module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L33F

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx, pow_two] at h
  exact h

theorem false_of_conjugate_mem [Finite G] (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36)
    (h39 : Asc82Lemma39) (hInner : Asc82OmegaPlusInner) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {g : G}
    (hsL : g⁻¹ * t * g ∈ L) : False := by
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact hS.involution
  have hS' := hS.conjugate g
  have hL'F : InFStar (CFSG.conjugate L g) := Or.inl hS'.inF
  by_cases hp : IsI4PlusIn L (g⁻¹ * t * g)
  · obtain ⟨-, K, hK⟩ := hp
    have hD := sec3PocketData_of_sl23PocketIn hS.involution hS.component (Or.inl hS.inF)
      (conjugate_eq_self_of_lemma36 h36 hS) hs2 hK
    exact h34c G t L hS t L _ K hD _ hS'.component hL'F
  · obtain ⟨X, u, hXc, hsX, hX2, -⟩ := hInner G L ⟨hS.inF, hΩ⟩ _ hs2 hsL hp
    have h := h39 G t L hS _ X hs2 hsL hsX hXc hX2
    have hLX : CFSG.conjugate L g = X := h.2.2 _ hS'.component hL'F
    have hΩ' := lieModel_quotient_oddCore_conjugate g hΩ
    subst hLX
    exact false_of_isTwoU43_of_pOmegaPlus hX2 hΩ'

theorem isConj_of_commuting_conjugate [Finite G] (h33 : Asc82Lemma33F) (h34c : Asc82Lemma34c)
    (h36 : Asc82Lemma36) (h39 : Asc82Lemma39) (hInner : Asc82OmegaPlusInner)
    (hOuter : Asc82OmegaPlusOuter) (hPC : Asc82OmegaPlusPocketedConj)
    (hPL : Asc82OmegaPlusPocketLift) (hCl : Asc82OmegaPlusClosure) (hCS : Asc82OmegaPlusCStar)
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {z : G} (hz : IsI4PlusIn L z) {g : G}
    (hne : g⁻¹ * t * g ≠ t) (hst : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g)) :
    IsConj (t * z) t := by
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hcomm : ∀ l ∈ L, l * t = t * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLt hl)
  have ht2 := hS.involution
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact ht2
  have hΩL : IsOmegaPlusIn L := ⟨hS.inF, hΩ⟩
  have hcyc : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic ↥(P : Subgroup (centralizer (L : Set G))) :=
    h33 G t L hS L (hCS G t L hS hΩ) hS.inF
  have htC : t ∈ centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr hcomm
  have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  by_cases hin : ∃ a ∈ L, ∃ c ∈ centralizer (L : Set G), g⁻¹ * t * g = a * c
  · obtain ⟨a, ha, c, hc, hs⟩ := hin
    obtain ⟨a', c', ha', hc', ha2, hc2, hs'⟩ := exists_involution_decomposition hΩ ha hc hs
      (mul_self_eq_one_of_orderOf_eq_two hs2)
    by_cases ha1 : a' = 1
    · exfalso
      have hsCL : g⁻¹ * t * g ∈ centralizer (L : Set G) := by
        rw [hs', ha1, one_mul]; exact hc'
      have hkl := eq_of_commuting_involutions_of_cyclic_sylow hcyc
        (a := (⟨g⁻¹ * t * g, hsCL⟩ : centralizer (L : Set G)))
        (b := (⟨t, htC⟩ : centralizer (L : Set G)))
        (by rw [Subgroup.orderOf_mk]; exact hs2) (by rw [Subgroup.orderOf_mk]; exact ht2)
        (Subtype.ext hst)
      exact hne (congrArg Subtype.val hkl)
    · by_cases hc1 : c' = 1
      · exact (false_of_conjugate_mem h34c h36 h39 hInner hS hΩ
          (by rw [hs', hc1, mul_one]; exact ha')).elim
      · have hc'2 : orderOf c' = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
        have ha'2 : orderOf a' = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
        have hct : c' * t = t * c' := by
          have h1 : a' * (c' * t) = a' * (t * c') := by
            calc a' * (c' * t) = a' * c' * t := (mul_assoc _ _ _).symm
              _ = t * (a' * c') := by rw [← hs']; exact hst
              _ = t * a' * c' := (mul_assoc _ _ _).symm
              _ = a' * t * c' := by rw [← hcomm a' ha']
              _ = a' * (t * c') := mul_assoc _ _ _
          exact mul_left_cancel h1
        have hceq := eq_of_commuting_involutions_of_cyclic_sylow hcyc
          (a := (⟨c', hc'⟩ : centralizer (L : Set G))) (b := (⟨t, htC⟩ : centralizer (L : Set G)))
          (by rw [Subgroup.orderOf_mk]; exact hc'2) (by rw [Subgroup.orderOf_mk]; exact ht2)
          (Subtype.ext hct)
        have hc't : c' = t := congrArg Subtype.val hceq
        exact isConj_of_inner_partner h36 hInner hPC hPL hS hΩ hz ha'2 ha' g
          (by rw [hs', hc't])
  · have hsn : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
      mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS _ hsC)
    obtain ⟨u, hu, hu2, a, haL, ha⟩ := hOuter G L hΩL _ hs2 hsn hin
    have hF : ∀ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) →
        InFStar J := fun J hJ => hCl G L hΩL _ hs2 hsn J hJ
    have huL' : u ∈ CFSG.conjugate L g := layer_le_conjugate h36 hS rfl hst hF hu
    have hconj := isConj_of_inner_partner h36 hInner hPC hPL (hS.conjugate g)
      (lieModel_quotient_oddCore_conjugate g hΩ) (hz.conjugate g) hu2 huL' a ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine isConj_iff.2 ⟨g * c * g⁻¹, ?_⟩
    have h1 : c * (g⁻¹ * (t * z) * g) * c⁻¹ = g⁻¹ * t * g := by
      rw [← hc]
      group
    calc g * c * g⁻¹ * (t * z) * (g * c * g⁻¹)⁻¹
        = g * (c * (g⁻¹ * (t * z) * g) * c⁻¹) * g⁻¹ := by group
      _ = t := by rw [h1]; group

theorem isConj_of_omegaPlus [Finite G] (h33 : Asc82Lemma33F) (h34c : Asc82Lemma34c)
    (h36 : Asc82Lemma36) (h39 : Asc82Lemma39) (hInner : Asc82OmegaPlusInner)
    (hOuter : Asc82OmegaPlusOuter) (hPC : Asc82OmegaPlusPocketedConj)
    (hPL : Asc82OmegaPlusPocketLift) (hCl : Asc82OmegaPlusClosure) (hCS : Asc82OmegaPlusCStar)
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {z : G} (hz : IsI4PlusIn L z) :
    IsConj (t * z) t := by
  have hnc : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨x, hxL, hx⟩ := SetLike.not_le_iff_exists.mp hS.component.not_le_centralizer
    rw [Subgroup.mem_centralizer_iff] at hx
    push_neg at hx
    obtain ⟨y, -, hy⟩ := hx
    exact ⟨y, x, hy⟩
  obtain ⟨g, hne, hst⟩ := exists_conj_commute_ne hS.simple hS.involution hnc
  exact isConj_of_commuting_conjugate h33 h34c h36 h39 hInner hOuter hPC hPL hCl hCS hS hΩ hz
    hne hst

end CFSG.OddStandard.SmallF3.Omega
