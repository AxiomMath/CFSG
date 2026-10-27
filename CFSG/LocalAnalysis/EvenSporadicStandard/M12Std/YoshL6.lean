module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelChecks
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshIndexArith
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshNoExtraFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFuseNormalizer

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Fusion

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem l6_fusion (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hue : ueCheck α k = true) (hl6 : l6Check α k = true) :
    ∃ y₁ : G, Nat.card (Nn e₀ ⊓ centralizer ({y₁} : Set G) : Subgroup G) = 128 ∧
      ∀ y ∈ EG E, IsConj e y →
        (∃ n ∈ Nn e₀, n * e * n⁻¹ = y) ∨ (∃ n ∈ Nn e₀, n * y₁ * n⁻¹ = y) := by
  obtain ⟨hEs, -⟩ := ueCheck_enum hue
  have hELe : tsub (wgens α k eWords) ≤ NG α k := tsub_wgens_le D hEs.perm
  unfold l6Check l6Core at hl6
  obtain ⟨T₁, hT₁, h1⟩ := List.any_eq_true.1 hl6
  rw [Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨hcard, hall⟩ := h1
  obtain ⟨hrep₁, hmem₁⟩ := hEs.rep_mem (Array.mem_toList_iff.1 hT₁)
  have hg₁ : tablePerm 16 T₁ ∈ NG α k := hELe hmem₁
  refine ⟨ψ E (tablePerm 16 T₁), ?_, ?_⟩
  · rw [card_Nn_centralizer D E hrep₁ hg₁]
    exact hcard
  · intro y hy hconj
    obtain ⟨g, hgN, hgK, rfl⟩ := (mem_img' E).1 hy
    obtain ⟨T, hT, hrep⟩ := hEs.exists_entry hgK
    have hall' := List.all_eq_true.1 hall T (Array.mem_toList_iff.2 hT)
    have hgood : memTab 16 (goodTabs α k) T = true :=
      (memTab_good_iff D E he2 hrep hgN).2 (by rwa [← ψ_of_mem E hgN])
    rw [hgood] at hall'
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hall'
    rcases hall' with h | h
    · left
      obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound D.hsz D.hnC (rep_nwT D eWord) hrep h
      obtain ⟨n, hn, hnn⟩ := exists_conj_Nn E (wp_mem α k _) hgN ⟨m, hm, hmm⟩
      rw [ψ_e E he2] at hnn
      exact ⟨n, hn, hnn⟩
    · right
      obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound D.hsz D.hnC hrep₁ hrep h
      obtain ⟨n, hn, hnn⟩ := exists_conj_Nn E hg₁ hgN ⟨m, hm, hmm⟩
      exact ⟨n, hn, hnn⟩

theorem conj_mem_of_relIndex_two {Γ : Type*} [Group Γ] (S P : Subgroup Γ) (hSP : S ≤ P)
    (h : S.relIndex P = 2) : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S := by
  have hn : (S.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two h
  intro p hp s hs
  have := hn.conj_mem ⟨s, hSP hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨p, hp⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem not_commute_d_e (hd : CentralSwap e₀ α d) : d * e ≠ e * d := by
  intro h
  have h2 : d * e * d⁻¹ = e := by rw [h]; group
  rw [hd.conj_e] at h2
  exact cG_ne_one e₀ (by simpa using h2)

theorem yosh6 [Finite G] (hG : IsSimpleGroup G) (M : ModelChecks) (he2 : orderOf e = 2)
    (hα : α = 0 ∨ α = 1) (hd : CentralSwap e₀ α d) : α = 1 := by
  by_contra hne
  have hα0 : α = 0 := by omega
  subst hα0
  obtain ⟨k, hk, Ψ, hinj, hrange, hgen, hrel⟩ := yosh5 e₀ he2 (by norm_num) hd
  let E : NEmb e₀ d 0 k := ⟨Ψ, hinj, hrange, hgen, hrel⟩
  have D := M.fusion 0 k (by norm_num) hk
  have hue := M.ue 0 k (by norm_num) hk
  have F := esFacts D E hue (M.es 0 k (by norm_num) hk)
  obtain ⟨y₁, hCy, hX⟩ := l6_fusion D E he2 hue (M.l6 k hk)
  haveI := hG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hee : e * e = 1 := by
    rw [← pow_two, ← he2, pow_orderOf_eq_one]
  have hna : ∃ a b : G, a * b ≠ b * a := ⟨d, e, not_commute_d_e hd⟩
  have hcount : Nat.card {y : ↥(Nn e₀) // IsConj e (y : G)} = 80 := card_isConj_e D E he2
  have hfac : (Nat.card G).factorization 2 = 11 :=
    factorization_eq_eleven hna hee (Nn e₀) (card_Nn e₀ he2 hd)
      (by rw [card_cent_e e₀]; norm_num) hcount
  have hG12 : ¬ 2 ^ 12 ∣ Nat.card G := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hfac]
    norm_num
  have hSp : IsPGroup 2 (SG E) := IsPGroup.of_card (n := 10) (by rw [F.cardS]; norm_num)
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup G) = 2 ^ 11 := by
    rw [P.card_eq_multiplicity, hfac]
  have hrelS : (SG E).relIndex (P : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := SG E) (K := (P : Subgroup G))
    rw [inf_eq_left.2 hSP, hPcard, F.cardS] at h
    omega
  have hSn := conj_mem_of_relIndex_two (SG E) (P : Subgroup G) hSP hrelS
  have hPE : ∀ p ∈ (P : Subgroup G), ∀ x ∈ EG E, p * x * p⁻¹ ∈ EG E := by
    intro p hp
    have hpc : p * cG e₀ * p⁻¹ = cG e₀ := by
      have hc' : p * cG e₀ * p⁻¹ ∈ SG E := hSn p hp _ (F.ES F.cE)
      have hcen : ∀ s ∈ SG E, (p * cG e₀ * p⁻¹) * s = s * (p * cG e₀ * p⁻¹) := by
        intro s hs
        have hs' : p⁻¹ * s * p ∈ SG E := by
          simpa using hSn p⁻¹ ((P : Subgroup G).inv_mem hp) s hs
        have h := F.cSZ _ hs'
        calc (p * cG e₀ * p⁻¹) * s = p * (cG e₀ * (p⁻¹ * s * p)) * p⁻¹ := by group
          _ = p * ((p⁻¹ * s * p) * cG e₀) * p⁻¹ := by rw [h]
          _ = s * (p * cG e₀ * p⁻¹) := by group
      rcases F.ZS _ hc' hcen with h | h
      · exfalso
        apply cG_ne_one e₀
        have : cG e₀ = p⁻¹ * (p * cG e₀ * p⁻¹) * p := by group
        rw [this, h]; group
      · exact h
    let D' : Subgroup G := conjSubgroup p (EG E)
    have hDS : D' ≤ SG E := by
      intro y hy
      have h1 : p⁻¹ * y * p ∈ EG E := mem_conjSubgroup.1 hy
      have := hSn p hp _ (F.ES h1)
      have e : p * (p⁻¹ * y * p) * p⁻¹ = y := by group
      rwa [e] at this
    have hsq : ∀ y ∈ D', y * y = 1 ∨ y * y = cG e₀ := by
      intro y hy
      have h1 : p⁻¹ * y * p ∈ EG E := mem_conjSubgroup.1 hy
      have hy2 : y * y = p * ((p⁻¹ * y * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
      rcases F.sq _ h1 with h | h
      · left; rw [hy2, h]; group
      · right; rw [hy2, h, hpc]
    have hcm : ∀ y ∈ D', ∀ z ∈ D', ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = cG e₀ := by
      intro y hy z hz
      have h1 : p⁻¹ * y * p ∈ EG E := mem_conjSubgroup.1 hy
      have h2 : p⁻¹ * z * p ∈ EG E := mem_conjSubgroup.1 hz
      have hyz : ⁅y, z⁆ = p * ⁅p⁻¹ * y * p, p⁻¹ * z * p⁆ * p⁻¹ := by
        simp only [commutatorElement_def]; group
      rcases F.comm _ h1 _ h2 with h | h
      · left; rw [hyz, h]; group
      · right; rw [hyz, h, hpc]
    have hD := F.uniq D' hDS (by rw [card_conjSubgroup, F.cardE]) hsq hcm
    intro x hx
    have : p * x * p⁻¹ ∈ D' := mul_mul_inv_mem_conjSubgroup hx
    rwa [hD] at this
  have hCL : ∀ g : G, g * e = e * g → (∀ x ∈ EG E, g * x * g⁻¹ ∈ EG E) → g ∈ Nn e₀ := by
    intro g hge hgE
    have hinv := conj_inv_mem (EG E) g hgE
    have hgc : g * cG e₀ * g⁻¹ = cG e₀ := by
      have hc'E : g * cG e₀ * g⁻¹ ∈ EG E := hgE _ F.cE
      have hcen : ∀ x ∈ EG E, (g * cG e₀ * g⁻¹) * x = x * (g * cG e₀ * g⁻¹) := by
        intro x hx
        have hx' : g⁻¹ * x * g ∈ EG E := hinv x hx
        have h := F.cSZ _ (F.ES hx')
        calc (g * cG e₀ * g⁻¹) * x = g * (cG e₀ * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * cG e₀) * g⁻¹ := by rw [h]
          _ = x * (g * cG e₀ * g⁻¹) := by group
      rcases F.ZE _ hc'E hcen with h | h
      · exfalso
        apply cG_ne_one e₀
        have : cG e₀ = g⁻¹ * (g * cG e₀ * g⁻¹) * g := by group
        rw [this, h]; group
      · exact h
    have hgc' : g * cG e₀ = cG e₀ * g := by
      rw [mul_inv_eq_iff_eq_mul] at hgc
      exact hgc
    exact HcG_le_Nn e₀ (Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hge,
      mem_centralizer_singleton_iff.2 hgc'⟩)
  have hCe : Nat.card (Nn e₀ ⊓ centralizer ({e} : Set G) : Subgroup G) = 384 := by
    rw [Nn_inf_centralizer e₀]
    exact card_HcG e₀
  exact no_extra_fusion (Nn e₀) (EG E) (P : Subgroup G) e y₁ F.EN hPE hPcard hG12
    (e_mem_EG D E he2 hue) (card_Nn e₀ he2 hd) hCe hCy hCL hX

end Fusion

end CFSG.EvenSporadicStandard.M12Std.Yosh
