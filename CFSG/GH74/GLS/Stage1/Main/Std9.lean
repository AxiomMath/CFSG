module

public import CFSG.GH74.GLS.Stage1.Thm4.Conj
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.GH74.GLS.Stage1.Thm4.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z : G}

theorem exists_extremal_conj' {S : Subgroup G} (hS : M.Syl2In S (centralizer ({z} : Set G))) {a : G}
    (haS : a ∈ S) :
    ∃ c ∈ centralizer ({z} : Set G), c * a * c⁻¹ ∈ S ∧
      M.Syl2In (S ⊓ centralizer ({c * a * c⁻¹} : Set G))
        (centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G)) := by
  have hSC : S ≤ centralizer ({z} : Set G) := hS.1
  have hT02 : IsPGroup 2 ↥(S ⊓ centralizer ({a} : Set G)) := hS.2.1.to_inf_left
  have hXle : S ⊓ centralizer ({a} : Set G) ≤ centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) :=
    le_inf (inf_le_left.trans hSC) inf_le_right
  obtain ⟨Ta, hTa, hT0Ta⟩ := M.exists_syl2In_ge hT02 hXle
  have haT0 : a ∈ S ⊓ centralizer ({a} : Set G) :=
    ⟨haS, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hTaC : Ta ≤ centralizer ({z} : Set G) := hTa.1.trans inf_le_left
  obtain ⟨P', hP', hTaP'⟩ := M.exists_syl2In_ge hTa.2.1 hTaC
  obtain ⟨c, hcC, hcP⟩ := hS.exists_conj hP'
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hcC
    rw [this]; group
  have haP' : a ∈ P' := hTaP' (hT0Ta haT0)
  rw [hcP, M.mem_cj] at haP'
  refine ⟨c, hcC, haP', ?_⟩
  have hY := M.syl2In_cj hTa c⁻¹
  have hXeq : M.cj (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G)) c⁻¹ =
      centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G) := by
    rw [M.cj_inf, M.cj_centralizer, M.cj_centralizer, inv_inv, hcz]
  rw [hXeq] at hY
  have hYS : M.cj Ta c⁻¹ ≤ S := by
    intro x hx
    have h1 : c⁻¹ * x * c ∈ Ta := by
      have := M.mem_cj.1 hx
      simpa using this
    have h2 : c⁻¹ * x * c ∈ P' := hTaP' h1
    rw [hcP, M.mem_cj] at h2
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at h2
  have hYle : M.cj Ta c⁻¹ ≤ S ⊓ centralizer ({c * a * c⁻¹} : Set G) :=
    le_inf hYS (hY.1.trans inf_le_right)
  have hQ2 : IsPGroup 2 ↥(S ⊓ centralizer ({c * a * c⁻¹} : Set G)) := hS.2.1.to_inf_left
  have hQle : S ⊓ centralizer ({c * a * c⁻¹} : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G) :=
    inf_le_inf_right _ hSC
  have := hY.eq_of_le hQ2 hYle hQle
  rw [this]
  exact hY

theorem exists_extremal_conj_of_involution {S : Subgroup G} (hS : M.Syl2In S (centralizer ({z} : Set G)))
    {a : G} (haC : a ∈ centralizer ({z} : Set G)) (ha2 : orderOf a = 2) :
    ∃ c ∈ centralizer ({z} : Set G), c * a * c⁻¹ ∈ S ∧
      M.Syl2In (S ⊓ centralizer ({c * a * c⁻¹} : Set G))
        (centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G)) := by
  have hA : IsPGroup 2 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2]; norm_num)
  have hAle : zpowers a ≤ centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_le]; exact haC
  obtain ⟨P, hP, haP⟩ := M.exists_syl2In_ge hA hAle
  obtain ⟨c₀, hc₀, hcP⟩ := hS.exists_conj hP
  have haS : c₀ * a * c₀⁻¹ ∈ S := by
    have := haP (Subgroup.mem_zpowers a)
    rw [hcP, M.mem_cj] at this
    exact this
  obtain ⟨c₁, hc₁, hc₁S, hext⟩ := exists_extremal_conj' hS haS
  refine ⟨c₁ * c₀, mul_mem hc₁ hc₀, ?_, ?_⟩
  · have e : c₁ * c₀ * a * (c₁ * c₀)⁻¹ = c₁ * (c₀ * a * c₀⁻¹) * c₁⁻¹ := by group
    rw [e]; exact hc₁S
  · have e : c₁ * c₀ * a * (c₁ * c₀)⁻¹ = c₁ * (c₀ * a * c₀⁻¹) * c₁⁻¹ := by group
    rw [e]; exact hext

theorem exists_std9 (h92 : Prop9_2) (hH : Hyp9 G Lh) :
    ∃ (z t : G) (S K : Subgroup G), Std9 G Lh z t S K := by
  obtain ⟨z, t, K, hg⟩ := h92 G Lh hH
  obtain ⟨t₀, K₀, hg₀, hpref⟩ : ∃ (t₀ : G) (K₀ : Subgroup G), Good92 G Lh z t₀ K₀ ∧ PrefT G Lh z t₀ := by
    by_cases hA : ∃ (t' : G) (K' : Subgroup G), Good92 G Lh z t' K' ∧ NormsAll Lh z t'
    · obtain ⟨t', K', hg', hn'⟩ := hA
      exact ⟨t', K', hg', fun _ => hn'⟩
    · exact ⟨t, K, hg, fun h => absurd h hA⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 2) (centralizer ({z} : Set G))
  have hS' : M.Syl2In S (centralizer ({z} : Set G)) := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  obtain ⟨c, hcC, hcS, hext⟩ :=
    exists_extremal_conj_of_involution hS' hg₀.t_cen hg₀.t_ord
  refine ⟨z, c * t₀ * c⁻¹, S, cmap c K₀, ?_⟩
  exact
    { toHyp9 := hH
      toGood92 := hg₀.conj hcC
      pref := by
        intro hex
        exact NormsAll.conj hcC (hpref hex)
      sylow := hS
      t_mem := hcS
      t_ext := (CFSG.ABGLocalTools.isSylowOf_iff).2 hext }

end CFSG.GH74.GLS.Stage1.Main
