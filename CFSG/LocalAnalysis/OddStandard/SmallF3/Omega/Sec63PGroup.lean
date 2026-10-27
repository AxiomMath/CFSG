module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase
public import CFSG.GH74.GLS.Balance.CompSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem sec63P_diag_D1_aux {J K Δ : Subgroup G} {g : G} (hJ : Group.IsPerfect ↥J)
    (hcomm : ∀ a ∈ J, ∀ c ∈ K, a * c = c * a)
    (hgJ : g ∈ normalizer (J : Set G)) (hgK : g ∈ normalizer (K : Set G))
    (hgΔ : Δ ≤ centralizer ({g} : Set G))
    (hp : ∀ a ∈ J, ∃ c ∈ K, a * c ∈ Δ) :
    J ≤ centralizer ({g} : Set G) := by
  have hc : ∀ k ∈ J, ∀ y ∈ J, y * ⁅k, g⁆ = ⁅k, g⁆ * y := by
    intro k hk y hy
    obtain ⟨c, hcK, hkcΔ⟩ := hp k hk
    have hkg : (k * c) * g = g * (k * c) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hgΔ hkcΔ)
    have hk'J : g * k * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hgJ k).mp hk
    have hc'K : g * c * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK c).mp hcK
    have hkc' : (g * k * g⁻¹) * (g * c * g⁻¹) = k * c := by
      have hconj : g * (k * c) * g⁻¹ = k * c := by rw [← hkg]; group
      rw [← hconj]; group
    have hc'' : g * c * g⁻¹ * c⁻¹ ∈ K := K.mul_mem hc'K (K.inv_mem hcK)
    have hcomm' : (g * k * g⁻¹) * (g * c * g⁻¹ * c⁻¹) =
        (g * c * g⁻¹ * c⁻¹) * (g * k * g⁻¹) := hcomm _ hk'J _ hc''
    have hk_eq : k = (g * k * g⁻¹) * (g * c * g⁻¹ * c⁻¹) := by
      calc k = k * c * c⁻¹ := by group
        _ = (g * k * g⁻¹) * (g * c * g⁻¹) * c⁻¹ := by rw [hkc']
        _ = (g * k * g⁻¹) * (g * c * g⁻¹ * c⁻¹) := by group
    have hcommut : ⁅k, g⁆ = g * c * g⁻¹ * c⁻¹ := by
      have h1 : ⁅k, g⁆ = k * (g * k * g⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h1]
      nth_rewrite 1 [hk_eq]
      rw [hcomm']
      group
    rw [hcommut]
    exact hcomm y hy _ hc''
  have hcent := CFSG.GH74.GLS.Balance.Comp.commute_of_commutator_central hJ hgJ hc
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent y hy).symm

theorem sec63_diag_D1 {J₁ J₂ Δ : Subgroup G} {g : G} (hJ₁ : Group.IsPerfect ↥J₁)
    (hJ₂ : Group.IsPerfect ↥J₂) (hcomm : ∀ a ∈ J₁, ∀ c ∈ J₂, a * c = c * a)
    (hg₁ : g ∈ normalizer (J₁ : Set G)) (hg₂ : g ∈ normalizer (J₂ : Set G))
    (hgΔ : Δ ≤ centralizer ({g} : Set G))
    (hp₁ : ∀ a ∈ J₁, ∃ c ∈ J₂, a * c ∈ Δ) (hp₂ : ∀ c ∈ J₂, ∃ a ∈ J₁, a * c ∈ Δ) :
    J₁ ≤ centralizer ({g} : Set G) ∧ J₂ ≤ centralizer ({g} : Set G) := by
  refine ⟨sec63P_diag_D1_aux hJ₁ hcomm hg₁ hg₂ hgΔ hp₁, ?_⟩
  exact sec63P_diag_D1_aux hJ₂ (fun a ha c hc => (hcomm c hc a ha).symm) hg₂ hg₁ hgΔ
    (fun c hc => by
      obtain ⟨a, ha, hac⟩ := hp₂ c hc
      exact ⟨a, ha, hcomm a ha c hc ▸ hac⟩)

theorem sec63_diag_D2 {J₁ J₂ Δ : Subgroup G} {g : G} (hΔq : IsQuasisimple ↥Δ)
    (hcomm : ∀ a ∈ J₁, ∀ c ∈ J₂, a * c = c * a) (hΔ : Δ ≤ J₁ ⊔ J₂) (hΔ₂ : ¬ Δ ≤ J₂)
    (hg₁ : J₁ ≤ centralizer ({g} : Set G)) (hg₂ : g ∈ normalizer (J₂ : Set G))
    (hgΔ : g ∈ normalizer (Δ : Set G)) : Δ ≤ centralizer ({g} : Set G) := by
  have hconj_mem : ∀ d ∈ Δ, ∀ x ∈ J₂, d * x * d⁻¹ ∈ J₂ := by
    intro d hd x hx
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := sec63P_mem_sup_of_comm hcomm (hΔ hd)
    have hmem : d₂ * x * d₂⁻¹ ∈ J₂ :=
      J₂.mul_mem (J₂.mul_mem hd₂ hx) (J₂.inv_mem hd₂)
    have hc := hcomm d₁ hd₁ (d₂ * x * d₂⁻¹) hmem
    have heq : d₁ * d₂ * x * (d₁ * d₂)⁻¹ = d₂ * x * d₂⁻¹ := by
      calc d₁ * d₂ * x * (d₁ * d₂)⁻¹ = d₁ * (d₂ * x * d₂⁻¹) * d₁⁻¹ := by group
        _ = (d₂ * x * d₂⁻¹) * d₁ * d₁⁻¹ := by rw [hc]
        _ = d₂ * x * d₂⁻¹ := by group
    rw [heq]
    exact hmem
  have hmem : ∀ a ∈ Δ, ⁅a, g⁆ ∈ J₂ ∧ ⁅a, g⁆ ∈ Δ := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := sec63P_mem_sup_of_comm hcomm (hΔ ha)
    have ha₁g : a₁ * g = g * a₁ := Subgroup.mem_centralizer_singleton_iff.mp (hg₁ ha₁)
    have ha₂' : g * a₂ * g⁻¹ ∈ J₂ := (Subgroup.mem_normalizer_iff.mp hg₂ a₂).mp ha₂
    have hconj : g * (a₁ * a₂) * g⁻¹ = a₁ * (g * a₂ * g⁻¹) := by
      calc g * (a₁ * a₂) * g⁻¹ = (g * a₁ * g⁻¹) * (g * a₂ * g⁻¹) := by group
        _ = a₁ * (g * a₂ * g⁻¹) := by
          have h : g * a₁ * g⁻¹ = a₁ := by rw [← ha₁g]; group
          rw [h]
    have hcommut : ⁅a₁ * a₂, g⁆ = a₂ * (g * a₂ * g⁻¹)⁻¹ := by
      have h1 : ⁅a₁ * a₂, g⁆ = (a₁ * a₂) * (g * (a₁ * a₂) * g⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h1, hconj]
      have hc := hcomm a₁ ha₁ (a₂ * (g * a₂ * g⁻¹)⁻¹)
        (J₂.mul_mem ha₂ (J₂.inv_mem ha₂'))
      calc (a₁ * a₂) * (a₁ * (g * a₂ * g⁻¹))⁻¹
          = a₁ * (a₂ * (g * a₂ * g⁻¹)⁻¹) * a₁⁻¹ := by group
        _ = (a₂ * (g * a₂ * g⁻¹)⁻¹) * a₁ * a₁⁻¹ := by rw [hc]
        _ = a₂ * (g * a₂ * g⁻¹)⁻¹ := by group
    refine ⟨?_, CFSG.GH74.GLS.Balance.Comp.commutator_mem hgΔ ha⟩
    rw [hcommut]
    exact J₂.mul_mem ha₂ (J₂.inv_mem ha₂')
  have hN : (J₂.subgroupOf Δ).Normal := by
    rw [← Subgroup.inf_subgroupOf_right J₂ Δ]
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).mpr ?_
    intro h k hh hk
    exact ⟨hconj_mem k hk h hh.1, Δ.mul_mem (Δ.mul_mem hk hh.2) (Δ.inv_mem hk)⟩
  have hNle : J₂.subgroupOf Δ ≤ Subgroup.center ↥Δ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hΔq hN with h | h
    · exfalso
      apply hΔ₂
      intro d hd
      have hmemN : (⟨d, hd⟩ : ↥Δ) ∈ J₂.subgroupOf Δ := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp hmemN
    · exact h
  have hc : ∀ k ∈ Δ, ∀ y ∈ Δ, y * ⁅k, g⁆ = ⁅k, g⁆ * y := by
    intro k hk y hy
    have hk' := hmem k hk
    have hcent : (⟨⁅k, g⁆, hk'.2⟩ : ↥Δ) ∈ Subgroup.center ↥Δ :=
      hNle (Subgroup.mem_subgroupOf.mpr hk'.1)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent (⟨y, hy⟩ : ↥Δ))
  have hcent := CFSG.GH74.GLS.Balance.Comp.commute_of_commutator_central hΔq.1 hgΔ hc
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent y hy).symm

theorem sec63P_commutator_dichotomy {J : Subgroup G} {v : G} (hJ : IsQuasisimple ↥J)
    (hv : v ∈ normalizer (J : Set G)) :
    ⁅J, zpowers v⁆ = J ∨ J ≤ centralizer ({v} : Set G) := by
  have hMJ : ⁅J, zpowers v⁆ ≤ J :=
    Subgroup.commutator_le.mpr fun a ha w hw =>
      CFSG.GH74.GLS.Balance.Comp.commutator_mem (Subgroup.zpowers_le.mpr hv hw) ha
  have hxM : ∀ x ∈ J, ∀ m ∈ ⁅J, zpowers v⁆, x * m * x⁻¹ ∈ ⁅J, zpowers v⁆ := by
    intro x hx m hm
    have hH3 : ⁅J, zpowers v⁆ ≤ (⁅J, zpowers v⁆).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha w hw
      change MulAut.conj x ⁅a, w⁆ ∈ ⁅J, zpowers v⁆
      rw [MulAut.conj_apply]
      have h1 : ⁅x * a, w⁆ ∈ ⁅J, zpowers v⁆ :=
        Subgroup.commutator_mem_commutator (J.mul_mem hx ha) hw
      have h2 : ⁅x, w⁆ ∈ ⁅J, zpowers v⁆ := Subgroup.commutator_mem_commutator hx hw
      have h3 : x * ⁅a, w⁆ * x⁻¹ = ⁅x * a, w⁆ * ⁅x, w⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h3]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    exact hH3 hm
  have hN : ((⁅J, zpowers v⁆).subgroupOf J).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hxM x x.2 n hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hN with h | h
  · left
    refine le_antisymm hMJ ?_
    intro x hx
    have hxM' : (⟨x, hx⟩ : ↥J) ∈ (⁅J, zpowers v⁆).subgroupOf J := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp hxM'
  · right
    have hc : ∀ k ∈ J, ∀ y ∈ J, y * ⁅k, v⁆ = ⁅k, v⁆ * y := by
      intro k hk y hy
      have hkv : ⁅k, v⁆ ∈ ⁅J, zpowers v⁆ :=
        Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers v)
      have hkJ : ⁅k, v⁆ ∈ J := hMJ hkv
      have hcent : (⟨⁅k, v⁆, hkJ⟩ : ↥J) ∈ Subgroup.center ↥J :=
        h (Subgroup.mem_subgroupOf.mpr hkv)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent (⟨y, hy⟩ : ↥J))
    have hcent := CFSG.GH74.GLS.Balance.Comp.commute_of_commutator_central hJ.1 hv hc
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent y hy).symm

end CFSG.OddStandard.SmallF3.Omega
