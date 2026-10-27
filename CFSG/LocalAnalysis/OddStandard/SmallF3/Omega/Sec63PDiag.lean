module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase
public import CFSG.GH74.GLS.Balance.CompSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem sec63P_commutator_mul_central {g h z z' : G} (hzg : z * g = g * z)
    (hzh : z * h = h * z) (hz'g : z' * g = g * z') (hz'h : z' * h = h * z')
    (hzz' : z * z' = z' * z) :
    ⁅g * z, h * z'⁆ = ⁅g, h⁆ := by
  have hz'g' : z' * g⁻¹ = g⁻¹ * z' := by
    calc z' * g⁻¹ = g⁻¹ * (g * z') * g⁻¹ := by group
      _ = g⁻¹ * (z' * g) * g⁻¹ := by rw [← hz'g]
      _ = g⁻¹ * z' := by group
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc g * z * (h * z') * (z⁻¹ * g⁻¹) * (z'⁻¹ * h⁻¹)
      = g * (z * h) * z' * z⁻¹ * g⁻¹ * z'⁻¹ * h⁻¹ := by group
    _ = g * (h * z) * z' * z⁻¹ * g⁻¹ * z'⁻¹ * h⁻¹ := by rw [hzh]
    _ = g * h * (z * z') * z⁻¹ * g⁻¹ * z'⁻¹ * h⁻¹ := by group
    _ = g * h * (z' * z) * z⁻¹ * g⁻¹ * z'⁻¹ * h⁻¹ := by rw [hzz']
    _ = g * h * z' * g⁻¹ * z'⁻¹ * h⁻¹ := by group
    _ = g * h * (z' * g⁻¹) * z'⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * z') * z'⁻¹ * h⁻¹ := by rw [hz'g']
    _ = g * h * g⁻¹ * h⁻¹ := by group

private theorem sec63P_exists_diag_decomp {u : G} (hu : orderOf u = 2) {J : Subgroup G}
    (hcomm : ∀ a ∈ J, ∀ d ∈ CFSG.conjugate J u, a * d = d * a) (φ : J →* G)
    (hφ : ∀ k : J, φ k = (k : G) * (u * k * u⁻¹))
    {c : G} (hcJ : c ∈ J ⊔ CFSG.conjugate J u) (hcC : c ∈ centralizer ({u} : Set G)) :
    ∃ a : J, ∃ z ∈ J ⊓ CFSG.conjugate J u,
      c = φ a * z ∧ (∀ a' : J, z * φ a' = φ a' * z) ∧
      (∀ z' ∈ J ⊓ CFSG.conjugate J u, z * z' = z' * z) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, hc_eq⟩ := sec63P_mem_sup_of_comm hcomm hcJ
  have hb : u * a₂ * u⁻¹ ∈ J := sec63P_mem_conjugate_iff.mp ha₂
  let b : G := u * a₂ * u⁻¹
  have hb' : b ∈ J := hb
  have hub : u * b * u⁻¹ = a₂ := by
    dsimp [b]
    calc u * (u * a₂ * u⁻¹) * u⁻¹ = (u * u) * a₂ * (u * u)⁻¹ := by group
      _ = a₂ := by rw [sec63P_mul_self hu]; group
  let p : G := u * a₁ * u⁻¹
  have hp : p ∈ CFSG.conjugate J u := sec63P_conj_mem_conjugate hu ha₁
  have huc : u * c * u⁻¹ = c := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hcC]
    group
  have hpb : p * b = a₁ * a₂ := by
    rw [hc_eq] at huc
    calc p * b = u * (a₁ * a₂) * u⁻¹ := by dsimp [p, b]; group
      _ = a₁ * a₂ := huc
  have hp_a₁ : p * a₁⁻¹ = a₁⁻¹ * p := by
    have h := hcomm a₁ ha₁ p hp
    calc p * a₁⁻¹ = a₁⁻¹ * (a₁ * p) * a₁⁻¹ := by group
      _ = a₁⁻¹ * (p * a₁) * a₁⁻¹ := by rw [← h]
      _ = a₁⁻¹ * p := by group
  let z : G := a₁⁻¹ * b
  have hzJ : z ∈ J := J.mul_mem (J.inv_mem ha₁) hb'
  have hzJ' : z ∈ CFSG.conjugate J u := by
    have hzp : z * p = a₂ := by
      dsimp [z]
      rw [mul_assoc, hcomm b hb' p hp, hpb]
      group
    have hz_eq : z = a₂ * p⁻¹ := by rw [← hzp]; group
    rw [hz_eq]
    exact (CFSG.conjugate J u).mul_mem ha₂ ((CFSG.conjugate J u).inv_mem hp)
  refine ⟨⟨a₁, ha₁⟩, z, ⟨hzJ, hzJ'⟩, ?_, ?_, ?_⟩
  · have h1 : φ ⟨a₁, ha₁⟩ * z = p * b := by
      rw [hφ]
      dsimp [z]
      calc (a₁ * p) * (a₁⁻¹ * b) = a₁ * (p * a₁⁻¹) * b := by group
        _ = a₁ * (a₁⁻¹ * p) * b := by rw [hp_a₁]
        _ = p * b := by group
    rw [h1, hpb]
    exact hc_eq
  · intro a'
    have ha' : (a' : G) ∈ J := a'.2
    have hconj : u * (a' : G) * u⁻¹ ∈ CFSG.conjugate J u :=
      sec63P_conj_mem_conjugate hu ha'
    have h1 : z * (a' : G) = (a' : G) * z := (hcomm a' ha' z hzJ').symm
    have h2 : z * (u * (a' : G) * u⁻¹) = (u * (a' : G) * u⁻¹) * z :=
      hcomm z hzJ (u * (a' : G) * u⁻¹) hconj
    rw [hφ]
    calc z * ((a' : G) * (u * (a' : G) * u⁻¹))
        = (z * (a' : G)) * (u * (a' : G) * u⁻¹) := by group
      _ = ((a' : G) * z) * (u * (a' : G) * u⁻¹) := by rw [h1]
      _ = (a' : G) * (z * (u * (a' : G) * u⁻¹)) := by group
      _ = (a' : G) * ((u * (a' : G) * u⁻¹) * z) := by rw [h2]
      _ = (a' : G) * (u * (a' : G) * u⁻¹) * z := by group
  · intro z' hz'
    exact hcomm z hzJ z' hz'.2

theorem sec63_diag_full [Finite G] {u : G} {J W : Subgroup G} (hu : orderOf u = 2)
    (hJ : IsQuasisimple ↥J) (hcomm : ∀ a ∈ J, ∀ c ∈ CFSG.conjugate J u, a * c = c * a)
    (hWJ : W ≤ J ⊔ CFSG.conjugate J u) (hW : IsComponentIn W (centralizer ({u} : Set G))) :
    ∀ a ∈ J, a * (u * a * u⁻¹) ∈ W := by
  have hc : ∀ a ∈ J, ∀ b ∈ J, a * (u * b * u⁻¹) = (u * b * u⁻¹) * a :=
    fun a ha b hb => hcomm a ha (u * b * u⁻¹) (sec63P_conj_mem_conjugate hu hb)
  obtain ⟨φ, hφ⟩ := CFSG.GH74.GLS.Balance.Comp.exists_diagHom hc
  have hker : φ.ker ≤ center J := CFSG.GH74.GLS.Balance.Comp.diagHom_ker_le_center hc hφ
  have hcen : ∀ k : J, φ k ∈ centralizer ({u} : Set G) :=
    CFSG.GH74.GLS.Balance.Comp.diagHom_mem_centralizer (sec63P_mul_self hu) hc hφ
  have hDq : IsQuasisimple φ.range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hJ φ.rangeRestrict
      φ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  have hDC : φ.range ≤ centralizer ({u} : Set G) := fun x hx => by
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hcen k
  have hWD : W ≤ φ.range := by
    have hcommW : ⁅W, W⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro c hcW c' hc'W
      obtain ⟨a, z, hz, hcz, hzφ, hzz⟩ :=
        sec63P_exists_diag_decomp hu hcomm φ hφ (hWJ hcW) (hW.1 hcW)
      obtain ⟨a', z', hz', hcz', hz'φ, hzz'⟩ :=
        sec63P_exists_diag_decomp hu hcomm φ hφ (hWJ hc'W) (hW.1 hc'W)
      rw [hcz, hcz']
      rw [sec63P_commutator_mul_central (hzφ a) (hzφ a') (hz'φ a) (hz'φ a') (hzz z' hz')]
      exact ⟨⁅a, a'⁆, by simp only [commutatorElement_def, map_mul, map_inv]⟩
    have hperf : ⁅W, W⁆ = W := Subgroup.isPerfect_iff.mp hW.isQuasisimple.1
    rw [← hperf]
    exact hcommW
  have hDW : φ.range ≤ W := by
    have hW' : IsComponentIn W φ.range := hW.mono hWD hDC
    have hK : IsComponent (W.subgroupOf φ.range) := hW'.2
    have hL : IsComponent (⊤ : Subgroup φ.range) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hDq,
        Subgroup.IsSubnormal.top⟩
    rcases CFSG.LocalCores.distinct_components_commute hK hL with heq | hbot
    · intro d hd
      have hmem : (⟨d, hd⟩ : φ.range) ∈ W.subgroupOf φ.range := by
        rw [heq]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    · exfalso
      apply hW.not_le_centralizer
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hmem : (⟨w, hWD hw⟩ : φ.range) ∈ W.subgroupOf φ.range := hw
      have hmem' : (⟨w', hWD hw'⟩ : φ.range) ∈ (⊤ : Subgroup φ.range) := Subgroup.mem_top _
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hle hmem) _ hmem')
  intro a ha
  have hmem : φ ⟨a, ha⟩ ∈ W := hDW ⟨⟨a, ha⟩, rfl⟩
  simpa [hφ] using hmem

end CFSG.OddStandard.SmallF3.Omega
