module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Cover

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise commutatorElement

variable {H : Type} [Group H]

theorem commutator_mul_commute {G : Type*} [Group G] {g₁ g₂ z₁ z₂ : G}
    (h2 : Commute z₁ g₂) (h3 : Commute z₂ g₁) (h5 : Commute z₁ z₂) :
    (g₁ * z₁) * (g₂ * z₂) * (g₁ * z₁)⁻¹ * (g₂ * z₂)⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  calc (g₁ * z₁) * (g₂ * z₂) * (g₁ * z₁)⁻¹ * (g₂ * z₂)⁻¹
      = g₁ * (z₁ * g₂) * z₂ * z₁⁻¹ * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * (g₂ * z₁) * z₂ * z₁⁻¹ * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by rw [h2.eq]
    _ = g₁ * g₂ * (z₁ * z₂ * z₁⁻¹) * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * z₂ * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by rw [h5.eq]; group
    _ = g₁ * g₂ * (z₂ * g₁⁻¹ * z₂⁻¹) * g₂⁻¹ := by group
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by rw [h3.inv_right.eq]; group

variable {A P : Subgroup H} {s : H}

theorem exists_diag_cover_of_link5a [Finite H] (hAq : CFSG.IsQuasisimple ↥A)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj s).toMonoidHom, a * b = b * a)
    (hs2 : s ^ 2 ∈ centralizer (A : Set H))
    (hP : P ≤ A ⊔ A.map (MulAut.conj s).toMonoidHom) (hsP : s ∈ centralizer (P : Set H))
    (hiso : Nonempty ((↥A ⧸ center ↥A) ≃* (↥P ⧸ center ↥P))) :
    ∃ π : ↥A →* ↥P, Function.Surjective π ∧ π.ker ≤ center ↥A ∧
      ∀ a : ↥A, ((π a : ↥P) : H) = (a : H) * (s * (a : H) * s⁻¹) := by
  set A' : Subgroup H := A.map (MulAut.conj s).toMonoidHom with hA'
  have hA'mem : ∀ y : H, y ∈ A' ↔ ∃ a ∈ A, s * a * s⁻¹ = y := fun y => by
    simp [hA', Subgroup.mem_map, MulAut.conj_apply]
  have hτA : ∀ a : H, a ∈ A → s * a * s⁻¹ ∈ A' := fun a ha => (hA'mem _).2 ⟨a, ha, rfl⟩
  have hτ2 : ∀ a ∈ A, s * (s * a * s⁻¹) * s⁻¹ = a := fun a ha => by
    have h := mem_centralizer_iff.1 hs2 a ha
    rw [pow_two] at h
    calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s * s)⁻¹ := by group
      _ = a * (s * s) * (s * s)⁻¹ := by rw [h]
      _ = a := by group
  let δ : ↥A →* H := MonoidHom.mk' (fun a => (a : H) * (s * (a : H) * s⁻¹)) (by
    intro a b
    have h := hcomm (b : H) b.2 (s * (a : H) * s⁻¹) (hτA _ a.2)
    calc ((a * b : ↥A) : H) * (s * ((a * b : ↥A) : H) * s⁻¹)
        = (a : H) * (b * (s * (a : H) * s⁻¹)) * (s * (b : H) * s⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
      _ = (a : H) * ((s * (a : H) * s⁻¹) * b) * (s * (b : H) * s⁻¹) := by rw [h]
      _ = ((a : H) * (s * (a : H) * s⁻¹)) * ((b : H) * (s * (b : H) * s⁻¹)) := by group)
  have hδ : ∀ a : ↥A, δ a = (a : H) * (s * (a : H) * s⁻¹) := fun a => rfl
  have hzA : ∀ z ∈ A ⊓ A', ∀ a ∈ A, z * a = a * z := fun z hz a ha =>
    (hcomm a ha z hz.2).symm
  have hzA' : ∀ z ∈ A ⊓ A', ∀ b ∈ A', z * b = b * z := fun z hz b hb => hcomm z hz.1 b hb
  have hzδ : ∀ z ∈ A ⊓ A', ∀ a : ↥A, z * δ a = δ a * z := fun z hz a => by
    have h1 := hzA z hz a a.2
    have h2 := hzA' z hz _ (hτA _ a.2)
    rw [hδ]
    calc z * ((a : H) * (s * (a : H) * s⁻¹)) = (z * (a : H)) * (s * (a : H) * s⁻¹) := by group
      _ = ((a : H) * z) * (s * (a : H) * s⁻¹) := by rw [h1]
      _ = (a : H) * (z * (s * (a : H) * s⁻¹)) := by group
      _ = (a : H) * ((s * (a : H) * s⁻¹) * z) := by rw [h2]
      _ = ((a : H) * (s * (a : H) * s⁻¹)) * z := by group
  have hzz : ∀ z ∈ A ⊓ A', ∀ z' ∈ A ⊓ A', z * z' = z' * z := fun z hz z' hz' =>
    hzA z hz z' hz'.1
  have hdecomp : ∀ x ∈ P, ∃ a : ↥A, ∃ z ∈ A ⊓ A', x = δ a * z := by
    intro x hx
    have hxs : s * x * s⁻¹ = x := by
      have := mem_centralizer_iff.1 hsP x hx
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [this]
        _ = x := by group
    have hAA' : x ∈ ((A : Set H) * (A' : Set H)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A A'
        (le_trans (fun a ha => mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
          (Subgroup.centralizer_le_normalizer (A' : Set H)))]
      exact hP hx
    obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := hAA'
    obtain ⟨c, hc, rfl⟩ := (hA'mem b₀).1 hb₀
    have hd₀A' : s * a₀ * s⁻¹ ∈ A' := hτA a₀ ha₀
    have hcd : c * (s * a₀ * s⁻¹) = (s * a₀ * s⁻¹) * c := hcomm c hc _ hd₀A'
    have hsx : (s * a₀ * s⁻¹) * c = a₀ * (s * c * s⁻¹) := by
      calc (s * a₀ * s⁻¹) * c = (s * a₀ * s⁻¹) * (s * (s * c * s⁻¹) * s⁻¹) := by rw [hτ2 c hc]
        _ = s * (a₀ * (s * c * s⁻¹)) * s⁻¹ := by group
        _ = a₀ * (s * c * s⁻¹) := hxs
    have hz0 : a₀⁻¹ * c = (s * c * s⁻¹) * (s * a₀ * s⁻¹)⁻¹ := by
      have h1 : a₀⁻¹ * (c * (s * a₀ * s⁻¹)) = (s * c * s⁻¹) := by
        rw [hcd, hsx]
        group
      calc a₀⁻¹ * c = a₀⁻¹ * (c * (s * a₀ * s⁻¹)) * (s * a₀ * s⁻¹)⁻¹ := by group
        _ = (s * c * s⁻¹) * (s * a₀ * s⁻¹)⁻¹ := by rw [h1]
    have hmem : a₀⁻¹ * c ∈ A ⊓ A' := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha₀) hc, ?_⟩
      rw [hz0]
      exact Subgroup.mul_mem _ (hτA c hc) (Subgroup.inv_mem _ hd₀A')
    refine ⟨⟨a₀, ha₀⟩, a₀⁻¹ * c, hmem, ?_⟩
    have hcomm_a : a₀ * (s * a₀ * s⁻¹) = (s * a₀ * s⁻¹) * a₀ := hcomm a₀ ha₀ _ hd₀A'
    show a₀ * (s * c * s⁻¹) = (a₀ * (s * a₀ * s⁻¹)) * (a₀⁻¹ * c)
    calc a₀ * (s * c * s⁻¹) = (s * a₀ * s⁻¹) * c := hsx.symm
      _ = ((s * a₀ * s⁻¹) * a₀) * (a₀⁻¹ * c) := by group
      _ = (a₀ * (s * a₀ * s⁻¹)) * (a₀⁻¹ * c) := by rw [hcomm_a]
  have hPD : P ≤ δ.range := by
    have hcomm' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ δ.range := by
      intro x hx y hy
      obtain ⟨a₁, z₁, hz₁, rfl⟩ := hdecomp x hx
      obtain ⟨a₂, z₂, hz₂, rfl⟩ := hdecomp y hy
      rw [commutator_mul_commute (Commute.symm (hzδ z₁ hz₁ a₂).symm)
        (Commute.symm (hzδ z₂ hz₂ a₁).symm) (hzz z₁ hz₁ z₂ hz₂)]
      refine ⟨⁅a₁, a₂⁆, ?_⟩
      rw [map_commutatorElement, commutatorElement_def]
    have hperf : Group.IsPerfect ↥P := hPq.1
    have hle : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ ≤ δ.range.subgroupOf P := by
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      show ((g₁ * g₂ * g₁⁻¹ * g₂⁻¹ : ↥P) : H) ∈ δ.range
      simpa using hcomm' (g₁ : H) g₁.2 (g₂ : H) g₂.2
    have htop : (⊤ : Subgroup ↥P) ≤ δ.range.subgroupOf P := by
      have := hperf.commutator_eq_top
      rw [_root_.commutator_def] at this
      rwa [this] at hle
    intro x hx
    exact htop (Subgroup.mem_top (⟨x, hx⟩ : ↥P))
  have hker : ∀ a : ↥A, δ a = 1 → a ∈ center ↥A := by
    intro a ha
    have h1 : s * (a : H) * s⁻¹ = (a : H)⁻¹ := by
      have : (a : H) * (s * (a : H) * s⁻¹) = 1 := ha
      exact eq_inv_of_mul_eq_one_right this
    have hmem : (a : H) ∈ A ⊓ A' := by
      refine ⟨a.2, ?_⟩
      have : (a : H)⁻¹ ∈ A' := h1 ▸ hτA _ a.2
      simpa using Subgroup.inv_mem _ this
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hzA _ hmem (g : H) g.2).symm
  have : Group.IsPerfect ↥A := hAq.1
  let π₀ : ↥A →* ↥δ.range := δ.rangeRestrict
  have hπ₀s : Function.Surjective π₀ := δ.rangeRestrict_surjective
  have hπ₀k : π₀.ker ≤ center ↥A := fun a ha => hker a (by
    have : (π₀ a : ↥δ.range) = 1 := ha
    exact congrArg Subtype.val this)
  have hDq : CFSG.IsQuasisimple ↥δ.range := isQuasisimple_of_cover hAq π₀ hπ₀s hπ₀k
  obtain ⟨e₁⟩ := cqEquiv_of_cover π₀ hπ₀s hπ₀k
  obtain ⟨e₂⟩ := hiso
  have hPDeq : P = δ.range :=
    eq_of_le_of_iso hPD hPq hDq ⟨e₂.symm.trans e₁⟩
  refine ⟨δ.codRestrict P (fun a => hPDeq ▸ ⟨a, rfl⟩), ?_, ?_, fun a => rfl⟩
  · intro y
    have : (y : H) ∈ δ.range := hPDeq ▸ y.2
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  · intro a ha
    exact hker a (by
      have : (δ.codRestrict P (fun a => hPDeq ▸ ⟨a, rfl⟩) a : ↥P) = 1 := ha
      exact congrArg Subtype.val this)

end CFSG.EvenSporadicStandard.Induction.Hyp
