module

public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

section Normal

variable {L : Type*} [Group L]

instance shortU_normal : (shortU L).Normal := by
  unfold shortU
  infer_instance

theorem shortC_le_shortU : shortC L ≤ shortU L := inf_le_left

end Normal

structure ShortIso (L₁ L₂ : Type) [Group L₁] [Group L₂] where
  e : (L₁ ⧸ pCore 2 L₁) ≃* (L₂ ⧸ pCore 2 L₂)
  κ : ↥(shortU L₁) ≃* ↥(shortU L₂)
  mem_C : ∀ u : ↥(shortU L₁),
    ((κ u : ↥(shortU L₂)) : L₂) ∈ shortC L₂ ↔ (u : L₁) ∈ shortC L₁
  conj : ∀ (l₁ : L₁) (l₂ : L₂),
    e (l₁ : L₁ ⧸ pCore 2 L₁) = (l₂ : L₂ ⧸ pCore 2 L₂) →
      ∀ (u : ↥(shortU L₁)) (hu : l₁ * (u : L₁) * l₁⁻¹ ∈ shortU L₁),
        ((κ ⟨l₁ * (u : L₁) * l₁⁻¹, hu⟩ : ↥(shortU L₂)) : L₂) =
          l₂ * ((κ u : ↥(shortU L₂)) : L₂) * l₂⁻¹

namespace ShortIso

variable {L₁ L₂ : Type} [Group L₁] [Group L₂] (S : ShortIso L₁ L₂)

include S

def symm : ShortIso L₂ L₁ where
  e := S.e.symm
  κ := S.κ.symm
  mem_C u := by
    have h := S.mem_C (S.κ.symm u)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  conj l₂ l₁ h u hu := by
    have he : S.e (l₁ : L₁ ⧸ pCore 2 L₁) = (l₂ : L₂ ⧸ pCore 2 L₂) := by
      rw [← h, MulEquiv.apply_symm_apply]
    have hu' : l₁ * ((S.κ.symm u : ↥(shortU L₁)) : L₁) * l₁⁻¹ ∈ shortU L₁ :=
      (inferInstance : (shortU L₁).Normal).conj_mem _ (S.κ.symm u).2 l₁
    have h1 := S.conj l₁ l₂ he (S.κ.symm u) hu'
    rw [MulEquiv.apply_symm_apply] at h1
    have h3 : S.κ ⟨l₁ * ((S.κ.symm u : ↥(shortU L₁)) : L₁) * l₁⁻¹, hu'⟩ =
        ⟨l₂ * (u : L₂) * l₂⁻¹, hu⟩ := Subtype.ext h1
    show ((S.κ.symm ⟨l₂ * (u : L₂) * l₂⁻¹, hu⟩ : ↥(shortU L₁)) : L₁) =
      l₁ * ((S.κ.symm u : ↥(shortU L₁)) : L₁) * l₁⁻¹
    rw [← h3, MulEquiv.symm_apply_apply]

theorem quotient_type
    (h : CFSG.IsQuasisimple (L₁ ⧸ pCore 2 L₁) ∨ (Nat.card (L₁ ⧸ pCore 2 L₁)).Prime) :
    CFSG.IsQuasisimple (L₂ ⧸ pCore 2 L₂) ∨ (Nat.card (L₂ ⧸ pCore 2 L₂)).Prime := by
  rcases h with hq | hp
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e hq)
  · exact Or.inr (by rwa [← Nat.card_congr S.e.toEquiv])

theorem nonzero (h : shortC L₁ < shortU L₁) : shortC L₂ < shortU L₂ := by
  refine lt_of_le_of_ne shortC_le_shortU ?_
  intro heq
  obtain ⟨x, hxU, hxC⟩ := IsConcreteLE.exists_of_lt h
  have h1 : ((S.κ ⟨x, hxU⟩ : ↥(shortU L₂)) : L₂) ∈ shortU L₂ := (S.κ ⟨x, hxU⟩).2
  have h2 : ((S.κ ⟨x, hxU⟩ : ↥(shortU L₂)) : L₂) ∉ shortC L₂ := fun hc =>
    hxC ((S.mem_C ⟨x, hxU⟩).mp hc)
  rw [heq] at h2
  exact h2 h1

theorem irreducible
    (h : ∀ N : Subgroup L₁, N.Normal → N ≤ shortU L₁ → shortC L₁ ≤ N →
      N = shortC L₁ ∨ N = shortU L₁) :
    ∀ N : Subgroup L₂, N.Normal → N ≤ shortU L₂ → shortC L₂ ≤ N →
      N = shortC L₂ ∨ N = shortU L₂ := by
  intro N₂ hN₂ hNU hCN
  let N₁ : Subgroup L₁ :=
    ((N₂.comap (shortU L₂).subtype).comap S.κ.toMonoidHom).map (shortU L₁).subtype
  have hmem : ∀ x : L₁, x ∈ N₁ ↔
      ∃ hx : x ∈ shortU L₁, ((S.κ ⟨x, hx⟩ : ↥(shortU L₂)) : L₂) ∈ N₂ := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hx, hκ⟩
      exact ⟨⟨x, hx⟩, hκ, rfl⟩
  have hN₁ : N₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnU, hκ⟩ := (hmem n).mp hn
    have hgn : g * n * g⁻¹ ∈ shortU L₁ :=
      (inferInstance : (shortU L₁).Normal).conj_mem _ hnU g
    obtain ⟨l₂, hl₂⟩ := QuotientGroup.mk_surjective (S.e (g : L₁ ⧸ pCore 2 L₁))
    have hc := S.conj g l₂ hl₂.symm ⟨n, hnU⟩ hgn
    refine (hmem _).mpr ⟨hgn, ?_⟩
    rw [hc]
    exact hN₂.conj_mem _ hκ l₂
  have hN₁U : N₁ ≤ shortU L₁ := fun x hx => ((hmem x).mp hx).1
  have hC₁ : shortC L₁ ≤ N₁ := fun x hx =>
    (hmem x).mpr ⟨shortC_le_shortU hx, hCN ((S.mem_C ⟨x, shortC_le_shortU hx⟩).mpr hx)⟩
  have hback : ∀ y : L₂, y ∈ shortU L₂ → ∃ x : ↥(shortU L₁),
      ((S.κ x : ↥(shortU L₂)) : L₂) = y := fun y hy =>
    ⟨S.κ.symm ⟨y, hy⟩, by simp⟩
  rcases h N₁ hN₁ hN₁U hC₁ with h1 | h1
  · left
    refine le_antisymm (fun y hy => ?_) hCN
    obtain ⟨x, hx⟩ := hback y (hNU hy)
    have hxN : (x : L₁) ∈ N₁ := (hmem _).mpr ⟨x.2, by rw [hx]; exact hy⟩
    rw [h1] at hxN
    have := (S.mem_C x).mpr hxN
    rwa [hx] at this
  · right
    refine le_antisymm hNU (fun y hy => ?_)
    obtain ⟨x, hx⟩ := hback y hy
    have hxN : (x : L₁) ∈ N₁ := by rw [h1]; exact x.2
    obtain ⟨hx', hκ⟩ := (hmem _).mp hxN
    rwa [hx] at hκ

theorem altModule {n : ℕ} {φ : (L₂ ⧸ pCore 2 L₂) ≃* alternatingGroup (Fin (2 * n + 1))}
    (h : IsNaturalAltModuleWith L₂ n φ) : IsNaturalAltModuleWith L₁ n (S.e.trans φ) := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := h
  refine ⟨ψ.comp S.κ.toMonoidHom, fun u => h1 _, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu⟩ := h2 v hv
    exact ⟨S.κ.symm u, by simpa using hu⟩
  · ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_subgroupOf]
    have h5 : ψ (S.κ u) = 1 ↔ ((S.κ u : ↥(shortU L₂)) : L₂) ∈ shortC L₂ := by
      rw [← MonoidHom.mem_ker, h3, Subgroup.mem_subgroupOf]
    rw [h5, S.mem_C u]
  · intro l u hu hu'
    obtain ⟨l₂, hl₂⟩ := QuotientGroup.mk_surjective (S.e (l : L₁ ⧸ pCore 2 L₁))
    have hc := S.conj l l₂ hl₂.symm ⟨u, hu⟩ hu'
    have hu₂ : l₂ * ((S.κ ⟨u, hu⟩ : ↥(shortU L₂)) : L₂) * l₂⁻¹ ∈ shortU L₂ :=
      (inferInstance : (shortU L₂).Normal).conj_mem _ (S.κ ⟨u, hu⟩).2 l₂
    have hkeq : S.κ ⟨l * u * l⁻¹, hu'⟩ =
        ⟨l₂ * ((S.κ ⟨u, hu⟩ : ↥(shortU L₂)) : L₂) * l₂⁻¹, hu₂⟩ := Subtype.ext hc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hkeq]
    rw [h4 l₂ _ (S.κ ⟨u, hu⟩).2 hu₂, MulEquiv.trans_apply, ← hl₂]

theorem slModule {n : ℕ} (h : IsNaturalSLTwoModule L₂ n) : IsNaturalSLTwoModule L₁ n := by
  obtain ⟨φ, ψ, h1, h2, h3⟩ := h
  refine ⟨S.e.trans φ, ψ.comp S.κ.toMonoidHom, h1.comp S.κ.surjective, ?_, ?_⟩
  · ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_subgroupOf]
    have h5 : ψ (S.κ u) = 1 ↔ ((S.κ u : ↥(shortU L₂)) : L₂) ∈ shortC L₂ := by
      rw [← MonoidHom.mem_ker, h2, Subgroup.mem_subgroupOf]
    rw [h5, S.mem_C u]
  · intro l u hu hu'
    obtain ⟨l₂, hl₂⟩ := QuotientGroup.mk_surjective (S.e (l : L₁ ⧸ pCore 2 L₁))
    have hc := S.conj l l₂ hl₂.symm ⟨u, hu⟩ hu'
    have hu₂ : l₂ * ((S.κ ⟨u, hu⟩ : ↥(shortU L₂)) : L₂) * l₂⁻¹ ∈ shortU L₂ :=
      (inferInstance : (shortU L₂).Normal).conj_mem _ (S.κ ⟨u, hu⟩).2 l₂
    have hkeq : S.κ ⟨l * u * l⁻¹, hu'⟩ =
        ⟨l₂ * ((S.κ ⟨u, hu⟩ : ↥(shortU L₂)) : L₂) * l₂⁻¹, hu₂⟩ := Subtype.ext hc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hkeq]
    rw [h3 l₂ _ (S.κ ⟨u, hu⟩).2 hu₂, MulEquiv.trans_apply, ← hl₂]

end ShortIso

end CFSG.CGT.PushingUpLit.CGT6
