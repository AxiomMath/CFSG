module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Gen
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section U19

section General2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem fuse_generalM (hΩ : HypOmegaGen Ω) {L L' : Subgroup G} {t : G} (hLΩ : L ∈ Ω)
    (hL'Ω : L' ∈ Ω) (hne : L' ≠ L) (hzL : IsUniqueInvolution L t) (hzL' : IsUniqueInvolution L' t)
    {M : Subgroup G} (hLM : L ⊔ L' ≤ M) {A A' : Subgroup G} (hA : IsSylow2In A L) (hA' : IsSylow2In A' L') (hAc : Commutes A A')
    (hstd : ∀ a ∈ A, ∀ x ∈ A, ∀ b ∈ A', ∀ y ∈ A', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set G), g ∈ M ∧ g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y)
    {u : G} (huM : u ∈ L ⊔ L') (hu1 : u ≠ 1) (huz : u ≠ t) (hu2 : u * u = 1)
    {R₁ R₂ : Subgroup G} (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂)
    {x y : G} (hx : x ∈ R₁) (hy : y ∈ R₂) (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set G), c ∈ M ∧ c * u * c⁻¹ = x * y := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hLΩ hL'Ω hne.symm hzL hzL'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL'Ω hLΩ hne hzL' hzL
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({t} : Set G) := sup_le hLC hL'C
  have hMNL : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hL'N
  have hMNL' : L ⊔ L' ≤ Subgroup.normalizer (L' : Set G) := sup_le hLN Subgroup.le_normalizer
  obtain ⟨m₂, hm₂M, a, ha, b, hb, haa, hbb, hab⟩ :=
    exists_ab hΩ hLΩ hL'Ω hne hzL hzL' huM hu1 huz hu2 hR₁ hR₂ hc
  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hQs : IsSylow2In (A ⊔ A') (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hA hA' hAc
  obtain ⟨m₁, hm₁M, hm₁⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In hQs hQ
  have hz1 : m₁ * t * m₁⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₁M)
    calc m₁ * t * m₁⁻¹ = (t * m₁) * m₁⁻¹ := by rw [this]
      _ = t := by group
  have hm₁L : conjSub m₁ L = L := mem_normalizer_iff_conjSub_eq.mp (hMNL hm₁M)
  have hm₁L' : conjSub m₁ L' = L' := mem_normalizer_iff_conjSub_eq.mp (hMNL' hm₁M)
  have hQ2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hQ.2.1
  have hAeq : conjSub m₁ A = R₁ := by
    have h1 : conjSub m₁ A ≤ (R₁ ⊔ R₂) ⊓ L := by
      refine le_inf ?_ ?_
      · rw [← hm₁]; exact conjSub_mono le_sup_left
      · have := conjSub_mono (n := m₁) hA.1
        rwa [hm₁L] at this
    have h2 : (R₁ ⊔ R₂) ⊓ L = R₁ :=
      hR₁.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_left hR₁.1)
    rw [h2] at h1
    have hs : IsSylow2In (conjSub m₁ A) L := by
      have := hA.conj m₁
      rwa [hm₁L] at this
    exact (hs.eq_of_le hR₁.2.1 hR₁.1 h1).symm
  have hA'eq : conjSub m₁ A' = R₂ := by
    have h1 : conjSub m₁ A' ≤ (R₁ ⊔ R₂) ⊓ L' := by
      refine le_inf ?_ ?_
      · rw [← hm₁]; exact conjSub_mono le_sup_right
      · have := conjSub_mono (n := m₁) hA'.1
        rwa [hm₁L'] at this
    have h2 : (R₁ ⊔ R₂) ⊓ L' = R₂ :=
      hR₂.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_right hR₂.1)
    rw [h2] at h1
    have hs : IsSylow2In (conjSub m₁ A') L' := by
      have := hA'.conj m₁
      rwa [hm₁L'] at this
    exact (hs.eq_of_le hR₂.2.1 hR₂.1 h1).symm
  have hmem : ∀ {w : G} {B₀ B₁ : Subgroup G}, conjSub m₁ B₀ = B₁ → w ∈ B₁ → m₁⁻¹ * w * m₁ ∈ B₀ := by
    intro w B₀ B₁ h hw
    rw [← h] at hw
    exact mem_conjSub_iff.mp hw
  have hxx : x * x = t := TwinPerp.sq_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hyy : y * y = t := TwinPerp.sq_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
  have hsq : ∀ {w : G}, w * w = t → (m₁⁻¹ * w * m₁) * (m₁⁻¹ * w * m₁) = t := by
    intro w hw
    calc (m₁⁻¹ * w * m₁) * (m₁⁻¹ * w * m₁) = m₁⁻¹ * (w * w) * m₁ := by group
      _ = m₁⁻¹ * t * m₁ := by rw [hw]
      _ = t := by
        calc m₁⁻¹ * t * m₁ = m₁⁻¹ * (m₁ * t * m₁⁻¹) * m₁ := by rw [hz1]
          _ = t := by group
  obtain ⟨c₀, hc₀t, hc₀M, hc₀a, hc₀b⟩ := hstd _ (hmem hAeq ha) _ (hmem hAeq hx) _ (hmem hA'eq hb) _
    (hmem hA'eq hy) (hsq haa) (hsq hxx) (hsq hbb) (hsq hyy)
  have hc₀t' : c₀ * t = t * c₀ := Subgroup.mem_centralizer_singleton_iff.mp hc₀t
  set c₁ := m₁ * c₀ * m₁⁻¹ with hc₁
  have hc₁t : c₁ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm₁t : m₁ * t = t * m₁ := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₁M)
    calc c₁ * t = m₁ * c₀ * m₁⁻¹ * t := rfl
      _ = m₁ * c₀ * (m₁⁻¹ * t) := by group
      _ = m₁ * c₀ * (t * m₁⁻¹) := by
          rw [show m₁⁻¹ * t = t * m₁⁻¹ by
            calc m₁⁻¹ * t = m₁⁻¹ * (t * m₁) * m₁⁻¹ := by group
              _ = m₁⁻¹ * (m₁ * t) * m₁⁻¹ := by rw [hm₁t]
              _ = t * m₁⁻¹ := by group]
      _ = m₁ * (c₀ * t) * m₁⁻¹ := by group
      _ = m₁ * (t * c₀) * m₁⁻¹ := by rw [hc₀t']
      _ = (m₁ * t) * c₀ * m₁⁻¹ := by group
      _ = (t * m₁) * c₀ * m₁⁻¹ := by rw [hm₁t]
      _ = t * c₁ := by rw [hc₁]; group
  have hm₂t : m₂ * t = t * m₂ := Subgroup.mem_centralizer_singleton_iff.mp (hMC hm₂M)
  have hc₁M : c₁ ∈ M := M.mul_mem (M.mul_mem (hLM hm₁M) hc₀M) (M.inv_mem (hLM hm₁M))
  refine ⟨c₁ * m₂, ?_, M.mul_mem hc₁M (hLM hm₂M), ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c₁ * t = t * c₁ := Subgroup.mem_centralizer_singleton_iff.mp hc₁t
    calc c₁ * m₂ * t = c₁ * (m₂ * t) := by group
      _ = c₁ * (t * m₂) := by rw [hm₂t]
      _ = (c₁ * t) * m₂ := by group
      _ = (t * c₁) * m₂ := by rw [h1]
      _ = t * (c₁ * m₂) := by group
  · have hca : c₁ * a * c₁⁻¹ = x := by
      calc c₁ * a * c₁⁻¹ = m₁ * (c₀ * (m₁⁻¹ * a * m₁) * c₀⁻¹) * m₁⁻¹ := by rw [hc₁]; group
        _ = m₁ * (m₁⁻¹ * x * m₁) * m₁⁻¹ := by rw [hc₀a]
        _ = x := by group
    have hcb : c₁ * b * c₁⁻¹ = y := by
      calc c₁ * b * c₁⁻¹ = m₁ * (c₀ * (m₁⁻¹ * b * m₁) * c₀⁻¹) * m₁⁻¹ := by rw [hc₁]; group
        _ = m₁ * (m₁⁻¹ * y * m₁) * m₁⁻¹ := by rw [hc₀b]
        _ = y := by group
    calc c₁ * m₂ * u * (c₁ * m₂)⁻¹ = c₁ * (m₂ * u * m₂⁻¹) * c₁⁻¹ := by group
      _ = c₁ * (a * b) * c₁⁻¹ := by rw [hab]
      _ = (c₁ * a * c₁⁻¹) * (c₁ * b * c₁⁻¹) := by group
      _ = x * y := by rw [hca, hcb]

end General2

end U19

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
