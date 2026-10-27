module

public import CFSG.ClassicalInvolution.Asc77.AscT3CII9Aut

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section CosetExt

variable {M : Type*} [Group M]

@[expose] def cosetExt (H : Subgroup M) (α : M) (h2 : ∀ d ∈ H, α⁻¹ * d * α ∈ H)
    (h3 : α * α ∈ H) : Subgroup M where
  carrier := {x | x ∈ H ∨ ∃ d ∈ H, x = α * d}
  one_mem' := Or.inl H.one_mem
  mul_mem' := by
    rintro x y (hx | ⟨d₁, hd₁, rfl⟩) (hy | ⟨d₂, hd₂, rfl⟩)
    · exact Or.inl (H.mul_mem hx hy)
    · refine Or.inr ⟨(α⁻¹ * x * α) * d₂, H.mul_mem (h2 x hx) hd₂, ?_⟩
      group
    · refine Or.inr ⟨d₁ * y, H.mul_mem hd₁ hy, ?_⟩
      group
    · refine Or.inl ?_
      have : α * d₁ * (α * d₂) = (α * α) * ((α⁻¹ * d₁ * α) * d₂) := by group
      rw [this]
      exact H.mul_mem h3 (H.mul_mem (h2 d₁ hd₁) hd₂)
  inv_mem' := by
    rintro x (hx | ⟨d, hd, rfl⟩)
    · exact Or.inl (H.inv_mem hx)
    · refine Or.inr ⟨α⁻¹ * (d⁻¹ * (α * α)⁻¹) * α, h2 _ (H.mul_mem (H.inv_mem hd)
        (H.inv_mem h3)), ?_⟩
      group

theorem mem_cosetExt {H : Subgroup M} {α : M} {h2 : ∀ d ∈ H, α⁻¹ * d * α ∈ H}
    {h3 : α * α ∈ H} {x : M} : x ∈ cosetExt H α h2 h3 ↔ x ∈ H ∨ ∃ d ∈ H, x = α * d := Iff.rfl

theorem le_cosetExt {H : Subgroup M} {α : M} {h2 : ∀ d ∈ H, α⁻¹ * d * α ∈ H}
    {h3 : α * α ∈ H} : H ≤ cosetExt H α h2 h3 := fun _ hx => Or.inl hx

theorem alpha_mem_cosetExt {H : Subgroup M} {α : M} {h2 : ∀ d ∈ H, α⁻¹ * d * α ∈ H}
    {h3 : α * α ∈ H} : α ∈ cosetExt H α h2 h3 := Or.inr ⟨1, H.one_mem, by group⟩

end CosetExt


section Main

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conj_conj_mem_range (γ : MulAut SL(2, F)) (x : SL(2, F)) :
    γ⁻¹ * MulAut.conj x * γ = MulAut.conj (γ⁻¹ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem exists_involution_mem_coset (hF : Odd (Nat.card F)) (hK : IsOddPrimePower (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (Q : Sylow 2 SL(2, F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {α : MulAut SL(2, F)} (hε : slEps F hK α = 1) (hρ : slRho F α = σ)
    {D : Subgroup (MulAut SL(2, F))}
    (hDI : D ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) (hD2 : IsPGroup 2 ↥D)
    (hDcard : 2 * Nat.card D = Nat.card Q) (hαD : ∀ d ∈ D, α⁻¹ * d * α ∈ D)
    (hα2 : α * α ∈ D) :
    ∃ d ∈ D, (α * d) * (α * d) = 1 ∧
      ∃ γ : MulAut SL(2, F), α * d = γ * slFieldAut F σ * γ⁻¹ := by
  classical
  have hfin : Finite (MulAut SL(2, F)) := finite_mulAut_sl2 F
  obtain ⟨Inn, hInn⟩ : ∃ Inn : Subgroup (MulAut SL(2, F)),
      Inn = (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := ⟨_, rfl⟩
  rw [← hInn] at hDI
  have hInnN : ∀ (γ : MulAut SL(2, F)), ∀ i ∈ Inn, γ⁻¹ * i * γ ∈ Inn := by
    subst hInn
    rintro γ _ ⟨x, rfl⟩
    exact ⟨γ⁻¹ x, (conj_conj_mem_range γ x).symm⟩
  have hα2Inn : α * α ∈ Inn := hDI hα2
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Subgroup (MulAut SL(2, F)),
      Γ = cosetExt Inn α (fun i hi => hInnN α i hi) hα2Inn := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Subgroup (MulAut SL(2, F)), P₁ = cosetExt D α hαD hα2 := ⟨_, rfl⟩
  have hP₁Γ : P₁ ≤ Γ := by
    rw [hP₁, hΓ]
    rintro x (hx | ⟨d, hd, rfl⟩)
    · exact Or.inl (hDI hx)
    · exact Or.inr ⟨d, hDI hd, rfl⟩
  have hP₁2 : IsPGroup 2 ↥P₁ := by
    intro x
    obtain ⟨x, hx⟩ := x
    rw [hP₁] at hx
    rcases hx with hx | ⟨d, hd, rfl⟩
    · obtain ⟨n, hn⟩ := hD2 ⟨x, hx⟩
      refine ⟨n, Subtype.ext ?_⟩
      have := congrArg Subtype.val hn
      simpa using this
    · have hsq : (α * d) * (α * d) ∈ D := by
        have : (α * d) * (α * d) = (α * α) * ((α⁻¹ * d * α) * d) := by group
        rw [this]
        exact D.mul_mem hα2 (D.mul_mem (hαD d hd) hd)
      obtain ⟨n, hn⟩ := hD2 ⟨_, hsq⟩
      refine ⟨n + 1, Subtype.ext ?_⟩
      have := congrArg Subtype.val hn
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [pow_succ', pow_mul, sq]
      exact this
  have hmax : ∀ P' : Subgroup (MulAut SL(2, F)), IsPGroup 2 ↥P' → P' ≤ Γ → P₁ ≤ P' →
      P' ≤ P₁ := by
    intro P' hP'2 hP'Γ hP₁P'
    have hDP' : D ≤ P' := by
      refine le_trans ?_ hP₁P'
      rw [hP₁]
      exact le_cosetExt
    have hαP' : α ∈ P' := by
      refine hP₁P' ?_
      rw [hP₁]
      exact alpha_mem_cosetExt
    have hU2 : IsPGroup 2 ↥(P' ⊓ Inn) := hP'2.to_le inf_le_left
    have hUcard : 2 * Nat.card ↥(P' ⊓ Inn) ≤ Nat.card Q :=
      two_mul_natCard_le_of_le_inn hF Q (hInn ▸ inf_le_right) hU2
    have hDU : D = P' ⊓ Inn :=
      Subgroup.eq_of_le_of_card_ge (le_inf hDP' hDI) (by omega)
    intro x hx
    have hxΓ := hP'Γ hx
    rw [hΓ] at hxΓ
    rcases hxΓ with hxI | ⟨i, hi, rfl⟩
    · have : x ∈ D := hDU ▸ ⟨hx, hxI⟩
      rw [hP₁]
      exact Or.inl this
    · have h1 : i ∈ P' ⊓ Inn := ⟨by
        have := P'.mul_mem (P'.inv_mem hαP') hx
        simpa using this, hi⟩
      have h2 : i ∈ D := hDU ▸ h1
      rw [hP₁]
      exact Or.inr ⟨i, h2, rfl⟩
  let SP : Sylow 2 ↥Γ :=
    { toSubgroup := P₁.subgroupOf Γ
      isPGroup' := hP₁2.comap_subtype
      is_maximal' := by
        intro Q' hQ'2 hle
        have h1 : P₁ ≤ Q'.map Γ.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hP₁Γ]
          exact Subgroup.map_mono hle
        have h2 := hmax (Q'.map Γ.subtype) (hQ'2.map _) (Subgroup.map_subtype_le _) h1
        refine le_antisymm ?_ hle
        rw [← Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective Q']
        exact Subgroup.comap_mono h2 }
  have hσfΓ : slFieldAut F σ ∈ Γ := by
    have hc : α * (slFieldAut F σ)⁻¹ ∈ Inn := by
      rw [hInn]
      apply (slEps_slRho_eq_one_iff F hK h4 _).mp
      constructor
      · have h1 : slEps F hK (α * (slFieldAut F σ)⁻¹) =
            slEps F hK α * (slEps F hK (slFieldAut F σ))⁻¹ := by
          rw [map_mul]
          exact congrArg _ (map_inv _ _)
        rw [h1, hε, slEps_slFieldAut]
        decide
      · rw [map_mul, map_inv, hρ, slRho_slFieldAut, mul_inv_cancel]
    rw [hΓ]
    exact Or.inr ⟨α⁻¹ * (α * (slFieldAut F σ)⁻¹)⁻¹ * α, hInnN α _ (Inn.inv_mem hc), by group⟩
  have hσfsq : slFieldAut F σ * slFieldAut F σ = 1 := by
    rw [← slFieldAut_mul, hσ2, slFieldAut_one]
  set σ' : ↥Γ := ⟨slFieldAut F σ, hσfΓ⟩ with hσ'
  have hσ'2 : IsPGroup 2 ↥(Subgroup.zpowers σ') := by
    have h1 : σ' ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext hσfsq
    have hd : orderOf σ' ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  obtain ⟨Q₀, hQ₀⟩ := hσ'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ Q₀ SP
  have hmem : g * σ' * g⁻¹ ∈ (SP : Subgroup ↥Γ) := by
    have h1 : (MulAut.conj g) σ' ∈ (MulAut.conj g) • (Q₀ : Subgroup ↥Γ) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ₀ (Subgroup.mem_zpowers _))
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    simpa [MulAut.conj_apply] using h1
  have hiP₁ : (g : MulAut SL(2, F)) * slFieldAut F σ * (g : MulAut SL(2, F))⁻¹ ∈ P₁ := hmem
  set γ : MulAut SL(2, F) := (g : MulAut SL(2, F)) with hγ
  have hρi : slRho F (γ * slFieldAut F σ * γ⁻¹) = σ := by
    rw [map_mul, map_mul, map_inv, slRho_slFieldAut]
    exact ringAut_conj_eq _ _
  have hiInn : γ * slFieldAut F σ * γ⁻¹ ∉ Inn := by
    intro h
    rw [hInn] at h
    have := (slEps_slRho_eq_one_iff F hK h4 _).mpr h
    exact hσ1 (hρi ▸ this.2)
  rw [hP₁] at hiP₁
  rcases hiP₁ with hiD | ⟨d, hd, hdi⟩
  · exact absurd (hDI hiD) hiInn
  · refine ⟨d, hd, ?_, γ, hdi.symm⟩
    rw [← hdi]
    have : γ * slFieldAut F σ * γ⁻¹ * (γ * slFieldAut F σ * γ⁻¹) = 1 := by
      calc γ * slFieldAut F σ * γ⁻¹ * (γ * slFieldAut F σ * γ⁻¹)
          = γ * (slFieldAut F σ * slFieldAut F σ) * γ⁻¹ := by group
        _ = 1 := by rw [hσfsq]; group
    exact this

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
