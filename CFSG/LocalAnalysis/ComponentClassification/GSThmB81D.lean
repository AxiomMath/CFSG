module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem injOn_D : Set.InjOn (QuotientGroup.mk' (pPrimeCore 2 ↥h.J))
    ((h.D.subgroupOf h.J : Subgroup ↥h.J) : Set ↥h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥h.J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥h.J))
  exact Eight.injOn_of_isPGroup hker
    ((h.toHyp52.isPGroup_S.to_le (inf_le_left : h.D ≤ h.S)).comap_subtype)

theorem D_facts (hSy : CFL2Sylow) (F : d.Facts) :
    (∃ t ∈ h.D, t * t ≠ 1 ∧ ∀ e ∈ h.D, t * t * e = e * (t * t)) ∧
      ∀ e ∈ h.D, ∃ i ∈ h.D, ∃ j ∈ h.D, i * i = 1 ∧ j * j = 1 ∧ e = i * j := by
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  obtain ⟨-, ⟨t, htT, ht1, htc⟩, hprod⟩ := hSy _ p' f' hp' hp2' hf' hJL T (hTD ▸ F.eight_le)
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥h.J) with hq
  have hinj := injOn_D (h := h)
  have hlift : ∀ s ∈ (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)),
      ∃ e : ↥h.J, (e : H) ∈ h.D ∧ q e = s := by
    intro s hs
    rw [hT] at hs
    obtain ⟨e, he, rfl⟩ := mem_map.mp hs
    exact ⟨e, mem_subgroupOf.mp he, rfl⟩
  have hDT : ∀ e : ↥h.J, (e : H) ∈ h.D → q e ∈ (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) := by
    intro e he
    rw [hT]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr he)
  have hinj' : ∀ e₁ e₂ : ↥h.J, (e₁ : H) ∈ h.D → (e₂ : H) ∈ h.D → q e₁ = q e₂ → e₁ = e₂ :=
    fun e₁ e₂ h1 h2 h3 => hinj (mem_subgroupOf.mpr h1) (mem_subgroupOf.mpr h2) h3
  refine ⟨?_, ?_⟩
  · obtain ⟨t₀, ht₀D, rfl⟩ := hlift t htT
    refine ⟨t₀, ht₀D, fun h1 => ht1 ?_, fun e he => ?_⟩
    · rw [← map_mul, show t₀ * t₀ = 1 from Subtype.ext h1, map_one]
    · have heJ : e ∈ h.J := (inf_le_right : h.D ≤ h.J) he
      have h2 := hinj' (t₀ * t₀ * ⟨e, heJ⟩) (⟨e, heJ⟩ * (t₀ * t₀))
        (mul_mem (mul_mem ht₀D ht₀D) he) (mul_mem he (mul_mem ht₀D ht₀D)) (by
          rw [map_mul, map_mul, map_mul]
          exact (mem_centralizer_iff.mp htc _ (hDT ⟨e, heJ⟩ he)).symm)
      exact congrArg Subtype.val h2
  · intro e he
    have heJ : e ∈ h.J := (inf_le_right : h.D ≤ h.J) he
    obtain ⟨i', hi', j', hj', hi2, hj2, hij⟩ := hprod (q ⟨e, heJ⟩) (hDT ⟨e, heJ⟩ he)
    obtain ⟨i, hiD, rfl⟩ := hlift i' hi'
    obtain ⟨j, hjD, rfl⟩ := hlift j' hj'
    have hi : (i : H) * i = 1 := by
      have := hinj' (i * i) 1 (mul_mem hiD hiD) (one_mem _) (by rw [map_mul, hi2, map_one])
      exact congrArg Subtype.val this
    have hj : (j : H) * j = 1 := by
      have := hinj' (j * j) 1 (mul_mem hjD hjD) (one_mem _) (by rw [map_mul, hj2, map_one])
      exact congrArg Subtype.val this
    have he' := hinj' ⟨e, heJ⟩ (i * j) he (mul_mem hiD hjD) (by rw [map_mul]; exact hij)
    exact ⟨i, hiD, j, hjD, hi, hj, congrArg Subtype.val he'⟩

theorem exists_noncentral_inv (hSy : CFL2Sylow) (F : d.Facts) :
    ∃ i ∈ h.D, i * i = 1 ∧ ∃ e ∈ h.D, i * e ≠ e * i := by
  obtain ⟨⟨t, htD, ht1, -⟩, hprod⟩ := d.D_facts hSy F
  obtain ⟨i, hiD, j, hjD, hi, hj, rfl⟩ := hprod t htD
  by_contra hne
  push Not at hne
  apply ht1
  have hic : ∀ e ∈ h.D, i * e = e * i := fun e he => by
    by_cases h1 : i * i = 1
    · exact hne i hiD h1 e he
    · exact absurd hi h1
  have hjc : ∀ e ∈ h.D, j * e = e * j := fun e he => hne j hjD hj e he
  calc i * j * (i * j) = i * (j * i) * j := by group
    _ = i * (i * j) * j := by rw [hjc i hiD]
    _ = (i * i) * (j * j) := by group
    _ = 1 := by rw [hi, hj, one_mul]

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
