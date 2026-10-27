module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsA4Block.le_of_forall_order_three {L U N : Subgroup G} (h : IsA4Block L U)
    (hN : ∀ y ∈ L, y ^ 3 = 1 → y ∈ N) : L ≤ N := by
  obtain ⟨c, hcL, hc3', hcN, hcfp, hLc⟩ := h.exists_c
  have hc3 : c ^ 3 = 1 := by rw [← hc3']; exact pow_orderOf_eq_one c
  have hcN' : c ∈ N := hN c hcL hc3
  have hnt : Nontrivial ↥U := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card_U]; norm_num)
  obtain ⟨u, hu1⟩ := exists_ne (1 : ↥U)
  have huU : (u : G) ∈ U := u.2
  have hu1' : (u : G) ≠ 1 := fun h' => hu1 (Subtype.ext h')
  have huL : (u : G) ∈ L := h.le huU
  have hucu : (u : G) * c * (u : G)⁻¹ ∈ N := by
    refine hN _ (L.mul_mem (L.mul_mem huL hcL) (L.inv_mem huL)) ?_
    calc ((u : G) * c * (u : G)⁻¹) ^ 3 = (u : G) * c ^ 3 * (u : G)⁻¹ := by
          rw [pow_three', pow_three']
          group
      _ = 1 := by rw [hc3]; group
  have hvN : (u : G) * c * (u : G)⁻¹ * c⁻¹ ∈ N := N.mul_mem hucu (N.inv_mem hcN')
  have hvU : (u : G) * c * (u : G)⁻¹ * c⁻¹ ∈ U := by
    have h1 : c * (u : G)⁻¹ * c⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hcN ((u : G)⁻¹)).mp (U.inv_mem huU)
    have h2 : (u : G) * c * (u : G)⁻¹ * c⁻¹ = (u : G) * (c * (u : G)⁻¹ * c⁻¹) := by group
    rw [h2]
    exact U.mul_mem huU h1
  have hv1 : (u : G) * c * (u : G)⁻¹ * c⁻¹ ≠ 1 := by
    intro h1
    apply hcfp (u : G) huU hu1'
    have h2 : (u : G) * c * (u : G)⁻¹ = c := mul_inv_eq_one.mp h1
    have huc : (u : G) * c = c * (u : G) := by
      calc (u : G) * c = ((u : G) * c * (u : G)⁻¹) * (u : G) := by group
        _ = c * (u : G) := by rw [h2]
    calc c * (u : G) * c⁻¹ = ((u : G) * c) * c⁻¹ := by rw [huc]
      _ = (u : G) := by group
  have hUN : U ≤ N := by
    intro w hw
    have hel := IsA4Block.elements h hcN hc3 hcfp hvU hv1 w hw
    rcases hel with h1 | h1 | h1 | h1
    · rw [h1]; exact N.one_mem
    · rw [h1]; exact hvN
    · rw [h1]; exact N.mul_mem (N.mul_mem hcN' hvN) (N.inv_mem hcN')
    · rw [h1]
      exact N.mul_mem (N.mul_mem hcN' (N.mul_mem (N.mul_mem hcN' hvN) (N.inv_mem hcN')))
        (N.inv_mem hcN')
  rw [hLc]
  exact sup_le hUN (Subgroup.zpowers_le.mpr hcN')

theorem IsA4Block.card_ne_six {L U W : Subgroup G} (h : IsA4Block L U) (hWL : W ≤ L) :
    Nat.card W ≠ 6 := by
  intro h6
  set W' : Subgroup ↥L := W.subgroupOf L with hW'
  have hcardW' : Nat.card W' = 6 := by
    rw [hW', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
    exact h6
  have hidx : W'.index = 2 := by
    have h1 := Subgroup.card_mul_index W'
    rw [hcardW', h.card_L] at h1
    omega
  have hsq : ∀ y ∈ L, y ^ 3 = 1 → y ∈ W := by
    intro y hy hy3
    have h1 : (⟨y⁻¹, L.inv_mem hy⟩ : ↥L) * ⟨y⁻¹, L.inv_mem hy⟩ ∈ W' :=
      Subgroup.mul_self_mem_of_index_two hidx _
    have h3 : y⁻¹ * y⁻¹ ∈ W := h1
    have hyyy : y * y * y = 1 := by rw [← pow_three']; exact hy3
    have h2 : y⁻¹ * y⁻¹ = y := by
      calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * (y * y * y) := by rw [hyyy, mul_one]
        _ = y := by group
    rw [h2] at h3
    exact h3
  have hLW : L ≤ W := h.le_of_forall_order_three hsq
  have hWeq : W = L := le_antisymm hWL hLW
  rw [hWeq, h.card_L] at h6
  omega

theorem card_dvd_factorial_of_simple {A : Type} [Group A] [Finite A] (hA : IsSimpleGroup A)
    {H : Subgroup A} (hH : H ≠ ⊤) : Nat.card A ∣ Nat.factorial H.index := by
  have hnc : H.normalCore = ⊥ := by
    rcases hA.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exfalso
      apply hH
      rw [eq_top_iff, ← h]
      exact H.normalCore_le
  have h1 := H.index_normalCore_dvd_factorial_index
  rwa [hnc, Subgroup.index_bot] at h1

theorem card_le_sixty_of_simple {A : Type} [Group A] [Finite A] (hA : IsSimpleGroup A)
    (hcard : Nat.card A = 360) {H : Subgroup A} (hH : H ≠ ⊤) : Nat.card H ≤ 60 := by
  have hdvd := card_dvd_factorial_of_simple hA hH
  rw [hcard] at hdvd
  have h6 : 6 ≤ H.index := by
    by_contra hcon
    have hle : H.index ≤ 5 := by omega
    have h1 : Nat.factorial H.index ≤ Nat.factorial 5 := Nat.factorial_le hle
    have h2 : 360 ≤ Nat.factorial H.index := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    have h3 : Nat.factorial 5 = 120 := by decide
    omega
  have h1 := Subgroup.card_mul_index H
  rw [hcard] at h1
  by_contra hcon
  have : 61 * 6 ≤ Nat.card H * H.index :=
    Nat.mul_le_mul (by omega) h6
  omega

theorem eq_of_two_A4 {A C Λ₁ Λ₂ V₂ : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 6))
    (hCA : C ≤ A) (hΛ₁C : Λ₁ ≤ C) (hΛ₂C : Λ₂ ≤ C) (hΛ₁ : Nat.card Λ₁ = 12)
    (hΛ₂ : IsA4Block Λ₂ V₂) {z : G} (hzΛ₂ : z ∈ Λ₂) (hzΛ₁ : z ∉ Λ₁) (hz2 : z * z = 1)
    (hzN : z ∈ normalizer (Λ₁ : Set G)) : C = A := by
  by_contra hCne
  have hAcard : Nat.card ↥A = 360 := (Nat.card_congr e.toEquiv).trans card_alt6'
  have hAsimple : IsSimpleGroup ↥A :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  have hCtop : C.subgroupOf A ≠ ⊤ := by
    intro htop
    apply hCne
    exact le_antisymm hCA (Subgroup.subgroupOf_eq_top.mp htop)
  have hC60 : Nat.card C ≤ 60 := by
    have := card_le_sixty_of_simple hAsimple hAcard hCtop
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv] at this
  have hz1 : z ≠ 1 := fun h => hzΛ₁ (h ▸ Λ₁.one_mem)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hzN' : Subgroup.zpowers z ≤ normalizer (Λ₁ : Set G) := Subgroup.zpowers_le.mpr hzN
  have hinf : Nat.card ↥(Subgroup.zpowers z ⊓ Λ₁) = 1 := by
    have hd : Nat.card ↥(Subgroup.zpowers z ⊓ Λ₁) ∣ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers z ⊓ Λ₁ ≤ Subgroup.zpowers z)
      rwa [hzcard] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact h1
    · exfalso
      have heq : Subgroup.zpowers z ⊓ Λ₁ = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hzcard, h2])
      apply hzΛ₁
      have : z ∈ Subgroup.zpowers z ⊓ Λ₁ := by rw [heq]; exact Subgroup.mem_zpowers z
      exact this.2
  have hS24 : Nat.card ↥(Subgroup.zpowers z ⊔ Λ₁) = 24 := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hzN'
    rw [hinf, hzcard, hΛ₁] at h1
    omega
  have hSC : Subgroup.zpowers z ⊔ Λ₁ ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr (hΛ₂C hzΛ₂)) hΛ₁C
  have h24C : 24 ∣ Nat.card C := hS24 ▸ Subgroup.card_dvd_of_le hSC
  have hC24 : Nat.card C = 24 := by
    obtain ⟨k, hk⟩ := h24C
    have hk1 : 1 ≤ k := by
      by_contra hcon
      have : k = 0 := by omega
      have h0 : Nat.card C = 0 := by rw [hk, this]
      exact Nat.card_pos.ne' h0
    have hk2 : k ≤ 2 := by omega
    have hdvdC : Nat.card C ∣ 360 := hAcard ▸ Subgroup.card_dvd_of_le hCA
    interval_cases k
    · omega
    · rw [hk] at hdvdC
      norm_num at hdvdC
  have hCS : Subgroup.zpowers z ⊔ Λ₁ = C :=
    Subgroup.eq_of_le_of_card_ge hSC (by rw [hC24, hS24])
  have hSN : Subgroup.zpowers z ⊔ Λ₁ ≤ normalizer (Λ₁ : Set G) :=
    sup_le hzN' (Subgroup.le_normalizer)
  have hCle : C ≤ Subgroup.zpowers z ⊔ Λ₁ := hCS.symm.le
  have hΛ₂S : Λ₂ ≤ Subgroup.zpowers z ⊔ Λ₁ := hΛ₂C.trans hCle
  have hΛ₁S : Λ₁ ≤ Subgroup.zpowers z ⊔ Λ₁ := hΛ₁C.trans hCle
  have hΛ₂N : Λ₂ ≤ normalizer (Λ₁ : Set G) := hΛ₂S.trans hSN
  have hΛ₂card : Nat.card Λ₂ = 12 := hΛ₂.card_L
  have h144 := C5.card_sup_mul_card_inf_of_le_normalizer hΛ₂N
  rw [hΛ₂card, hΛ₁] at h144
  have hsup24 : Nat.card ↥(Λ₂ ⊔ Λ₁) ≤ 24 := by
    have := Subgroup.card_le_of_le (sup_le hΛ₂S hΛ₁S : Λ₂ ⊔ Λ₁ ≤ Subgroup.zpowers z ⊔ Λ₁)
    omega
  have hW6 : 6 ≤ Nat.card ↥(Λ₂ ⊓ Λ₁) := by
    have h1 : Nat.card ↥(Λ₂ ⊔ Λ₁) * Nat.card ↥(Λ₂ ⊓ Λ₁) ≤ 24 * Nat.card ↥(Λ₂ ⊓ Λ₁) :=
      Nat.mul_le_mul_right _ hsup24
    omega
  have hWdvd : Nat.card ↥(Λ₂ ⊓ Λ₁) ∣ 12 :=
    hΛ₂card ▸ Subgroup.card_dvd_of_le (inf_le_left : Λ₂ ⊓ Λ₁ ≤ Λ₂)
  have hWne : Nat.card ↥(Λ₂ ⊓ Λ₁) ≠ 12 := by
    intro h12
    have heq : Λ₂ ⊓ Λ₁ = Λ₂ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h12, hΛ₂card])
    apply hzΛ₁
    have : z ∈ Λ₂ ⊓ Λ₁ := by rw [heq]; exact hzΛ₂
    exact this.2
  have hW : Nat.card ↥(Λ₂ ⊓ Λ₁) = 6 := by
    have hle : Nat.card ↥(Λ₂ ⊓ Λ₁) ≤ 12 := Nat.le_of_dvd (by norm_num) hWdvd
    generalize Nat.card ↥(Λ₂ ⊓ Λ₁) = w at hW6 hWdvd hWne hle ⊢
    interval_cases w <;> omega
  exact hΛ₂.card_ne_six inf_le_left hW

end CFSG.QuasithinUnique.DoubleA3
