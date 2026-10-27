module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2General

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3

section Embedded

variable {K : Type} [Field K] [Finite K]

theorem no_offender_of_inner_rank
    (hK : ringChar K ≠ 2) {Hg : Type*} [Group Hg]
    (j : Hg →* PGL2 K) (hj : Function.Injective j) (hS : pglS K ≤ j.range)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E))
    (hinner : ∀ a : Hg, j a ∈ pglS K → a ≠ 1 → a * a = 1 →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (disp ρ a)))
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρ B) ≤
      Nat.log 2 (Nat.card B)) : False := by
  obtain ⟨-, hidx, -, -, hpair⟩ := projective_involution_pairing K hK
  have hBmap : Nat.card B ≤ 4 := by
    have : CFSG.IsElementaryAbelian 2 (B.map j) := by
      refine isElementaryAbelian_two_of ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hBc a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_mul, hB2 a ha, map_one]
    have h4 := card_le_four_of_elementaryAbelian hK (B.map j)
    exact (Nat.card_congr (B.equivMapOfInjective j hj).toEquiv).le.trans h4
  have hlog : Nat.log 2 (Nat.card B) ≤ 2 := (Nat.log_mono_right hBmap).trans (by norm_num)
  by_cases hcase : ∃ a ∈ B, j a ∈ pglS K ∧ a ≠ 1
  · obtain ⟨a, haB, haS, ha1⟩ := hcase
    have h1 := finrank_range_disp_le_of_offender ρ haB (hoff.trans hlog)
    have h3 := hinner a haS ha1 (hB2 a haB)
    omega
  · push Not at hcase
    obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
      obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
      exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
    have ht2 : t * t = 1 := hB2 t htB
    have htS : j t ∉ pglS K := fun h => ht1 (hcase t htB h)
    have hBsub : ∀ b ∈ B, b = 1 ∨ b = t := by
      intro b hb
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · right
        have hbS : j b ∉ pglS K := fun h => hb1 (hcase b hb h)
        have hmem : j (b * t⁻¹) ∈ pglS K := by
          rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx]
          simp [hbS, htS]
        have : b * t⁻¹ = 1 := hcase _ (B.mul_mem hb (B.inv_mem htB)) hmem
        exact mul_inv_eq_one.1 this
    have hcardB : Nat.card B ≤ 2 := by
      have hsub : (B : Set Hg) ⊆ {1, t} := fun b hb => by
        rcases hBsub b hb with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc Nat.card B = Set.ncard (B : Set Hg) := (Nat.card_coe_set_eq _).symm
        _ ≤ Set.ncard ({1, t} : Set Hg) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ Set.ncard ({t} : Set Hg) + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hlog1 : Nat.log 2 (Nat.card B) ≤ 1 := (Nat.log_mono_right hcardB).trans (by norm_num)
    have hrt : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) ≤ 1 :=
      finrank_range_disp_le_of_offender ρ htB (hoff.trans hlog1)
    have hτ2 : j t * j t = 1 := by rw [← map_mul, ht2, map_one]
    have hτ1 : j t ≠ 1 := fun h => ht1 (hj (by rw [h, map_one]))
    obtain ⟨s, hsS, hst, hcomm⟩ := hpair (j t) hτ2 hτ1
    obtain ⟨s₀, hs₀⟩ := MonoidHom.mem_range.1 (hS hsS)
    set t' := s₀⁻¹ * t * s₀ with ht'
    have hjt' : j t' = s⁻¹ * j t * s := by
      rw [ht', map_mul, map_mul, map_inv, hs₀]
    have hrt' : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t')) ≤ 1 := by
      have h1 := finrank_range_disp_conj ρ t s₀⁻¹
      rw [inv_inv] at h1
      rw [ht', h1]
      exact hrt
    have ht'S : j t' ∉ pglS K := by
      intro h
      apply htS
      have hs' : s⁻¹ ∈ pglS K := (pglS K).inv_mem hsS
      have : j t = s * j t' * s⁻¹ := by rw [hjt']; group
      rw [this]
      exact (pglS K).mul_mem ((pglS K).mul_mem hsS h) hs'
    have hjaS : j (t * t') ∈ pglS K := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two hidx]
      simp [htS, ht'S]
    have hne : t * t' ≠ 1 := by
      intro h
      apply hst
      have h1 : t' = t⁻¹ := eq_inv_of_mul_eq_one_right h
      have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [← hjt', h1, h2]
    have hcomm' : t * t' = t' * t := by
      apply hj
      rw [map_mul j t t', map_mul j t' t, hjt']
      exact hcomm.eq
    have ht'2 : t' * t' = 1 := by
      calc t' * t' = s₀⁻¹ * (t * t) * s₀ := by rw [ht']; group
        _ = 1 := by rw [ht2]; group
    have hsq : (t * t') * (t * t') = 1 := by
      calc (t * t') * (t * t') = t * (t' * t) * t' := by group
        _ = t * (t * t') * t' := by rw [← hcomm']
        _ = (t * t) * (t' * t') := by group
        _ = 1 := by rw [ht2, ht'2, mul_one]
    have h1 := finrank_range_disp_mul_le ρ t t'
    have h3 := hinner (t * t') hjaS hne hsq
    omega

end Embedded

end CFSG.QuasithinUnique.Setup.Family
