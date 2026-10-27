module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDSkeleton
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Blueprint GorensteinWalter CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.LocalAnalysis.ComponentInitial

theorem card_inf_centralizer_conj {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H)
    (r : G) : Nat.card (H ⊓ centralizer ({g * r * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (H ⊓ centralizer ({r} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun p => ⟨g⁻¹ * p * g, mem_inf.mpr ⟨?_, ?_⟩⟩
      invFun := fun p => ⟨g * p * g⁻¹, mem_inf.mpr ⟨?_, ?_⟩⟩
      left_inv := fun p => Subtype.ext (by simp [mul_assoc])
      right_inv := fun p => Subtype.ext (by simp [mul_assoc]) }
  · exact mul_mem (mul_mem (inv_mem hg) (mem_inf.mp p.2).1) hg
  · have h := mem_centralizer_singleton_iff.mp (mem_inf.mp p.2).2
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * p * g * r = g⁻¹ * (p * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * p) * g := by rw [h]
      _ = r * (g⁻¹ * p * g) := by group
  · exact mul_mem (mul_mem hg (mem_inf.mp p.2).1) (inv_mem hg)
  · have h := mem_centralizer_singleton_iff.mp (mem_inf.mp p.2).2
    rw [mem_centralizer_singleton_iff]
    calc g * p * g⁻¹ * (g * r * g⁻¹) = g * (p * r) * g⁻¹ := by group
      _ = g * (r * p) * g⁻¹ := by rw [h]
      _ = g * r * g⁻¹ * (g * p * g⁻¹) := by group

theorem card_centralizer_of_HS {X : Type*} [Group X] (e : X ≃* NativeSporadic.HS) {t : X}
    (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set X)) = 7680 ∨ Nat.card (centralizer ({t} : Set X)) = 2880 := by
  set φ : X ≃* hsP := e.trans hsPermEquiv with hφ
  set τ : Equiv.Perm (Fin 3850) := (φ t : Equiv.Perm (Fin 3850)) with hτ
  have hτP : τ ∈ hsP := (φ t).2
  have hτ2 : orderOf τ = 2 := by
    rw [hτ, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hc : Nat.card (centralizer ({t} : Set X)) =
      Nat.card (hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) : Subgroup _) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨(φ g : Equiv.Perm (Fin 3850)), mem_inf.mpr ⟨(φ g).2, ?_⟩⟩
        invFun := fun p => ⟨φ.symm ⟨p, (mem_inf.mp p.2).1⟩, ?_⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun p => Subtype.ext (by simp) }
    · have h := mem_centralizer_singleton_iff.mp g.2
      rw [mem_centralizer_singleton_iff, hτ, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
        ← map_mul, h]
    · have h := mem_centralizer_singleton_iff.mp (mem_inf.mp p.2).2
      rw [mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext h
  obtain ⟨-, -, h1, h2, hcov⟩ := hs_reps
  obtain ⟨r, hr, g, hg, hτg⟩ := hcov τ hτP hτ2
  rw [hc, hτg, card_inf_centralizer_conj hsP hg r]
  rcases hr with rfl | rfl
  · left
    exact h1
  · right
    exact h2

theorem eq_nine_of_card_psl2 {q : ℕ} (hq3 : 3 < q)
    (hdvd : q * (q ^ 2 - 1) / 2 ∣ 7680 ∨ q * (q ^ 2 - 1) / 2 ∣ 2880)
    (h8 : 8 ∣ q * (q ^ 2 - 1) / 2) : q = 9 := by
  have hle : q * (q ^ 2 - 1) / 2 ≤ 7680 := by
    rcases hdvd with h | h
    · exact Nat.le_of_dvd (by norm_num) h
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
  have hq24 : q ≤ 24 := by
    by_contra hlt
    push Not at hlt
    have h25 : 25 ≤ q := hlt
    have h1 : 25 * (25 ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / 2 := by
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul h25
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h25 2) 1
    norm_num at h1
    omega
  interval_cases q <;> first | rfl | (exfalso; revert hdvd h8; decide)

theorem hsQuotA6 : HSQuotA6 := by
  intro X _ _ t L h ⟨e⟩
  have hC := card_centralizer_of_HS e h.orderOf_eq
  have hLC : Nat.card (L ⧸ pPrimeCore 2 L) ∣ Nat.card (centralizer ({t} : Set X)) :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.le_centralizer)
  have h8 := h.eight_dvd_card
  rcases h.type with hf | ⟨K, _, _, hodd, h3, hf⟩
  · exfalso
    obtain ⟨f⟩ := hf
    have hA : Nat.card (L ⧸ pPrimeCore 2 L) = 2520 := by
      rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    rw [hA] at hLC
    rcases hC with hc | hc <;> rw [hc] at hLC <;> norm_num at hLC
  · obtain ⟨f⟩ := hf
    have hcard : Nat.card (L ⧸ pPrimeCore 2 L) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
      rw [Nat.card_congr f.toEquiv, psl2_card_formula K hodd]
    have h9 : Nat.card K = 9 := by
      refine eq_nine_of_card_psl2 h3 ?_ (hcard ▸ h8)
      rw [← hcard]
      rcases hC with hc | hc
      · exact Or.inl (hc ▸ hLC)
      · exact Or.inr (hc ▸ hLC)
    let _ := Fintype.ofFinite K
    obtain ⟨g⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism K
      (by rw [← Nat.card_eq_fintype_card, h9])
    exact ⟨f.trans g⟩

end CFSG.ComponentClassification.HSFLit
