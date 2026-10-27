module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.PhiD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeMem

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7_cycle_d_mem {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (φ : ↥(Gxy a x) ≃* Sym 7) {τ : Sym 7} (hτ : τ.IsSwap) :
    ((φ.symm τ : ↥(Gxy a x)) : G) ∈ orb2A a a ∩ orb2A a x := by
  rw [s7_phi_D H hx φ (φ.symm τ)]
  simpa only [MulEquiv.apply_symm_apply] using (Equiv.Perm.isSwap_iff_cycleType.mp hτ)

private theorem s7_cycle_symm_coe_ne {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7) {τ τ' : Sym 7}
    (h : τ ≠ τ') :
    ((φ.symm τ : ↥(Gxy a x)) : G) ≠ ((φ.symm τ' : ↥(Gxy a x)) : G) := by
  intro hc
  apply h
  have h' : (φ.symm τ : ↥(Gxy a x)) = φ.symm τ' := Subtype.ext hc
  calc τ = φ (φ.symm τ) := (MulEquiv.apply_symm_apply φ τ).symm
    _ = φ (φ.symm τ') := by rw [h']
    _ = τ' := MulEquiv.apply_symm_apply φ τ'

private theorem s7_cycle_symm_coe_mul_comm {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7)
    {τ τ' : Sym 7} (h : τ * τ' = τ' * τ) :
    ((φ.symm τ : ↥(Gxy a x)) : G) * ((φ.symm τ' : ↥(Gxy a x)) : G) =
    ((φ.symm τ' : ↥(Gxy a x)) : G) * ((φ.symm τ : ↥(Gxy a x)) : G) := by
  have hsub : φ.symm τ * φ.symm τ' = φ.symm τ' * φ.symm τ := by
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, h]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hsub]

private theorem s7_cycle_symm_coe_ne_mul {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7)
    {τ τ' τ'' : Sym 7} (h : τ'' ≠ τ * τ') :
    ((φ.symm τ'' : ↥(Gxy a x)) : G) ≠
      ((φ.symm τ : ↥(Gxy a x)) : G) * ((φ.symm τ' : ↥(Gxy a x)) : G) := by
  intro hc
  apply h
  have h' : (φ.symm τ'' : ↥(Gxy a x)) = φ.symm τ * φ.symm τ' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hc
  calc τ'' = φ (φ.symm τ'') := (MulEquiv.apply_symm_apply φ τ'').symm
    _ = φ (φ.symm τ * φ.symm τ') := by rw [h']
    _ = τ * τ' := by simp only [map_mul, MulEquiv.apply_symm_apply]

private theorem s7_cycle_symm_coe_mul_eq {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7)
    {t : ↥(Gxy a x)} {τ τ' : Sym 7} (h : φ t = τ * τ') :
    (t : G) = ((φ.symm τ : ↥(Gxy a x)) : G) * ((φ.symm τ' : ↥(Gxy a x)) : G) := by
  have ht : t = φ.symm τ * φ.symm τ' := by
    apply φ.injective
    simp only [h, map_mul, MulEquiv.apply_symm_apply]
  rw [ht, Subgroup.coe_mul]

private theorem s7_cycle_symm_coe_mul3_eq {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7)
    {t : ↥(Gxy a x)} {τ τ' τ'' : Sym 7} (h : φ t = τ * τ' * τ'') :
    (t : G) = ((φ.symm τ : ↥(Gxy a x)) : G) * ((φ.symm τ' : ↥(Gxy a x)) : G) *
      ((φ.symm τ'' : ↥(Gxy a x)) : G) := by
  have ht : t = φ.symm τ * φ.symm τ' * φ.symm τ'' := by
    apply φ.injective
    simp only [h, map_mul, MulEquiv.apply_symm_apply]
  rw [ht, Subgroup.coe_mul, Subgroup.coe_mul]

theorem s7_classes_cycle {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (φ : ↥(Gxy a x) ≃* Sym 7) (t : ↥(Gxy a x)) (ht : orderOf (t : G) = 2) :
    ((t : G) ∈ orb2A a a ∩ orb2A a x ∧ (φ t).cycleType = {2}) ∨
    ((t : G) ∈ orb2B a z a ∩ orb2B a z x ∧ (φ t).cycleType = {2, 2}) ∨
    ((t : G) ∈ orb2BB a z a ∩ orb2BB a z x ∧ (φ t).cycleType = {2, 2, 2}) := by
  have ht2G : (t : G) ^ 2 = 1 := by
    simpa only [ht] using pow_orderOf_eq_one (t : G)
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using ht2G
  have ht_ne_one : t ≠ 1 := by
    intro h
    have h1 : (t : G) = 1 := by rw [h]; simp only [Subgroup.coe_one]
    rw [h1, orderOf_one] at ht
    omega
  have hσ2 : (φ t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hσ1 : φ t ≠ 1 := fun h => ht_ne_one ((MulEquiv.map_eq_one_iff φ).mp h)
  rcases s7_sym7_involution (φ t) hσ2 hσ1 with
      hcyc | ⟨hcyc, τ₁, τ₂, hτ₁, hτ₂, hne12, hcomm12, hσeq⟩
    | ⟨hcyc, τ₁, τ₂, τ₃, hτ₁, hτ₂, hτ₃, hne12, hne31, hne32, h3, c12, c13, c23, hσeq⟩
  · exact Or.inl ⟨(s7_phi_D H hx φ t).mpr hcyc, hcyc⟩
  · refine Or.inr (Or.inl ⟨?_, hcyc⟩)
    rw [s7_cycle_symm_coe_mul_eq φ hσeq]
    exact s7_DD_mem H hx (s7_cycle_d_mem H hx φ hτ₁) (s7_cycle_d_mem H hx φ hτ₂)
      (s7_cycle_symm_coe_ne φ hne12) (s7_cycle_symm_coe_mul_comm φ hcomm12)
  · refine Or.inr (Or.inr ⟨?_, hcyc⟩)
    rw [s7_cycle_symm_coe_mul3_eq φ hσeq]
    exact s7_DDD_mem H hx (s7_cycle_d_mem H hx φ hτ₁) (s7_cycle_d_mem H hx φ hτ₂)
      (s7_cycle_d_mem H hx φ hτ₃) (s7_cycle_symm_coe_ne φ hne12)
      (s7_cycle_symm_coe_ne φ hne31) (s7_cycle_symm_coe_ne φ hne32)
      (s7_cycle_symm_coe_ne_mul φ h3) (s7_cycle_symm_coe_mul_comm φ c12)
      (s7_cycle_symm_coe_mul_comm φ c13) (s7_cycle_symm_coe_mul_comm φ c23)

theorem s7_E2_nonempty [Finite G] {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a) :
    (orb2B a z a ∩ orb2B a z x).Nonempty := by
  obtain ⟨φ⟩ := s7_shape H hx
  obtain ⟨τ₁, τ₂, τ₃, hτ₁, hτ₂, _, hne12, _, _, _, c12, _, _⟩ := s7_sym7_swaps
  refine ⟨((φ.symm τ₁ : ↥(Gxy a x)) : G) * ((φ.symm τ₂ : ↥(Gxy a x)) : G), ?_⟩
  exact s7_DD_mem H hx (s7_cycle_d_mem H hx φ hτ₁) (s7_cycle_d_mem H hx φ hτ₂)
    (s7_cycle_symm_coe_ne φ hne12) (s7_cycle_symm_coe_mul_comm φ c12)

theorem s7_E3_nonempty [Finite G] {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a) :
    (orb2BB a z a ∩ orb2BB a z x).Nonempty := by
  obtain ⟨φ⟩ := s7_shape H hx
  obtain ⟨τ₁, τ₂, τ₃, hτ₁, hτ₂, hτ₃, hne12, hne31, hne32, h3, c12, c13, c23⟩ :=
    s7_sym7_swaps
  refine ⟨((φ.symm τ₁ : ↥(Gxy a x)) : G) * ((φ.symm τ₂ : ↥(Gxy a x)) : G) *
      ((φ.symm τ₃ : ↥(Gxy a x)) : G), ?_⟩
  exact s7_DDD_mem H hx (s7_cycle_d_mem H hx φ hτ₁) (s7_cycle_d_mem H hx φ hτ₂)
    (s7_cycle_d_mem H hx φ hτ₃) (s7_cycle_symm_coe_ne φ hne12)
    (s7_cycle_symm_coe_ne φ hne31) (s7_cycle_symm_coe_ne φ hne32)
    (s7_cycle_symm_coe_ne_mul φ h3) (s7_cycle_symm_coe_mul_comm φ c12)
    (s7_cycle_symm_coe_mul_comm φ c13) (s7_cycle_symm_coe_mul_comm φ c23)

end CFSG.EvenSporadicStandard.HNRecog.Section3
