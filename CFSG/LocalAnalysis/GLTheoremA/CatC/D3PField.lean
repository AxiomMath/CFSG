module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PLayer2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PCases
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FTriality

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]

section Final

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

open CFSG.Open CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.HardMathSupport.Timmesfeld.DFour
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem d3FieldPair_holds : D3FieldPair := by
  intro K _ _ n hK y b hy3 hb3 hyb hyQ hyI hbQ A hA hfy hfb
  classical
  haveI := charP_three_of_card hK
  let φ : D4Model K ≃* ↥(adjointGroup Tag.D4 K) :=
    (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm
  have hb3' : b * b * b = 1 := by rw [← pow_three']; exact hb3
  have hb_ni : b ∉ Inn (D4Model K) := fun h => hbQ (inner_le_D4Img h)
  have hyb_ni : y * b ∉ Inn (D4Model K) := fun h => hbQ (by
    have : b = y⁻¹ * (y * b) := by group
    rw [this]
    exact (D4Img K).mul_mem ((D4Img K).inv_mem hyQ) (inner_le_D4Img h))
  have hybb_ni : y * b * b ∉ Inn (D4Model K) := fun h => hbQ (by
    have h2 : b * b ∈ D4Img K := by
      have : b * b = y⁻¹ * (y * b * b) := by group
      rw [this]
      exact (D4Img K).mul_mem ((D4Img K).inv_mem hyQ) (inner_le_D4Img h)
    have h3 : (b * b)⁻¹ = b := inv_eq_of_mul_eq_one_right hb3'
    rw [← h3]
    exact (D4Img K).inv_mem h2)
  have hni : ∀ γ : MulAut (D4Model K), γ ∉ Inn (D4Model K) →
      MulAut.congr φ γ ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    intro γ hγ h
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at h
    obtain ⟨t, ht, hte⟩ := h
    have : t = γ := (MulAut.congr φ).injective hte
    exact hγ (this ▸ ht)
  set αy : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ y with hαy
  set αb : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ b with hαb
  have hαy3 : αy ^ 3 = 1 := by rw [hαy, ← map_pow, hy3, map_one]
  have hαb3 : αb ^ 3 = 1 := by rw [hαb, ← map_pow, hb3, map_one]
  have hαyb : αy * αb = αb * αy := by rw [hαy, hαb, ← map_mul, ← map_mul, hyb]
  have hA' := d3f_isElemAbelian_map φ hA
  have hfy' : ∀ a ∈ A.map φ.toMonoidHom, αy a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change αy (φ a) = φ a
    rw [hαy, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfy a ha]
  have hfb' : ∀ a ∈ A.map φ.toMonoidHom, αb a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change αb (φ a) = φ a
    rw [hαb, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfb a ha]
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨S, hAS, hSy, hSb⟩ := D3P.exists_stable_sylow_fixing_pair αy αb hαy3 hαb3 hαyb _ hA' hfy' hfb'
  obtain ⟨x, hmemS⟩ := exists_conj_to_U S
  have hUy := stable_of_sylow_conj hmemS hSy
  have hUb := stable_of_sylow_conj hmemS hSb
  set y' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * αy * MulAut.conj x with hy'
  set b' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * αb * MulAut.conj x with hb'
  have hy'3 : y' ^ 3 = 1 := by
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := αy) (i := 3)
    rw [inv_inv] at h
    rw [hy', h, hαy3]; group
  have hb'3 : b' ^ 3 = 1 := by
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := αb) (i := 3)
    rw [inv_inv] at h
    rw [hb', h, hαb3]; group
  have hyb' : y' * b' = b' * y' := by
    have : y' * b' = (MulAut.conj x)⁻¹ * (αy * αb) * MulAut.conj x := by rw [hy', hb']; group
    have h2 : b' * y' = (MulAut.conj x)⁻¹ * (αb * αy) * MulAut.conj x := by rw [hy', hb']; group
    rw [this, h2, hαyb]
  have hyn' : y' ∉ Inn ↥(adjointGroup Tag.D4 K) := not_inner_conj x (hni y hyI)
  have hbn' : b' ∉ Inn ↥(adjointGroup Tag.D4 K) := not_inner_conj x (hni b hb_ni)
  have hybn' : y' * b' ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    have : y' * b' = (MulAut.conj x)⁻¹ * (αy * αb) * MulAut.conj x := by rw [hy', hb']; group
    rw [this]
    refine not_inner_conj x ?_
    have := hni (y * b) hyb_ni
    rwa [map_mul] at this
  have hybbn' : y' * b' * b' ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    have : y' * b' * b' = (MulAut.conj x)⁻¹ * (αy * αb * αb) * MulAut.conj x := by
      rw [hy', hb']; group
    rw [this]
    refine not_inner_conj x ?_
    have := hni (y * b * b) hybb_ni
    rwa [map_mul, map_mul] at this
  set A'' : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (A.map φ.toMonoidHom).map (MulAut.conj x)⁻¹.toMonoidHom with hA''
  have hAU : A'' ≤ unitU K := by
    rintro _ ⟨a, ha, rfl⟩
    have := (hmemS a).1 (hAS ha)
    change (MulAut.conj x)⁻¹ a ∈ unitU K
    rw [MulAut.conj_inv_apply]
    exact this
  have hA0 : A'' ≤ unitN Tag.D4 K 0 := fun u hu =>
    unitN_zero_of_mem_pos (Subgroup.mem_subgroupOf.1 (hAU hu))
  have hfixy : ∀ a ∈ A'', y' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    have e : y' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ (αy a) := by
      rw [hy']
      simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]
    change y' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [e, hfy' a ha]
  have hfixb : ∀ a ∈ A'', b' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    have e : b' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ (αb a) := by
      rw [hb']
      simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]
    change b' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [e, hfb' a ha]
  have hcard := fieldpair_stable hy'3 hb'3 hyb' hUy hUb hyn' hbn' hybn' hybbn' hA0 hfixy hfixb
  have hcardA : Nat.card A'' = Nat.card A := by
    rw [hA'', Subgroup.card_map_of_injective (MulAut.conj x)⁻¹.injective,
      Subgroup.card_map_of_injective φ.injective]
  rw [hcardA] at hcard
  have h2 : Nat.card A ^ 3 ≤ (3 ^ (2 * n)) ^ 3 := by
    calc Nat.card A ^ 3 ≤ Nat.card K ^ 6 := hcard
      _ = (3 ^ (2 * n)) ^ 3 := by rw [hK, ← pow_mul, ← pow_mul]; ring_nf
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2

theorem d3FixedPointFree_of_fixed (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hA4 : D3A4Fixed) (hN : D3CaseTwoOne) : D3FixedPointFree :=
  d3FixedPointFree_of_cases hI hF d3FieldPair_holds hA4 hN

end Final

end CFSG.LocalAnalysis.GLTheoremA
