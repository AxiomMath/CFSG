module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorCount
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PField

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

theorem map_eq_of_forall_mem {G : Type*} [Group G] [Finite G] (S : Subgroup G) (α : MulAut G)
    (h : ∀ y ∈ S, α y ∈ S) : S.map α.toMonoidHom = S :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (by rw [Subgroup.card_map_of_injective α.injective])

theorem d3A4Borel_holds : D3A4Borel := by
  intro K _ _ n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 ht₁₂c ht₁1 ht₂1 ht₁₂ hbt₁ hbt₂ A hA hAbig hfb hf1 hf2 S
    hAS hSb hSt
  classical
  haveI := charP_three_of_card hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 1 ≤ n := one_le_of_card_field hK
  let φ : D4Model K ≃* ↥(adjointGroup Tag.D4 K) :=
    (coordinatePlusWitnessEquiv K (isoAdj K).symm).symm
  have hb3' : b * b * b = 1 := by rw [← pow_three']; exact hb3
  have ht₁2' : t₁ * t₁ = 1 := by rw [← pow_two]; exact ht₁2
  have ht₂2' : t₂ * t₂ = 1 := by rw [← pow_two]; exact ht₂2
  have hbt3 : (t₁ * b) ^ 3 = 1 := by
    rw [pow_three']
    have e1 : t₁ * b * (t₁ * b) * (t₁ * b) = t₁ * (b * t₁) * b * t₁ * b := by group
    rw [e1, hbt₁]
    have e2 : t₁ * (t₂ * b) * b * t₁ * b = t₁ * t₂ * b * (b * t₁) * b := by group
    rw [e2, hbt₁]
    have e3 : t₁ * t₂ * b * (t₂ * b) * b = t₁ * t₂ * (b * t₂) * b * b := by group
    rw [e3, hbt₂]
    have e4 : t₁ * t₂ * (t₁ * t₂ * b) * b * b = t₁ * t₂ * t₁ * t₂ * (b * b * b) := by group
    rw [e4, hb3', mul_one]
    have e5 : t₁ * t₂ * t₁ * t₂ = t₁ * (t₂ * t₁) * t₂ := by group
    rw [e5, ← ht₁₂c]
    have e6 : t₁ * (t₁ * t₂) * t₂ = (t₁ * t₁) * (t₂ * t₂) := by group
    rw [e6, ht₁2', ht₂2', mul_one]
  have hb_ni : b ∉ Inn (D4Model K) := fun h => hbQ (inner_le_D4Img h)
  have hni : ∀ γ : MulAut (D4Model K), γ ∉ Inn (D4Model K) →
      MulAut.congr φ γ ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    intro γ hγ h
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at h
    obtain ⟨t, ht, hte⟩ := h
    have : t = γ := (MulAut.congr φ).injective hte
    exact hγ (this ▸ ht)
  set αb : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ b with hαb
  set αt : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.congr φ t₁ with hαt
  have hαb3 : αb ^ 3 = 1 := by rw [hαb, ← map_pow, hb3, map_one]
  have hαt2 : αt * αt = 1 := by rw [hαt, ← map_mul, ht₁2', map_one]
  have hαbt3 : (αt * αb) ^ 3 = 1 := by rw [hαt, hαb, ← map_mul, ← map_pow, hbt3, map_one]
  have hαt1 : αt ≠ 1 := fun h => ht₁1 ((MulAut.congr φ).injective (by rw [← hαt, h, map_one]))
  have hA' := d3f_isElemAbelian_map φ hA
  have hfb' : ∀ a ∈ A.map φ.toMonoidHom, αb a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change αb (φ a) = φ a
    rw [hαb, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfb a ha]
  have hf1' : ∀ a ∈ A.map φ.toMonoidHom, αt a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change αt (φ a) = φ a
    rw [hαt, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hf1 a ha]
  haveI : Finite (D4Model K) := inferInstance
  haveI : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  obtain ⟨S', hS'coe⟩ : ∃ S' : Sylow 3 ↥(adjointGroup Tag.D4 K),
      (S' : Subgroup ↥(adjointGroup Tag.D4 K)) = (S : Subgroup (D4Model K)).map φ.toMonoidHom :=
    ⟨Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective S, Sylow.coe_mapSurjective _ _⟩
  have hS'mem : ∀ y, y ∈ (S' : Subgroup ↥(adjointGroup Tag.D4 K)) ↔
      φ.symm y ∈ (S : Subgroup (D4Model K)) := by
    intro y
    rw [hS'coe]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s ∈ (S : Subgroup (D4Model K)) := hs
      simpa using hs'
    · intro h
      exact ⟨φ.symm y, h, by simp⟩
  have hSαb : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map αb.toMonoidHom = S' := by
    refine map_eq_of_forall_mem _ _ fun y hy => ?_
    rw [hS'mem] at hy ⊢
    have h1 : b (φ.symm y) ∈ (S : Subgroup (D4Model K)) := by
      have := Subgroup.mem_map_of_mem b.toMonoidHom hy
      rwa [hSb] at this
    simpa [hαb, MulAut.congr_apply] using h1
  have hSαt : (S' : Subgroup ↥(adjointGroup Tag.D4 K)).map αt.toMonoidHom = S' := by
    refine map_eq_of_forall_mem _ _ fun y hy => ?_
    rw [hS'mem] at hy ⊢
    have h1 : t₁ (φ.symm y) ∈ (S : Subgroup (D4Model K)) := by
      have := Subgroup.mem_map_of_mem t₁.toMonoidHom hy
      rwa [hSt] at this
    simpa [hαt, MulAut.congr_apply] using h1
  have hAS' : A.map φ.toMonoidHom ≤ (S' : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hS'mem]
    simpa using hAS ha
  obtain ⟨x, hmemS⟩ := exists_conj_to_U S'
  have hUb := stable_of_sylow_conj hmemS hSαb
  have hUt := stable_of_sylow_conj hmemS hSαt
  set α' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * αb * MulAut.conj x with hα'
  set t' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * αt * MulAut.conj x with ht'
  have hα'3 : α' ^ 3 = 1 := by
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := αb) (i := 3)
    rw [inv_inv] at h
    rw [hα', h, hαb3]; group
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = (MulAut.conj x)⁻¹ * (αt * αt) * MulAut.conj x := by rw [ht']; group
      _ = 1 := by rw [hαt2]; group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply hαt1
    have : αt = MulAut.conj x * t' * (MulAut.conj x)⁻¹ := by rw [ht']; group
    rw [this, h]; group
  have hb'3 : (t' * α') ^ 3 = 1 := by
    have e : t' * α' = (MulAut.conj x)⁻¹ * (αt * αb) * MulAut.conj x := by rw [hα', ht']; group
    have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := αt * αb) (i := 3)
    rw [inv_inv] at h
    rw [e, h, hαbt3]; group
  have hbn' : α' ∉ Inn ↥(adjointGroup Tag.D4 K) := not_inner_conj x (hni b hb_ni)
  set A'' : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (A.map φ.toMonoidHom).map (MulAut.conj x)⁻¹.toMonoidHom with hA''
  have hAU : A'' ≤ unitU K := by
    rintro _ ⟨a, ha, rfl⟩
    have := (hmemS a).1 (hAS' ha)
    change (MulAut.conj x)⁻¹ a ∈ unitU K
    rw [MulAut.conj_inv_apply]
    exact this
  have hcomm : ∀ u ∈ A'', ∀ w ∈ A'', u * w = w * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    change (MulAut.conj x)⁻¹ a * (MulAut.conj x)⁻¹ c = (MulAut.conj x)⁻¹ c * (MulAut.conj x)⁻¹ a
    rw [← map_mul, ← map_mul, D3P.comm_of_elemAbelian hA' ha hc]
  have hfixα : ∀ a ∈ A'', α' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    have e : α' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ (αb a) := by
      rw [hα']
      simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]
    change α' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [e, hfb' a ha]
  have hfixt : ∀ a ∈ A'', t' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    have e : t' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ (αt a) := by
      rw [ht']
      simp [MulAut.conj_apply, MulAut.conj_inv_apply, mul_assoc]
    change t' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [e, hf1' a ha]
  have hcard := borel_card_le α' t' hα'3 hbn' ht'2 ht'1 hb'3 hUb hUt A'' hAU hcomm hfixα hfixt
  have hcardA : Nat.card A'' = Nat.card A := by
    rw [hA'', Subgroup.card_map_of_injective (MulAut.conj x)⁻¹.injective,
      Subgroup.card_map_of_injective φ.injective]
  rw [hcardA, hK, ← pow_mul] at hcard
  have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 1) := by
    calc 3 ^ (4 * n) ≤ 3 * Nat.card A := hAbig
      _ ≤ 3 * 3 ^ (2 * n) := Nat.mul_le_mul_left _ (by simpa [mul_comm] using hcard)
      _ = 3 ^ (2 * n + 1) := by rw [pow_succ]; ring
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  omega

theorem d3A4Fixed_of_regular (hR : D3A4Regular) : D3A4Fixed :=
  d3A4Fixed_of_borel_regular d3A4Borel_holds hR

theorem d3FixedPointFree_of_regular (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hR : D3A4Regular) (hN : D3CaseTwoOne) : D3FixedPointFree :=
  d3FixedPointFree_of_fixed hI hF (d3A4Fixed_of_regular hR) hN

end Final

end CFSG.LocalAnalysis.GLTheoremA
