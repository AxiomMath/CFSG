module

public import CFSG.ClassicalInvolution.Q3.Q3MFODSimAt
public import CFSG.ClassicalInvolution.Q3.Q3MFODSim
public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Center
public import CFSG.Sporadic.Ly.Primitive

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Q3.Q3T
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

local notation "Proj₈" => StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))

local notation "𝔉" => statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))

section Desc

theorem d4Proj_surjective : Function.Surjective (d4Proj 𝔽₃) :=
  (spinToStatedProj_quadPlus three_le_four).1

theorem ker_d4Proj : (d4Proj 𝔽₃).ker = Subgroup.center Spin₈ :=
  (spinToStatedProj_quadPlus three_le_four).2.2

noncomputable def descAut (α : MulAut Spin₈) : MulAut Proj₈ :=
  Classical.choose (exists_descend (d4Proj 𝔽₃) d4Proj_surjective ker_d4Proj α)

theorem descAut_apply (α : MulAut Spin₈) (x : Spin₈) :
    descAut α (d4Proj 𝔽₃ x) = d4Proj 𝔽₃ (α x) :=
  Classical.choose_spec (exists_descend (d4Proj 𝔽₃) d4Proj_surjective ker_d4Proj α) x

theorem descAut_mul (α α' : MulAut Spin₈) : descAut (α * α') = descAut α * descAut α' := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := d4Proj_surjective y
  simp only [descAut_apply, MulAut.mul_apply]

theorem descAut_one : descAut (1 : MulAut Spin₈) = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := d4Proj_surjective y
  rw [descAut_apply]
  rfl

theorem descAut_inv (α : MulAut Spin₈) : descAut α⁻¹ = (descAut α)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← descAut_mul, inv_mul_cancel, descAut_one]

@[expose] def Pres (α : MulAut Spin₈) : Prop := descAut α • 𝔉 = 𝔉

theorem pres_of_eq (τ τ' : MulAut Spin₈) (h : descAut τ • 𝔉 = descAut τ' • 𝔉) :
    Pres (τ'⁻¹ * τ) := by
  unfold Pres
  rw [descAut_mul, descAut_inv, mul_smul, h, inv_smul_smul]

end Desc

section Combinatorics

theorem not_four_distinct {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card ≤ 3) {w x y z : α}
    (hw : w ∈ s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hwx : w ≠ x) (hwy : w ≠ y)
    (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have h4 : ({w, x, y, z} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
      Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
  have hsub : ({w, x, y, z} : Finset α) ⊆ s := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  omega

theorem exists_fixed_of_involutive {α : Type*} (π : α → α) (hπ : ∀ x, π (π x) = x) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcl : ∀ x, (x = a ∨ x = b ∨ x = c) → (π x = a ∨ π x = b ∨ π x = c)) :
    π a = a ∨ π b = b ∨ π c = c := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  rcases hcl a (Or.inl rfl) with h1 | h1 | h1
  · exact ha h1
  · rcases hcl c (Or.inr (Or.inr rfl)) with h2 | h2 | h2
    · have e := hπ c
      rw [h2, h1] at e
      exact hbc e
    · have e1 := hπ c
      have e2 := hπ a
      rw [h2] at e1
      rw [h1] at e2
      exact hac (e2.symm.trans e1)
    · exact hc h2
  · have hca : π c = a := by
      have e := hπ a
      rw [h1] at e
      exact e
    rcases hcl b (Or.inr (Or.inl rfl)) with h2 | h2 | h2
    · have e := hπ b
      rw [h2, h1] at e
      exact hbc e.symm
    · exact hb h2
    · have e := hπ b
      rw [h2, hca] at e
      exact hab e

end Combinatorics

section Involutions


theorem neg_ne_one₃ :
    (LinearEquiv.neg 𝔽₃ : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ≠ 1 := by
  intro h
  have h' := congrFun (LinearEquiv.congr_fun h (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)
  exact neg_one_ne_one_of_card_three ModelFacts.TG3.natCard_galoisField_three (by simpa using h')

theorem exists_triality_data : ∃ ρ : MulAut Spin₈, PreservesFund 3 1 ρ.symm ∧
    ρ (z2 𝔽₃ * z3 𝔽₃) = z3 𝔽₃ * z0 𝔽₃ ∧ ρ (z3 𝔽₃ * z0 𝔽₃) = z0 𝔽₃ * z2 𝔽₃ ∧
    ρ (z0 𝔽₃ * z2 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.TG3.two_ne_zero_three
  obtain ⟨ρ, hρ⟩ := ModelFacts.TG3.exists_triality3 hadm
  have e0 : ρ (z0 𝔽₃) = z2 𝔽₃ := triality_z0 h2 ρ hρ
  have e2 : ρ (z2 𝔽₃) = z3 𝔽₃ := triality_z2 h2 ρ hρ
  have e3 : ρ (z3 𝔽₃) = z0 𝔽₃ := triality_z3 h2 ρ hρ
  have hF : PreservesFund 3 1 ρ.symm :=
    preservesFund_of_nodes hadm ρ.symm triEquiv.symm (symm_nodes ρ triEquiv hρ)
  refine ⟨ρ, hF, ?_, ?_, ?_⟩
  · rw [map_mul, e2, e3]
  · rw [map_mul, e3, e0]
  · rw [map_mul, e0, e2]

end Involutions

section Pres

theorem pres_fix_b (hb1 : z2 𝔽₃ * z3 𝔽₃ ≠ 1) (τ : MulAut Spin₈) (h : Pres τ) :
    τ (z2 𝔽₃ * z3 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ := by
  have : Group.IsPerfect Spin₈ := isPerfect_spinGroup_quadPlus three_le_four
  obtain ⟨A, φ, μ, -, hA⟩ := spin_plus4_sim_of_family τ (descAut τ) (descAut_apply τ) h
  have hb : (z2 𝔽₃ * z3 𝔽₃ : Spin₈) ∈ (spinMatrix (quadPlus 4 𝔽₃)).ker :=
    (mem_ker_spinMatrix_quadPlus_iff _).mpr (Or.inr coe_z2_mul_z3)
  have hb' : spinMatrix (quadPlus 4 𝔽₃) (z2 𝔽₃ * z3 𝔽₃) = 1 := hb
  have h1 : spinMatrix (quadPlus 4 𝔽₃) (τ (z2 𝔽₃ * z3 𝔽₃)) = 1 := by
    rw [hA, hb', map_one, mul_one, mul_inv_cancel]
  have hmem : τ (z2 𝔽₃ * z3 𝔽₃) ∈ (spinMatrix (quadPlus 4 𝔽₃)).ker := h1
  rcases (mem_ker_spinMatrix_quadPlus_iff _).mp hmem with h2 | h2
  · exact absurd (τ.injective (h2.trans (map_one τ).symm)) hb1
  · exact Subtype.ext (h2.trans coe_z2_mul_z3.symm)

theorem smul_ne_of_apply_ne (hb1 : z2 𝔽₃ * z3 𝔽₃ ≠ 1) (τ τ' : MulAut Spin₈)
    (h : τ (z2 𝔽₃ * z3 𝔽₃) ≠ τ' (z2 𝔽₃ * z3 𝔽₃)) : descAut τ • 𝔉 ≠ descAut τ' • 𝔉 := by
  intro heq
  have hp := pres_fix_b hb1 _ (pres_of_eq τ τ' heq)
  rw [MulAut.mul_apply] at hp
  apply h
  have := congrArg τ' hp
  rw [MulAut.apply_inv_self] at this
  exact this

end Pres

section Orbit


theorem b_ne_one : z2 𝔽₃ * z3 𝔽₃ ≠ 1 := by
  obtain ⟨ρ, -, -, -, h3⟩ := exists_triality_data
  intro h
  have h1 : z0 𝔽₃ * z2 𝔽₃ = 1 := ρ.injective (by rw [h3, h, map_one])
  have h' := spinAction_z0_mul_z2 (F := 𝔽₃)
  rw [h1, map_one] at h'
  exact neg_ne_one₃ h'.symm

theorem pres_conj_of_fix (α τ : MulAut Spin₈)
    (h : descAut α • (descAut τ • 𝔉) = descAut τ • 𝔉) : Pres (τ⁻¹ * α * τ) := by
  unfold Pres
  rw [descAut_mul, descAut_mul, descAut_inv, mul_smul, mul_smul, h, inv_smul_smul]

theorem exists_pres_conj (α : MulAut Spin₈) (hα2 : α * α = 1) :
    ∃ σ : MulAut Spin₈, PreservesFund 3 1 σ ∧ Pres (σ * α * σ⁻¹) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ρ, hF, h1, h2, h3⟩ := exists_triality_data
  have hb1 := b_ne_one
  have hθb : spinAction (quadPlus 4 𝔽₃) (z2 𝔽₃ * z3 𝔽₃) = 1 := spinAction_z2_mul_z3
  have hθb₁ : spinAction (quadPlus 4 𝔽₃) (z3 𝔽₃ * z0 𝔽₃) = LinearEquiv.neg 𝔽₃ :=
    spinAction_z3_mul_z0
  have hθb₂ : spinAction (quadPlus 4 𝔽₃) (z0 𝔽₃ * z2 𝔽₃) = LinearEquiv.neg 𝔽₃ :=
    spinAction_z0_mul_z2
  have hbb₁ : z2 𝔽₃ * z3 𝔽₃ ≠ z3 𝔽₃ * z0 𝔽₃ := fun h =>
    neg_ne_one₃ (by rw [← hθb₁, ← h, hθb])
  have hbb₂ : z2 𝔽₃ * z3 𝔽₃ ≠ z0 𝔽₃ * z2 𝔽₃ := fun h =>
    neg_ne_one₃ (by rw [← hθb₂, ← h, hθb])
  have hb₁b₂ : z3 𝔽₃ * z0 𝔽₃ ≠ z0 𝔽₃ * z2 𝔽₃ := fun h =>
    hbb₁ (ρ.injective (h1.trans (h.trans h2.symm)))
  let τ : Fin 3 → MulAut Spin₈ := ![1, ρ, ρ * ρ]
  have hτ0 : τ 0 (z2 𝔽₃ * z3 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ := rfl
  have hτ1 : τ 1 (z2 𝔽₃ * z3 𝔽₃) = z3 𝔽₃ * z0 𝔽₃ := h1
  have hτ2 : τ 2 (z2 𝔽₃ * z3 𝔽₃) = z0 𝔽₃ * z2 𝔽₃ := by
    show ρ (ρ (z2 𝔽₃ * z3 𝔽₃)) = _
    rw [h1, h2]
  set G : Fin 3 → Set (Subgroup Proj₈) := fun i => descAut (τ i) • 𝔉 with hG
  have hG01 : G 0 ≠ G 1 := smul_ne_of_apply_ne hb1 _ _ (by rw [hτ0, hτ1]; exact hbb₁)
  have hG02 : G 0 ≠ G 2 := smul_ne_of_apply_ne hb1 _ _ (by rw [hτ0, hτ2]; exact hbb₂)
  have hG12 : G 1 ≠ G 2 := smul_ne_of_apply_ne hb1 _ _ (by rw [hτ1, hτ2]; exact hb₁b₂)
  obtain ⟨C₁, C₂, hΦ⟩ : ∃ C₁ C₂ : Set (Subgroup Proj₈), ∀ Y ∈ MulAction.orbit (MulAut Proj₈) 𝔉,
      Y = 𝔉 ∨ Y = C₁ ∨ Y = C₂ :=
    ⟨_, _, fun Y hY => by
      simpa using stated_pointFamily_orbit_subset (K := 𝔽₃) (n := 4) rfl hY⟩
  have hGorb : ∀ i, G i ∈ MulAction.orbit (MulAut Proj₈) 𝔉 := fun i =>
    MulAction.mem_orbit _ _
  have hπ : ∀ X : Set (Subgroup Proj₈), descAut α • (descAut α • X) = X := by
    intro X
    rw [← mul_smul, ← descAut_mul, hα2, descAut_one, one_smul]
  have hcl : ∀ i : Fin 3, descAut α • G i = G 0 ∨ descAut α • G i = G 1 ∨
      descAut α • G i = G 2 := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1, c2⟩ := hcon
    have hy : descAut α • G i ∈ MulAction.orbit (MulAut Proj₈) 𝔉 :=
      ⟨descAut α * descAut (τ i), by
        show (descAut α * descAut (τ i)) • 𝔉 = descAut α • G i
        rw [mul_smul]⟩
    exact not_four_distinct ({𝔉, C₁, C₂} : Finset (Set (Subgroup Proj₈)))
      Finset.card_le_three (by simpa using hΦ _ hy) (by simpa using hΦ _ (hGorb 0))
      (by simpa using hΦ _ (hGorb 1)) (by simpa using hΦ _ (hGorb 2)) c0 c1 c2 hG01 hG02 hG12
  have hfix := exists_fixed_of_involutive (fun X => descAut α • X) hπ hG01 hG02 hG12
    (fun x hx => by
      rcases hx with rfl | rfl | rfl
      · exact hcl 0
      · exact hcl 1
      · exact hcl 2)
  rcases hfix with h | h | h
  · refine ⟨1, PreservesFund.refl, ?_⟩
    have h' : descAut α • (descAut (1 : MulAut Spin₈) • 𝔉) = descAut (1 : MulAut Spin₈) • 𝔉 := h
    have := pres_conj_of_fix α 1 h'
    simpa using this
  · refine ⟨ρ⁻¹, hF, ?_⟩
    have h' : descAut α • (descAut ρ • 𝔉) = descAut ρ • 𝔉 := h
    have := pres_conj_of_fix α ρ h'
    rwa [inv_inv]
  · refine ⟨(ρ * ρ)⁻¹, ?_, ?_⟩
    · have e : (ρ * ρ)⁻¹ = ρ.symm.trans ρ.symm := rfl
      rw [e]
      exact hF.comp hF
    · have h' : descAut α • (descAut (ρ * ρ) • 𝔉) = descAut (ρ * ρ) • 𝔉 := h
      have := pres_conj_of_fix α (ρ * ρ) h'
      rwa [inv_inv]

end Orbit

end CFSG.ClassicalInvolution.Q3.Q3MFOD
