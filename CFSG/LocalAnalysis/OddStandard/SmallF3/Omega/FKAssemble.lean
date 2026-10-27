module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMultNegOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKDet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKCoset
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFam
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMult
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKTri
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSim
public import CFSG.ClassicalInvolution.Q3.TL4D4NCOneP

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TL4 (sim_cases4 finrank_d4)
open CFSG.ClassicalInvolution.G2D4Models.Twin (z0 z2 z3)
open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (ne01 ne23)
open CFSG.LieType.Universal.Spin (spinAction quadPlus map_spinAction range_spinAction_quadPlus
  nondegenerate_polarBilin_quadPlus)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

private theorem fk_map_conj {G : Type*} [Group G] (τ κ : MulAut G) {ℓ ℓ' : Subgroup G}
    (hτ : ℓ.map τ.toMonoidHom = ℓ') (hκ : ℓ'.map κ.toMonoidHom = ℓ') :
    ℓ.map (τ⁻¹ * κ * τ).toMonoidHom = ℓ := by
  have h1 : (τ⁻¹ * κ * τ).toMonoidHom =
      τ⁻¹.toMonoidHom.comp (κ.toMonoidHom.comp τ.toMonoidHom) := rfl
  have h2 : τ⁻¹.toMonoidHom.comp τ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h1, ← Subgroup.map_map, ← Subgroup.map_map, hτ, hκ, ← hτ, Subgroup.map_map, h2,
    Subgroup.map_id]

private theorem fk_finish {α κ τ : MulAut Spin₈} {y : Spin₈} (hα2 : α * α = 1)
    (hακ : ∀ x, α x = κ (y * x * y⁻¹)) (hp : Q3MFOD.Pres (τ⁻¹ * α * τ))
    (A : V₈ ≃ₗ[𝔽₃] V₈) (hA : ∀ v, Q₄ (A v) = Q₄ v)
    (hκA : ∀ x, spinAction Q₄ ((τ⁻¹ * κ * τ) x) = A * spinAction Q₄ x * A⁻¹) :
    ∃ σ : MulAut Spin₈, Q3MFOD.Pres (σ * α * σ⁻¹) ∧
      ∃ (a' : V₈ ≃ₗ[𝔽₃] V₈) (s' : 𝔽₃), (∀ v, Q₄ (a' v) = Q₄ v) ∧ (∀ v, a' (a' v) = s' • v) ∧
        ∀ x, spinAction Q₄ ((σ * α * σ⁻¹) x) = a' * spinAction Q₄ x * a'⁻¹ := by
  refine ⟨τ⁻¹, by rwa [inv_inv], ?_⟩
  set a' : V₈ ≃ₗ[𝔽₃] V₈ := A * spinAction Q₄ (τ⁻¹ y) with ha'
  have hact : ∀ x, spinAction Q₄ ((τ⁻¹ * α * τ⁻¹⁻¹) x) = a' * spinAction Q₄ x * a'⁻¹ := by
    intro x
    have e1 : (τ⁻¹ * α * τ⁻¹⁻¹) x = (τ⁻¹ * κ * τ) (τ⁻¹ y * x * (τ⁻¹ y)⁻¹) := by
      simp only [inv_inv, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self,
        MulAut.inv_apply_self, hακ]
    rw [e1, hκA, ha']
    simp only [map_mul, map_inv]
    group
  have hQ' : ∀ v, Q₄ (a' v) = Q₄ v := fun v => by
    show Q₄ (A (spinAction Q₄ (τ⁻¹ y) v)) = _
    rw [hA, map_spinAction]
  refine ⟨a', ?_⟩
  have hα'2 : (τ⁻¹ * α * τ⁻¹⁻¹) * (τ⁻¹ * α * τ⁻¹⁻¹) = 1 := by
    calc (τ⁻¹ * α * τ⁻¹⁻¹) * (τ⁻¹ * α * τ⁻¹⁻¹) = τ⁻¹ * (α * α) * τ⁻¹⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have hcomm : ∀ h ∈ elementaryGroup Q₄, a' * a' * h = h * (a' * a') := by
    intro h hh
    rw [← range_spinAction_quadPlus (K := 𝔽₃) (by norm_num : 3 ≤ 4)] at hh
    obtain ⟨x, rfl⟩ := hh
    have h1 : spinAction Q₄ ((τ⁻¹ * α * τ⁻¹⁻¹) ((τ⁻¹ * α * τ⁻¹⁻¹) x)) = spinAction Q₄ x := by
      rw [← MulAut.mul_apply, hα'2, MulAut.one_apply]
    rw [hact, hact] at h1
    calc a' * a' * spinAction Q₄ x
        = (a' * (a' * spinAction Q₄ x * a'⁻¹) * a'⁻¹) * (a' * a') := by group
      _ = spinAction Q₄ x * (a' * a') := by rw [h1]
  obtain ⟨-, ha2⟩ := sim_cases4 ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
    (nondegenerate_polarBilin_quadPlus 4 𝔽₃) (by rw [finrank_d4]; norm_num) (μ := 1) one_ne_zero
    (fun v => by rw [hQ' v, one_mul]) hcomm
  rcases ha2 with ha2 | ha2
  · exact ⟨1, hQ', fun v => by rw [one_smul]; exact LinearEquiv.congr_fun ha2 v, hact⟩
  · exact ⟨-1, hQ', fun v => by rw [ha2, neg_one_smul], hact⟩

private theorem fk_prop_xor {p q r : Prop} (h1 : ¬(p ↔ q)) (h2 : ¬(q ↔ r)) : (r ↔ p) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp_all

theorem fkMultNegOne_holds : FKMultNegOne := by
  intro α hα2 _ a s hQ ha2 hαa
  obtain ⟨d, y, hd, hay⟩ := fk_coset a hQ (fk_det_eq_one a s hQ ha2)
  have hdμ : ∀ m : Fin 4, (d (.inl m) : 𝔽₃) * d (.inr m) = -1 := by
    rcases hd with rfl | rfl
    · exact fkD0_mul
    · exact fkD1_mul
  obtain ⟨κ, hκx⟩ : ∃ κ : MulAut Spin₈, ∀ x, κ x = α (y⁻¹ * x * y) :=
    ⟨α * MulAut.conj y⁻¹, fun x => by simp [MulAut.mul_apply, MulAut.conj_apply]⟩
  have hκ : ∀ x, spinAction Q₄ (κ x) = fkDiag d * spinAction Q₄ x * (fkDiag d)⁻¹ := by
    intro x
    rw [hκx, hαa, hay]
    simp only [map_mul, map_inv]
    group
  have hακ : ∀ x, α x = κ (y * x * y⁻¹) := by
    intro x
    rw [hκx, show y⁻¹ * (y * x * y⁻¹) * y = x by group]
  obtain ⟨hz0, hz2, hz3⟩ := fk_diag_fix_z κ d (-1) hdμ hκ
  obtain ⟨hb0, hb1, hb2⟩ := fk_fix_mul_of_fix κ hz0 hz2 hz3
  have hcen : ∀ c ∈ Subgroup.center Spin₈, κ c = c → α c = c := by
    intro c hc hκc
    rw [hακ, Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right, hκc]
  have hαb0 := hcen _ fk_b_mem_center hb0
  have hαb1 := hcen _ fk_b₁_mem_center hb1
  have hαb2 := hcen _ fk_b₂_mem_center hb2
  obtain ⟨ρ, hρ⟩ := fkTri_exists
  have e1 : ρ (z2 𝔽₃ * z3 𝔽₃) = z3 𝔽₃ * z0 𝔽₃ := by rw [map_mul, hρ.apply_z2, hρ.apply_z3]
  have e2 : ρ (z3 𝔽₃ * z0 𝔽₃) = z0 𝔽₃ * z2 𝔽₃ := by rw [map_mul, hρ.apply_z3, hρ.apply_z0]
  have e3 : ρ (z0 𝔽₃ * z2 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ := by rw [map_mul, hρ.apply_z0, hρ.apply_z2]
  obtain ⟨hpα1, hpα2⟩ := fk_pres_conj e1 e2 e3 hαb0 hαb1 hαb2
  obtain ⟨hpκ1, hpκ2⟩ := fk_pres_conj e1 e2 e3 hb0 hb1 hb2
  obtain ⟨A1, μ1, hμ1, hA1, hκA1⟩ := fk_sim_of_pres _ hpκ1
  obtain ⟨A2, μ2, hμ2, hA2, hκA2⟩ := fk_sim_of_pres _ hpκ2
  have n0 : (fkNode 0).map κ.toMonoidHom = fkNode 0 := by
    rw [fkNode_zero]
    exact fk_diag_map_node κ d (-1) hdμ hκ ne01 true false
  have n2 : (fkNode 2).map κ.toMonoidHom = fkNode 2 := by
    rw [fkNode_two]
    exact fk_diag_map_node κ d (-1) hdμ hκ ne23 true false
  have n3 : (fkNode 3).map κ.toMonoidHom = fkNode 3 := by
    rw [fkNode_three]
    exact fk_diag_map_node κ d (-1) hdμ hκ ne23 true true
  have m0 := fk_mult_swap κ (fkDiag d) (-1) (neg_ne_zero.mpr one_ne_zero)
    (quadPlus_fkDiag d (-1) hdμ) hκ n2 n3
  have m1 := fk_mult_swap (ρ⁻¹ * κ * ρ) A1 μ1 hμ1 hA1 hκA1
    (fk_map_conj ρ κ hρ.map_node_two n3) (fk_map_conj ρ κ hρ.map_node_three n0)
  have m2 := fk_mult_swap ((ρ * ρ)⁻¹ * κ * (ρ * ρ)) A2 μ2 hμ2 hA2 hκA2
    (fk_map_conj (ρ * ρ) κ hρ.map_map_node_two n0)
    (fk_map_conj (ρ * ρ) κ hρ.map_map_node_three n2)
  rw [fkSwap_congr ρ κ hρ.map_node_two, fkSwap_congr ρ κ hρ.map_node_three] at m1
  rw [fkSwap_congr (ρ * ρ) κ hρ.map_map_node_two,
    fkSwap_congr (ρ * ρ) κ hρ.map_map_node_three] at m2
  have hneg : (-1 : 𝔽₃) ≠ 1 :=
    Q3MFOD.neg_one_ne_one_of_card_three
      ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  have key : μ1 = 1 ∨ μ2 = 1 := by
    by_cases h30 : (FKSwap κ (fkNode 3) ↔ FKSwap κ (fkNode 0))
    · exact Or.inl (m1.mpr h30)
    · refine Or.inr (m2.mpr ?_)
      have h23 : ¬(FKSwap κ (fkNode 2) ↔ FKSwap κ (fkNode 3)) := fun h => hneg (m0.mpr h)
      exact fk_prop_xor h23 h30
  rcases key with h1 | h2
  · exact fk_finish hα2 hακ hpα1 A1 (fun v => by rw [hA1 v, h1, one_mul]) hκA1
  · exact fk_finish hα2 hακ hpα2 A2 (fun v => by rw [hA2 v, h2, one_mul]) hκA2

end CFSG.OddStandard.SmallF3.Omega
