module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Dn
public import CFSG.ClassicalInvolution.Q3.Q3TY34
public import CFSG.ClassicalInvolution.RouteD.TWED6Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TWE.D6 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TY
open scoped MatrixGroups


section Plus

theorem toral_lift_plus_six3 {X : Type} [Group X]
    (θ : spinGroup (quadPlus 6 (GaloisField 3 1)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))}
    (hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b))
    (hM : ∀ a ≤ 2, Commutes RM (R a))
    (hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((R 0).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        ((R 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i ≠ j)
    (hne : Rtw ≠ R 2)
    (htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((R 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadPlus 6 (GaloisField 3 1))) (t : Bool)
      (α : spinGroup (quadPlus 6 (GaloisField 3 1)) ≃* spinGroup (quadPlus 6 (GaloisField 3 1)))
      (g₀ : (Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
        (Fin 6 ⊕ Fin 6 → GaloisField 3 1)),
      (∀ a (ha : a ≤ 2), R a = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 2 3 (by omega) (by omega)
        (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 4 5 (by omega) (by omega)
        (by omega) true t).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadPlus 6 (GaloisField 3 1)) (α y) (g₀ z) =
        g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) y z)) ∧
      (∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
        g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) x
          ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s)) =
        spinAction (quadPlus 6 (GaloisField 3 1)) x
          ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s)) := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hf : 1 ≤ 1 := le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_plus (m := 6) (by norm_num)
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus3]
    omega
  have hQ : (quadPlus 6 (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1))
  set F₀ := plusFrame 6 (GaloisField 3 1) hm3 with hF₀
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen3 hQ (s := 2) (by omega) F₀
    hdim cq hRf hRtwf hRMf hadj hlin hcomm hM
    (fun a b hab hb i j hi hj => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hdist i j hi hj) hne htwin
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift hp2 (by norm_num : 5 ≤ 6) hf hK θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadPlus 6 (GaloisField 3 1))) :=
    isPerfect_spinGroup_quadPlus hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadPlus 6 (GaloisField 3 1)) →* _).comp
      (α : spinGroup (quadPlus 6 (GaloisField 3 1)) →* _))
      (MonoidHom.id (spinGroup (quadPlus 6 (GaloisField 3 1)))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  obtain ⟨hZ, hcent⟩ := plus_center_facts (F := GaloisField 3 1) hp2 hm3
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))),
      ∃ η : GaloisField 3 1, ∀ v, spinAction (quadPlus 6 (GaloisField 3 1)) z v = η • v :=
    fun z hz => by
      obtain ⟨η, -, hη⟩ := hcent z hz
      exact ⟨η, hη⟩
  obtain ⟨H1g, H2g, -⟩ := frame_chain_fixed_data (s := 2) (by omega) F₀ θ hker σ hscal x t hxR hxtw
    hxM hfix hfixtw hfixM hnorm0
  let i₀ : Fin 6 := ⟨4, by omega⟩
  let i₁ : Fin 6 := ⟨5, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hfixr : ∀ {i j : Fin 6} (hij : i ≠ j) (s' t' : Bool) (c : GaloisField 3 1),
      σ (θ (x * F₀.longRoot hij s' t' (.ofAdd c) * x⁻¹)) =
        θ (x * F₀.longRoot hij s' t' (.ofAdd c) * x⁻¹) →
      conjTwist α x (F₀.longRoot hij s' t' (.ofAdd c)) = F₀.longRoot hij s' t' (.ofAdd c) :=
    fun hij s' t' c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ x
      (longRoot_pow_char F₀ hij s' t' c) (longRoot_pow_char F₀ hij s' t' c) h
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h01 true t (.ofAdd c)) =
      F₀.longRoot h01 true t (.ofAdd c) := fun c =>
    hfixr h01 true t c (H1g _ ⟨F₀.longRoot h01 true t (.ofAdd c),
      ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true t c⟩, rfl⟩)
  have hO : ∀ (a b : Fin 6) (hab : a ≠ b), (a.val ≠ 4 ∧ a.val ≠ 5 ∧ a.val ≠ 0) →
      (b.val ≠ 4 ∧ b.val ≠ 5 ∧ b.val ≠ 0) → ∀ (s' t' : Bool) (c : GaloisField 3 1),
      conjTwist α x (F₀.longRoot hab s' t' (.ofAdd c)) = F₀.longRoot hab s' t' (.ofAdd c) :=
    fun a b hab ha hb s' t' c => hfixr hab s' t' c
      (H2g a b hab ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 s' t' c)
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h01 true t hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar F₀ (plus_hspan hm3) hα hα2 x
    (O := fun a => a.val ≠ 4 ∧ a.val ≠ 5 ∧ a.val ≠ 0) (a₁ := ⟨1, by omega⟩) (a₂ := ⟨2, by omega⟩)
    ⟨by simp, by simp, by simp⟩ ⟨by simp, by simp, by simp⟩
    (fun h => by have := congrArg Fin.val h; simp at this) hφ hO
  exact ⟨x, t, α, g₀, hxR, hxtw, hxM, hαθ, hg₀O, hg₀2, hconj,
    fun a h1 h3 s => hfixv a ⟨by omega, by omega, by omega⟩ s⟩

end Plus

end CFSG.ClassicalInvolution.Q3.Q3TD
