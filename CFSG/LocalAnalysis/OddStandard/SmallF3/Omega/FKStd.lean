module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKSim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKIsom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMultNegOne
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4 QuadraticMap
open CFSG.LieType.Universal.Spin (spinAction quadPlus nondegenerate_quadPlus
  nondegenerate_polarBilin_quadPlus range_spinAction_quadPlus_eq_commutator)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Q₀" => quadPlus 4 (ZMod 3)

private theorem fk_conjNormal_eq_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    {x : OGroup Q} (hx : x ∈ omegaGroup hQ) :
    ∃ p : omegaProj hQ, MulAut.conjNormal (toProj Q x) = MulAut.conj p :=
  ⟨⟨toProj Q x, (mem_omegaProj_iff hQ).mpr ⟨x, hx, rfl⟩⟩,
    MulEquiv.ext fun y => Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      rfl)⟩

private theorem fk_congr_conj_eq {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (τ f : MulAut G) :
    MulAut.congr e (τ * f * τ⁻¹) =
      MulAut.congr e τ * MulAut.congr e f * (MulAut.congr e τ)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

private theorem fk_congr_congr_symm {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut H) : MulAut.congr e (MulAut.congr e.symm α) = α :=
  MulEquiv.ext fun y => by simp [MulAut.congr_apply]

section Std


theorem fkStmt_std_of_multNegOne (h : FKMultNegOne) :
    FKStmt (nondegenerate_quadPlus 4 (ZMod 3)) := by
  intro α hα2 hinner
  obtain ⟨e, he⟩ := fk_exists_equiv
  have hf'2 : MulAut.congr e.symm α * MulAut.congr e.symm α = 1 := by
    rw [← map_mul, hα2, map_one]
  obtain ⟨αt, hαt2, hdesc⟩ := exists_lift_desc (MulAut.congr e.symm α) hf'2
  obtain ⟨σ, -, hpres⟩ := Q3MFOD.exists_pres_conj αt hαt2
  have hσ2 : σ * αt * σ⁻¹ * (σ * αt * σ⁻¹) = 1 := by
    calc σ * αt * σ⁻¹ * (σ * αt * σ⁻¹) = σ * (αt * αt) * σ⁻¹ := by group
      _ = 1 := by rw [hαt2]; group
  obtain ⟨a₁, m, s₁, hm, -, hQ₁, ha₁, hαa₁⟩ := exists_sim_of_pres _ hσ2 hpres
  obtain ⟨σ₂, a, s, hQa, ha2, hαa⟩ : ∃ (σ₂ : MulAut (spinGroup Q₄))
      (a : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) (s : 𝔽₃),
      (∀ v, Q₄ (a v) = Q₄ v) ∧ (∀ v, a (a v) = s • v) ∧
        ∀ x, spinAction Q₄ ((σ₂ * αt * σ₂⁻¹) x) = a * spinAction Q₄ x * a⁻¹ := by
    rcases hm with rfl | rfl
    · exact ⟨σ, a₁, s₁, fun v => by rw [hQ₁ v, one_mul], ha₁, hαa₁⟩
    · obtain ⟨σ', -, a', s', h1, h2, h3⟩ :=
        h _ hσ2 hpres a₁ s₁ (fun v => by rw [hQ₁ v, neg_one_mul]) ha₁ hαa₁
      refine ⟨σ' * σ, a', s', h1, h2, ?_⟩
      have e1 : σ' * σ * αt * (σ' * σ)⁻¹ = σ' * (σ * αt * σ⁻¹) * σ'⁻¹ := by group
      rw [e1]
      exact h3
  have ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hQa
  have hcongr := fk_congr_descAut he (σ₂ * αt * σ₂⁻¹) ha hαa
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut (omegaProj (nondegenerate_quadPlus 4 (ZMod 3))),
      β = MulAut.congr e (Q3MFOD.descAut σ₂) := ⟨_, rfl⟩
  have hβ : MulAut.congr e (Q3MFOD.descAut (σ₂ * αt * σ₂⁻¹)) = β * α * β⁻¹ := by
    have h1 : Q3MFOD.descAut (σ₂ * αt * σ₂⁻¹) =
        Q3MFOD.descAut σ₂ * MulAut.congr e.symm α * (Q3MFOD.descAut σ₂)⁻¹ := by
      rw [Q3MFOD.descAut_mul, Q3MFOD.descAut_mul, Q3MFOD.descAut_inv, hdesc]
    rw [h1, fk_congr_conj_eq, fk_congr_congr_symm, hβdef]
  rw [hβ] at hcongr
  have hnotinner : ∀ p : omegaProj (nondegenerate_quadPlus 4 (ZMod 3)),
      β * α * β⁻¹ ≠ MulAut.conj p := by
    intro p hp
    apply hinner
    refine ⟨β⁻¹ p, ?_⟩
    rw [← inv_mul_conj_mul, ← hp]
    group
  rcases fk_sq_eq_of_orth hQa ha2 with rfl | rfl
  · refine ⟨β⁻¹, fkOrth ha, ?_, ?_, ?_⟩
    · have h1 : a * a = 1 := LinearEquiv.ext fun v => by simpa using ha2 v
      apply Subtype.ext
      change LinearEquiv.autCongr fkCoord a * LinearEquiv.autCongr fkCoord a = 1
      rw [← map_mul, h1, map_one]
    · intro hmem
      obtain ⟨p, hp⟩ := fk_conjNormal_eq_conj (nondegenerate_quadPlus 4 (ZMod 3)) hmem
      exact hnotinner p (hcongr.trans hp)
    · rw [inv_inv]
      exact hcongr
  · exfalso
    have hK : Nat.card 𝔽₃ = 3 :=
      CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
    have hcomm := mem_commutator_of_sq_neg_one hK (nondegenerate_polarBilin_quadPlus 4 𝔽₃)
      finrank_d4 ha (fun v => by rw [ha2, neg_one_smul])
    rw [← range_spinAction_quadPlus_eq_commutator (n := 4) (K := 𝔽₃) (by norm_num)] at hcomm
    obtain ⟨y, hy⟩ := hcomm
    have hinn := fk_congr_descAut_conj (e := e) (σ₂ * αt * σ₂⁻¹) y
      (fun x => by rw [hαa, ← hy])
    exact hnotinner _ (hβ.symm.trans hinn)

end Std

end CFSG.OddStandard.SmallF3.Omega
