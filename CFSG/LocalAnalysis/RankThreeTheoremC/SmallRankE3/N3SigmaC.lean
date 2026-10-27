module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3SigmaA
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3SigmaB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

theorem exists_sigma {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ}
    {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hS : Q8D8Facts S z) (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    (hz : z ∈ Zc) :
    ∃ σ : ↥(Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ)) →* Equiv.Perm (Fin 6),
      ∀ g : ↥(Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ)),
        σ g = 1 ↔ ∀ s ∈ S, (g : Γ) * s * (g : Γ)⁻¹ * s⁻¹ ∈ Zc := by
  have hex : ∀ g : ↥(Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ)),
      ∃ φ : Sp4.V4 ≃+ Sp4.V4, ActsAs S Zc Ψ (g : Γ) φ ∧
        ∀ x y, Sp4.symp (φ x) (φ y) = Sp4.symp x y :=
    fun g => exists_actsAs hS hΨ hZc hz g.2
  choose φ hφ hiso using hex
  have hperm : ∀ g : ↥(Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ)),
      ∃ σ : Equiv.Perm (Fin 6), ∀ a b, φ g (Sp4.dv a b) = Sp4.dv (σ a) (σ b) :=
    fun g => Sp4.isometry_eq_perm (φ g) (hiso g)
  choose σ hσ using hperm
  have hφ1 : φ 1 = AddEquiv.refl _ :=
    actsAs_unique hΨ hZc (Subgroup.one_mem _) (hφ 1) (actsAs_one hS hΨ hZc)
  have hφmul : ∀ g h, φ (g * h) = (φ h).trans (φ g) := fun g h =>
    actsAs_unique hΨ hZc (Subgroup.mul_mem _ g.2 h.2) (hφ (g * h))
      (actsAs_mul hΨ hZc g.2 h.2 (hφ g) (hφ h))
  have hσ1 : σ 1 = 1 := by
    refine Sp4.perm_unique fun a b => ?_
    have h := hσ 1 a b
    rw [hφ1] at h
    simpa using h.symm
  have hσmul : ∀ g h, σ (g * h) = σ g * σ h := by
    intro g h
    refine Sp4.perm_unique fun a b => ?_
    have h1 := hσ (g * h) a b
    rw [hφmul] at h1
    have h2 := hσ h a b
    have h3 := hσ g (σ h a) (σ h b)
    simp only [AddEquiv.trans_apply] at h1
    rw [h2, h3] at h1
    simpa using h1.symm
  refine ⟨{ toFun := σ, map_one' := hσ1, map_mul' := hσmul }, fun g => ?_⟩
  show σ g = 1 ↔ _
  rw [← actsAs_refl_iff hS hΨ hZc hz g.2 (hφ g)]
  constructor
  · intro h1
    refine AddEquiv.ext fun x => ?_
    by_cases hx : x = 0
    · rw [hx, map_zero]; rfl
    · obtain ⟨a, b, -, rfl⟩ := Sp4.dv_surj x hx
      rw [hσ g a b, h1]
      rfl
  · intro h1
    refine Sp4.perm_unique fun a b => ?_
    have h := hσ g a b
    rw [h1] at h
    simpa using h.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
