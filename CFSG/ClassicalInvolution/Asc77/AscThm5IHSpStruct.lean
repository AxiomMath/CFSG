module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHProd
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section Center

variable {F : Type} [Field F]

theorem thm5IH_sp_center_sq {a : ℕ} (ha : 1 ≤ a) {g : StatedSp a F}
    (hg : g ∈ Subgroup.center (StatedSp a F)) : g * g = 1 := by
  rw [Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hmem : (c : F) ^ 2 = 1 := by
    have h := g.2
    rw [← hc, CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff ha] at h
    exact h
  have hc2 : c * c = 1 := Units.ext (by rw [Units.val_mul, ← pow_two, hmem, Units.val_one])
  apply Subtype.ext
  show (g : GL (Fin a ⊕ Fin a) F) * (g : GL (Fin a ⊕ Fin a) F) = 1
  rw [← hc, ← map_mul, hc2, map_one]

theorem thm5IH_center_sq_of_equiv_sp {T : Type} [Group T] {Q : Subgroup T} {a : ℕ} (ha : 1 ≤ a)
    (e : StatedSp a F ≃* ↥Q) : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c * c = 1 := by
  intro c hc hcc
  have hz : e.symm ⟨c, hc⟩ ∈ Subgroup.center (StatedSp a F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcc _ (e g).2).symm
  have h := thm5IH_sp_center_sq ha hz
  have h2 : (⟨c, hc⟩ : ↥Q) * ⟨c, hc⟩ = 1 := by
    have := congrArg e h
    rwa [map_mul, MulEquiv.apply_symm_apply, map_one] at this
  exact congrArg Subtype.val h2

end Center

section Involution

variable {F : Type} [Field F] {n : ℕ}

theorem thm5IH_sp_exists_card_pos (h2 : (2 : F) ≠ 0) {y : StatedSp n F} (hy2 : y * y = 1)
    (hyc : ¬ ∀ s : StatedSp n F, y * s = s * y) :
    ∃ (S : Finset (Fin n)) (g : StatedSp n F), y = g * stdInv F S * g⁻¹ ∧ 1 ≤ S.card ∧
      1 ≤ Sᶜ.card := by
  classical
  obtain ⟨S, g, hg⟩ := exists_mul_eq_stdInv h2 hy2
  have hyg : y = g * stdInv F S * g⁻¹ := by
    rw [← hg]
    group
  refine ⟨S, g, hyg, ?_, ?_⟩
  · by_contra hS
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hyc
    have : y = 1 := by rw [hyg, hS0, stdInv_empty]; group
    intro s
    rw [this, one_mul, mul_one]
  · by_contra hS
    have hSc : Sᶜ = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSu : S = Finset.univ := Finset.eq_univ_of_forall fun k => by
      by_contra hk
      have : k ∈ Sᶜ := Finset.mem_compl.mpr hk
      rw [hSc] at this
      exact absurd this (Finset.notMem_empty k)
    have hsign : stdSign F S = fun _ => -1 := funext fun t =>
      stdSign_of_mem (by simp [cS, hSu])
    have hmat : mat n F (stdInv F S) = -1 := by
      rw [mat_stdInv, hsign]
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
      · simp [hab]
    have hmy : mat n F y = -1 := by
      rw [hyg, map_mul, map_mul, hmat]
      have h1 : mat n F g * mat n F g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      simp [h1]
    apply hyc
    intro s
    apply mat_injective
    rw [map_mul, map_mul, hmy]
    simp

end Involution

section Prod

variable {p e n : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem thm5IH_sp_centralizerProd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {π : StatedSp n (GaloisField p e) →* Y} (hπ : π.ker ≤ Subgroup.center _)
    {y : StatedSp n (GaloisField p e)} (hy2 : y * y = 1)
    (hyc : ¬ ∀ s : StatedSp n (GaloisField p e), y * s = s * y) :
    CentralizerProd π.range (π y) ((longRootGroup y).map π) ((complGroup y).map π) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  obtain ⟨S, g, hyg, hS1, hS2⟩ := thm5IH_sp_exists_card_pos h2 hy2 hyc
  obtain ⟨e₁⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hyg
  obtain ⟨e₂⟩ := nonempty_mulEquiv_complGroup_sp h2 hyg
  have hQ₁ : CFSG.Open.IsQuasisimple ↥(longRootGroup y) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv e₁.symm
      (open_isQuasisimple_statedSp hq hS1)
  have hQ₂ : CFSG.Open.IsQuasisimple ↥(complGroup y) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv e₂.symm
      (open_isQuasisimple_statedSp hq hS2)
  exact thm5IH_centralizerProd_of_quasisimple hπ hy2 hQ₁ hQ₂
    (thm5IH_center_sq_of_equiv_sp hS1 e₁) (thm5IH_center_sq_of_equiv_sp hS2 e₂)
    (fun q hq => comm_of_mem_longRootGroup h2 hy2 hq)
    (fun q hq => comm_of_mem_complGroup h2 hy2 hq)
    (fun a ha b hb => commute_of_mem_longRootGroup_of_mem_complGroup h2 hy2 ha hb)
    (fun g' hg' => exists_mul_of_commute h2 hy2 hg')

end Prod

end CFSG.ClassicalInvolution.Asc77
