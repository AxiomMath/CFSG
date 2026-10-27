module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.RankThree.PartOne.KE.A2Shape

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


section LatticePerm

variable {τ : Tag}

@[expose] def latticePerm (π : Equiv.Perm (Fin τ.rank)) : Equiv.Perm (Fin τ.rank → ℤ) where
  toFun := permLattice π
  invFun := permLattice π.symm
  left_inv v := by ext i; simp [permLattice]
  right_inv v := by ext i; simp [permLattice]

theorem latticePerm_apply (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    latticePerm π v = permLattice π v := rfl

theorem latticePerm_neg (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    latticePerm π (-v) = -latticePerm π v := by
  ext i; simp [latticePerm_apply, permLattice]

theorem iform_latticePerm {π : Equiv.Perm (Fin τ.rank)}
    (h : ∀ i j, τ.symmetrizedCartan (π i) (π j) = τ.symmetrizedCartan i j)
    (x y : Fin τ.rank → ℤ) :
    iform (latticePerm π x) (latticePerm π y) = iform x y := by
  simp only [iform, latticePerm_apply, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [h]

theorem isRoot_latticePerm_iff {π : Equiv.Perm (Fin τ.rank)}
    (h : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (v : Fin τ.rank → ℤ) :
    IsRoot τ (latticePerm π v) ↔ IsRoot τ v := by
  refine ⟨fun hv => ?_, fun hv => hv.permLattice h⟩
  have := hv.permLattice (cartan_perm_symm h)
  convert this using 1
  ext i; simp [latticePerm_apply, permLattice]

end LatticePerm

theorem symmetrizedCartan_perm (t : TwistTag) (i j : Fin t.tag.rank) :
    t.tag.symmetrizedCartan (t.perm i) (t.perm j) = t.tag.symmetrizedCartan i j := by
  have h : t.tag.symmetrizer = 1 := by cases t <;> rfl
  simp only [Tag.symmetrizedCartan, h, Matrix.one_mul]
  exact t.cartan_perm i j

theorem exists_diagram_data {τ : Tag} {L : Type} [Field L] {P : ModGL τ L}
    (hP : P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) :
    ∃ π : Equiv.Perm (Fin τ.rank → ℤ),
      (∀ γ, IsRoot τ (π γ) ↔ IsRoot τ γ) ∧ (∀ γ, π (-γ) = -π γ) ∧
      (∀ γ δ, iform (π γ) (π δ) = iform γ δ) ∧
      ∀ γ, IsRoot τ γ → ∃ ε : L, ε * ε = 1 ∧
        ∀ c : L, P * pinnedX τ L γ c * P⁻¹ = pinnedX τ L (π γ) (ε * c) := by
  rcases hP with rfl | ⟨t, h, rfl⟩
  · refine ⟨Equiv.refl _, fun _ => Iff.rfl, fun _ => rfl, fun _ _ => rfl, fun γ _ => ⟨1, one_mul 1, fun c => ?_⟩⟩
    simp
  · subst h
    refine ⟨latticePerm t.perm, isRoot_latticePerm_iff t.cartan_perm, latticePerm_neg _,
      iform_latticePerm (symmetrizedCartan_perm t), fun γ hγ => ?_⟩
    obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := L) t hγ
    exact ⟨ε, hε, h⟩

section Step

variable {τ : Tag} {L : Type} [Field L]

theorem exists_step_pinnedX (D : LangDatum τ L) :
    ∃ ρ : Equiv.Perm (Fin τ.rank → ℤ),
      (∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) ∧ (∀ γ, ρ (-γ) = -ρ γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      ∀ γ, IsRoot τ γ → ∃ μ : L, μ ≠ 0 ∧
        ∀ c : L, D.step (pinnedX τ L γ c) = pinnedX τ L (ρ γ) (μ * c ^ D.q) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  obtain ⟨π, hπroot, hπneg, hπform, hπ⟩ := exists_diagram_data (L := L) hP
  obtain ⟨w, hn⟩ := D.n_weyl
  refine ⟨π.trans (MulAction.toPerm w), fun γ => ?_, fun γ => ?_, fun γ δ => ?_, fun γ hγ => ?_⟩
  · simp only [Equiv.trans_apply, MulAction.toPerm_apply]
    rw [isRoot_smul_iff, hπroot]
  · simp only [Equiv.trans_apply, MulAction.toPerm_apply]
    rw [hπneg, smul_neg]
  · simp only [Equiv.trans_apply, MulAction.toPerm_apply]
    rw [iform_smul, hπform]
  · obtain ⟨ε₁, hε₁, h₁⟩ := hπ γ hγ
    have hπγ : IsRoot τ (π γ) := (hπroot γ).2 hγ
    obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hπγ
    refine ⟨ε₂ * ε₁, ?_, fun c => ?_⟩
    · intro h0
      have := mul_eq_zero.1 h0
      rcases this with h | h <;> simp [h] at hε₁ hε₂
    · have hs : D.step (pinnedX τ L γ c) = D.n * D.Φ (pinnedX τ L γ c) * D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      rw [hs, hΦ, units_map_entrywiseHom_pinnedX, hFr, h₁, hn, h₂]
      simp [mul_assoc]

end Step


theorem frobeniusOnRoots_proved : FrobeniusOnRoots := by
  intro τ L _ _ D
  obtain ⟨ρ, hroot, hneg, hform, hstep⟩ := exists_step_pinnedX D
  have hq : 0 < D.q := by
    obtain ⟨Fr, hFr, -⟩ := D.steinberg
    rcases Nat.eq_zero_or_pos D.q with h | h
    · exfalso
      have h0 := hFr 0
      rw [map_zero, h, pow_zero] at h0
      exact zero_ne_one h0
    · exact h
  refine ⟨ρ, ⟨hroot, hneg, hform, ?_, ?_⟩⟩
  · intro γ hγ
    obtain ⟨μ, hμ, h⟩ := hstep γ hγ
    refine map_rootSubgroup_eq_of_forall (g := fun c => μ * c ^ D.q) ?_ h
    intro y
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (y / μ) hq
    exact ⟨x, by simp only; rw [hx]; field_simp⟩
  · intro a ha γ hγ
    obtain ⟨μ, hμ, h⟩ := hstep γ hγ
    have hfix : D.step (rootDiagUnit τ a) = rootDiagUnit τ a := by
      have := ((mem_twistedTorusOf.1 ha).2)
      simpa [LangDatum.step, MulAut.conj_apply] using this
    have hργ : IsRoot τ (ρ γ) := (hroot γ).2 hγ
    have h1 : D.step (rootDiagUnit τ a * pinnedX τ L γ 1 * (rootDiagUnit τ a)⁻¹) =
        D.step (pinnedX τ L γ ((rootChar a γ : L) * 1)) := by
      rw [rootDiagUnit_conj_pinnedX a hγ]
    rw [map_mul, map_mul, map_inv, hfix, h, h, rootDiagUnit_conj_pinnedX a hργ] at h1
    have h2 := pinnedX_injective (τ := τ) (R := L) (ρ γ) h1
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    have h3 : (rootChar a (ρ γ) : L) * μ = μ * (rootChar a γ : L) ^ D.q := by
      simpa using h2
    exact mul_right_cancel₀ hμ (by rw [h3]; ring)

end CFSG.HardMathSupport.Timmesfeld.LangTorus
