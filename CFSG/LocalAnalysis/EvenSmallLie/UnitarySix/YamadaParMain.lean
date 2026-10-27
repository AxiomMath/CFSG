module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSUJ
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix Subgroup CFSG.Fischer
open scoped MatrixGroups

variable {Γ : Type} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {K : Subgroup Γ} {θ : K ≃* SU42b} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)} {z : ℕ}

theorem rhoL_of_mem_fixSigma (hz : z = 1 ∨ z = 2) {g : SL4} (hg : g ∈ fixSigma) :
    ∃ x : SU42b, rhoL z g = rhoMHom x := by
  have hg' : g ∈ genSLGroup := genSLGroup_eq_fixSigma ▸ hg
  refine ⟨genSLEquiv ⟨g, hg'⟩, ?_⟩
  have hx : (((genSLEquiv ⟨g, hg'⟩ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8) =
      reF4 (g : Matrix (Fin 4) (Fin 4) F4) := by rw [coe_genSLEquiv]; rfl
  have hσ : sigmaSL g = g := hg
  set z' := if z = 1 then 0 else 3 with hz'
  have hz'03 : z' = 0 ∨ z' = 3 := by rcases hz with rfl | rfl <;> simp [hz']
  have hl : lineM z = lineM z' ∧ lineInvM z = lineInvM z' := by
    rcases hz with rfl | rfl <;> exact ⟨rfl, rfl⟩
  rw [rhoM_eq_rhoU_diag hz'03, rhoL_apply, hσ, rhoU_apply, hl.1, hl.2]
  change _ = lineM z' * bdiag (((genSLEquiv ⟨g, hg'⟩ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8)
    (((genSLEquiv ⟨g, hg'⟩ : SU42b) : GL (Fin 8) (ZMod 2)) : Mat8) * lineInvM z'
  rw [hx]

theorem matOf_π_θ (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (x : SU42b) : matOf e (π ((θ.symm x : K) : Γ)) = rhoMHom x := by
  rw [hK, MulEquiv.apply_symm_apply]; rfl

theorem R3Hyp.main [Finite Γ] [Finite W] (h : R3Hyp π K θ τW ι D B τ) :
    (∀ γ, τ γ = γ → γ ∈ K) ∧
      ((∃ ψ : SL4 ≃* Γ, ∀ g, τ (ψ g) = ψ (sigmaSL g)) ∨
        ∃ ψ : SU42b × SU42b ≃* Γ, ∀ p, τ (ψ p) = ψ p.swap) := by
  obtain ⟨e, z, hz, he, hK, hDe, hDe'⟩ := h.exists_coords
  have hzc : z = 1 ∨ z = 2 ∨ z = 0 ∨ z = 3 := by omega
  rcases hzc with hz1 | hz1 | hz1 | hz1
  all_goals first
    | (have hzL : z = 1 ∨ z = 2 := by omega
       obtain ⟨ψ, hψ, hτ⟩ := h.exists_equiv_SL4 he hzL hK hDe hDe'
       refine ⟨fun γ hγ => ?_, Or.inl ⟨ψ, hτ⟩⟩
       obtain ⟨g, rfl⟩ := ψ.surjective γ
       have hgσ : sigmaSL g = g := ψ.injective (by rw [← hτ, hγ])
       obtain ⟨x, hx⟩ := rhoL_of_mem_fixSigma hzL hgσ
       have : ψ g = ((θ.symm x : K) : Γ) := by
         obtain ⟨g', hg'⟩ := ψ.surjective ((θ.symm x : K) : Γ)
         rw [← hg']
         congr 1
         apply rhoL_injective z
         rw [← hψ, ← hψ, hg', matOf_π_θ hK, ← hx, hψ]
       rw [this]
       exact (θ.symm x).2)
    | (have hzU : z = 0 ∨ z = 3 := by omega
       obtain ⟨ψ, hψ, hτ⟩ := h.exists_equiv_SU42b_prod he hzU hK hDe hDe'
       refine ⟨fun γ hγ => ?_, Or.inr ⟨ψ, hτ⟩⟩
       obtain ⟨p, rfl⟩ := ψ.surjective γ
       have hp : p.swap = p := ψ.injective (by rw [← hτ, hγ])
       have hp' : p = diagSU p.1 := by
         ext1
         · rfl
         · exact congrArg Prod.fst hp
       have : ψ p = ((θ.symm p.1 : K) : Γ) := by
         obtain ⟨q, hq⟩ := ψ.surjective ((θ.symm p.1 : K) : Γ)
         rw [← hq]
         congr 1
         apply rhoU_injective z
         rw [← hψ, ← hψ, hq, matOf_π_θ hK, rhoM_eq_rhoU_diag hzU, ← hp', hψ]
       rw [this]
       exact (θ.symm p.1).2)

noncomputable def slEquivF4 (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4) : SL(4, F) ≃* SL4 :=
  have : Fintype F := Fintype.ofFinite F
  let e : F ≃+* F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_F4])
  { toFun := SpecialLinearGroup.map e.toRingHom
    invFun := SpecialLinearGroup.map e.symm.toRingHom
    left_inv := fun g => Subtype.ext (by ext i j; simp)
    right_inv := fun g => Subtype.ext (by ext i j; simp)
    map_mul' := map_mul _ }

theorem R3Hyp.main_factor [Finite Γ] [Finite W] (h : R3Hyp π K θ τW ι D B τ) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    (∀ γ, τ γ = γ → γ ∈ K) ∧
      ((∃ ψ : SL(4, F) →* Γ, Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) ∨
        ∃ M : Subgroup Γ, M ⊔ M.map τ = ⊤ ∧ ⁅M, M.map τ⁆ = ⊥ ∧ M ⊓ M.map τ = ⊥ ∧
          CFSG.Blueprint.LieModel M .PSU 4 2 1) := by
  obtain ⟨hfix, hL | hU⟩ := h.main
  · obtain ⟨ψ, -⟩ := hL
    refine ⟨hfix, Or.inl ⟨ψ.toMonoidHom.comp (slEquivF4 F hF).toMonoidHom, ?_, ?_⟩⟩
    · exact ψ.surjective.comp (slEquivF4 F hF).surjective
    · intro g hg
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, ← map_one ψ, ψ.injective.eq_iff, ← map_one (slEquivF4 F hF),
        (slEquivF4 F hF).injective.eq_iff] at hg
      rw [hg]
      exact Subgroup.one_mem _
  · obtain ⟨ψ, hτ⟩ := hU
    set f₁ := ψ.toMonoidHom.comp (MonoidHom.inl SU42b SU42b)
    set f₂ := ψ.toMonoidHom.comp (MonoidHom.inr SU42b SU42b)
    have hmap : f₁.range.map τ = f₂.range := by
      rw [MonoidHom.range_eq_map, Subgroup.map_map, MonoidHom.range_eq_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
        MonoidHom.inr_apply, f₁, f₂, hτ]
      rfl
    refine ⟨hfix, Or.inr ⟨f₁.range, ?_, ?_, ?_, ?_⟩⟩
    · rw [hmap, eq_top_iff]
      intro γ _
      obtain ⟨⟨x, y⟩, rfl⟩ := ψ.surjective γ
      have : ψ (x, y) = f₁ x * f₂ y := by
        simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
          MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [this]
      exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨y, rfl⟩
    · rw [hmap, Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
        MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    · rw [hmap, eq_bot_iff]
      rintro _ ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
        MonoidHom.inr_apply] at hy ⊢
      have := ψ.injective hy
      rw [Subgroup.mem_bot, show x = 1 from (congrArg Prod.fst this).symm]
      exact map_one ψ
    · have hinj : Function.Injective f₁ := fun x y hxy =>
        congrArg Prod.fst (ψ.injective hxy)
      exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (MonoidHom.ofInjective hinj) lieModel_SU42b

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
