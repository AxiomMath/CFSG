module

public import CFSG.GF2Type.Smith1979W3.CaseD.Perm8
public import CFSG.GF2Type.Smith1979W3.CaseD.TypeDict
public import CFSG.LargeExtraspecial.Types

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix Matrix Equiv
  CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem sub_eq_add_of_module_zmod_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v w : W) : v - w = v + w := by
  have hneg : -w = w := by
    rw [neg_eq_iff_add_eq_zero]
    have h2 : w + w = 0 := by
      have h : (1 + 1 : ZMod 2) • w = 0 := by
        rw [show (1 + 1 : ZMod 2) = 0 from by decide, zero_smul]
      rwa [add_smul, one_smul] at h
    exact h2
  rw [sub_eq_add_neg, hneg]

@[expose] noncomputable def mLin :
    Perm (Fin 8) →* ((ι6 → ZMod 2) ≃ₗ[ZMod 2] (ι6 → ZMod 2)) :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι6 (ZMod 2)).toMonoidHom.comp psi

theorem mLin_apply (σ : Perm (Fin 8)) (w : ι6 → ZMod 2) : mLin σ w = Mm σ *ᵥ w := by
  change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι6 (ZMod 2)) (psi σ) w = Mm σ *ᵥ w
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, psi_val]

@[expose] noncomputable def permLin (E : V ≃ₗ[ZMod 2] (ι6 → ZMod 2)) :
    Perm (Fin 8) →* (V ≃ₗ[ZMod 2] V) :=
  (LinearEquiv.autCongr E.symm).toMonoidHom.comp mLin

variable (E : V ≃ₗ[ZMod 2] (ι6 → ZMod 2))

theorem E_permLin (σ : Perm (Fin 8)) (v : V) : E (permLin E σ v) = Mm σ *ᵥ E v := by
  simp only [permLin, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    mLin_apply]

theorem permLin_injective : Function.Injective (permLin E) := by
  intro σ τ h
  apply psi_injective
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro w
  simp only [psi_val]
  have h3 := congrArg (fun f : V ≃ₗ[ZMod 2] V => E (f (E.symm w))) h
  simpa only [E_permLin, LinearEquiv.apply_symm_apply] using h3

theorem permLin_mem (hE : ∀ v, Q6 (E v) = q v) (σ : Perm (Fin 8)) :
    permLin E σ ∈ TauCeti.QuadraticMap.orthogonalGroup q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [← hE (permLin E σ v), E_permLin, Q6_Mm, hE v]

theorem exists_permLin_eq (hE : ∀ v, Q6 (E v) = q v) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) : ∃ σ, permLin E σ = g := by
  set L : (ι6 → ZMod 2) ≃ₗ[ZMod 2] (ι6 → ZMod 2) := (E.symm.trans g).trans E with hL
  set A : GL ι6 (ZMod 2) :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι6 (ZMod 2)).symm L with hA
  have hAapply : ∀ w, (A : Matrix ι6 ι6 (ZMod 2)) *ᵥ w = L w := by
    intro w
    rw [hA, ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply]
  have hLw : ∀ w, L w = E (g (E.symm w)) := by
    intro w
    rw [hL]
    rfl
  have hA_mem : A ∈ O6 := by
    rw [mem_O6]
    intro w
    rw [hAapply w, hLw w, hE (g (E.symm w)),
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg (E.symm w), ← hE (E.symm w),
      LinearEquiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ := O6_le_range A hA_mem
  refine ⟨σ, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply E.injective
  rw [E_permLin]
  have hmat : Mm σ = (A : Matrix ι6 ι6 (ZMod 2)) := by
    have hc := congrArg (fun x : GL ι6 (ZMod 2) => (x : Matrix ι6 ι6 (ZMod 2))) hσ
    simpa only [psi_val] using hc
  rw [hmat, hAapply, hL]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

@[expose] noncomputable def permEquivOrth (hE : ∀ v, Q6 (E v) = q v) :
    Perm (Fin 8) ≃* TauCeti.QuadraticMap.orthogonalGroup q :=
  MulEquiv.ofBijective ((permLin E).codRestrict _ (permLin_mem E hE))
    ⟨fun σ τ h => permLin_injective E (congrArg Subtype.val h), fun g => by
      obtain ⟨σ, hσ⟩ := exists_permLin_eq E hE g.2
      exact ⟨σ, Subtype.ext hσ⟩⟩

theorem coe_permEquivOrth (hE : ∀ v, Q6 (E v) = q v) (σ : Perm (Fin 8)) :
    ((permEquivOrth E hE σ : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) =
      permLin E σ := rfl

theorem mem_commImage_iff (σ : Perm (Fin 8)) (y : ι6 → ZMod 2) :
    y ∈ commImage σ ↔ ∃ x ∈ commSpace (permLin E σ), E x = y := by
  constructor
  · intro hy
    rw [commImage, Finset.mem_image] at hy
    obtain ⟨w, -, hw⟩ := hy
    refine ⟨permLin E σ (E.symm w) - E.symm w, sub_mem_commSpace _ _, ?_⟩
    rw [sub_eq_add_of_module_zmod_two, map_add, E_permLin, LinearEquiv.apply_symm_apply, ← hw,
      add_comm]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ := mem_commSpace.mp hx
    rw [commImage, Finset.mem_image]
    refine ⟨E v, Finset.mem_univ _, ?_⟩
    rw [← hv, sub_eq_add_of_module_zmod_two, map_add, E_permLin, add_comm]

theorem card_commImage_eq (σ : Perm (Fin 8)) :
    (commImage σ).card = Nat.card (commSpace (permLin E σ)) := by
  have h : Nat.card (commSpace (permLin E σ)) =
      Nat.card {y : ι6 → ZMod 2 // y ∈ commImage σ} :=
    Nat.card_congr (Equiv.subtypeEquiv E.toEquiv (fun x => by
      rw [mem_commImage_iff E]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x', hx', hEq⟩
        rw [← E.injective hEq]
        exact hx'))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem isDT_of_isTypeC (hE : ∀ v, Q6 (E v) = q v) {σ : Perm (Fin 8)}
    (hC : IsTypeC q (permLin E σ) 2) : IsDT σ := by
  haveI : Module.Finite (ZMod 2) V :=
    Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  refine isDT_of_commImage ?_ ?_ ?_ ?_
  · apply permLin_injective E
    rw [map_mul, hC.2.2.1, map_one]
  · intro h
    exact hC.2.1 (by rw [h, map_one])
  · rw [card_commImage_eq E σ, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      hC.2.2.2.1]
    norm_num
  · obtain ⟨x, hx, hxq⟩ := hC.2.2.2.2.2
    exact ⟨E x, (mem_commImage_iff E σ (E x)).mpr ⟨x, hx, rfl⟩, by rw [hE x]; exact hxq⟩

theorem irr8_comap (hE : ∀ v, Q6 (E v) = q v)
    {Mbar : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)}
    (hirr : ¬ ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g ∈ Mbar, ∀ v ∈ W, (g : V ≃ₗ[ZMod 2] V) v ∈ W) :
    Irr8 (Mbar.comap (permEquivOrth E hE).toMonoidHom) := by
  intro U hU
  set W : Submodule (ZMod 2) V := U.comap E.toLinearMap
  have hWinv : ∀ g ∈ Mbar, ∀ v ∈ W, (g : V ≃ₗ[ZMod 2] V) v ∈ W := by
    intro g hg v hv
    rw [Submodule.mem_comap] at hv ⊢
    have hσX : (permEquivOrth E hE).symm g ∈
        Mbar.comap (permEquivOrth E hE).toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hg
    have hg' : (g : V ≃ₗ[ZMod 2] V) = permLin E ((permEquivOrth E hE).symm g) := by
      rw [← coe_permEquivOrth E hE ((permEquivOrth E hE).symm g), MulEquiv.apply_symm_apply]
    rw [hg']
    change E (permLin E ((permEquivOrth E hE).symm g) v) ∈ U
    rw [E_permLin]
    exact hU ((permEquivOrth E hE).symm g) hσX (E v) hv
  have hW : W = ⊥ ∨ W = ⊤ := by
    by_contra h
    rw [not_or] at h
    exact hirr ⟨W, h.1, h.2, hWinv⟩
  rcases hW with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hu' : E.symm u ∈ W := by
      rw [Submodule.mem_comap]
      simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] using hu
    rw [hbot, Submodule.mem_bot] at hu'
    rw [← LinearEquiv.apply_symm_apply E u, hu', map_zero]
  · right
    rw [Submodule.eq_top_iff']
    intro u
    have hu' : E.symm u ∈ W := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_comap] at hu'
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] using hu'

theorem exists_nine_le_stab_of_model (hE : ∀ v, Q6 (E v) = q v)
    {Mbar : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)}
    (hirr : ¬ ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g ∈ Mbar, ∀ v ∈ W, (g : V ≃ₗ[ZMod 2] V) v ∈ W)
    {s : TauCeti.QuadraticMap.orthogonalGroup q} (hs : s ∈ Mbar)
    (hsC : IsTypeC q (s : V ≃ₗ[ZMod 2] V) 2) {x : V} (hx0 : x ≠ 0) (hx : q x = 0) :
    ∃ P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q), P ≤ Mbar ∧ Nat.card P = 9 ∧
      ∀ p ∈ P, (p : V ≃ₗ[ZMod 2] V) x = x := by
  have hIrr : Irr8 (Mbar.comap (permEquivOrth E hE).toMonoidHom) := irr8_comap E hE hirr
  have htX : (permEquivOrth E hE).symm s ∈
      Mbar.comap (permEquivOrth E hE).toMonoidHom := by
    rw [Subgroup.mem_comap]
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hs
  have htC : IsTypeC q (permLin E ((permEquivOrth E hE).symm s)) 2 := by
    have h1 := coe_permEquivOrth E hE ((permEquivOrth E hE).symm s)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact hsC
  have htDT : IsDT ((permEquivOrth E hE).symm s) := isDT_of_isTypeC E hE htC
  have hx0' : E x ≠ 0 := by
    intro h
    exact hx0 (E.injective (by rw [h, map_zero]))
  have hx' : Q6 (E x) = 0 := by rw [hE x, hx]
  obtain ⟨P₀, hP₀X, hP₀card, hP₀stab⟩ :=
    exists_nine_le_stab_perm8 hIrr htX htDT hx0' hx'
  refine ⟨P₀.map (permEquivOrth E hE).toMonoidHom, ?_, ?_, ?_⟩
  · intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨σ, hσP, hσeq⟩ := hp
    rw [← hσeq]
    exact Subgroup.mem_comap.mp (hP₀X hσP)
  · rw [Subgroup.card_map_of_injective (f := (permEquivOrth E hE).toMonoidHom)
      (permEquivOrth E hE).injective, hP₀card]
  · intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨σ, hσP, hσeq⟩ := hp
    rw [← hσeq, MulEquiv.coe_toMonoidHom, coe_permEquivOrth E hE]
    apply E.injective
    rw [E_permLin, hP₀stab σ hσP]

end CFSG.GF2Type.Smith1979W3.CaseD
