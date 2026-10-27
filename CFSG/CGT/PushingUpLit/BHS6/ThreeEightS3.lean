module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

@[expose] def uVec3 : Fin 2 → Fin 3 → ZMod 2 := ![![1, 0, 1], ![0, 1, 1]]

@[expose] def M3 (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => uVec3 j (σ⁻¹ (Fin.castSucc i))

theorem M3_det : ∀ σ : Equiv.Perm (Fin 3), (M3 σ).det = 1 := by decide

theorem M3_one : M3 1 = 1 := by decide

theorem M3_mul : ∀ σ τ : Equiv.Perm (Fin 3), M3 (σ * τ) = M3 σ * M3 τ := by decide

theorem M3_injective : ∀ σ τ : Equiv.Perm (Fin 3), M3 σ = M3 τ → σ = τ := by decide

theorem M3_surjective : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∃ σ : Equiv.Perm (Fin 3), M3 σ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by decide

theorem M3_compat : ∀ σ : Equiv.Perm (Fin 3), ∀ a b : ZMod 2, ∀ i : Fin 2,
    (![a, b, a + b] : Fin 3 → ZMod 2) (σ⁻¹ (Fin.castSucc i)) = (M3 σ).mulVec ![a, b] i := by
  decide

@[expose] def s3Hom : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun σ := ⟨M3 σ, M3_det σ⟩
  map_one' := Subtype.ext M3_one
  map_mul' σ τ := Subtype.ext (M3_mul σ τ)

@[expose] noncomputable def s3Equiv :
    Equiv.Perm (Fin 3) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective s3Hom ⟨fun σ τ h => M3_injective σ τ (congrArg Subtype.val h), fun A => by
    obtain ⟨σ, hσ⟩ := M3_surjective A
    exact ⟨σ, Subtype.ext hσ⟩⟩

@[expose] def coordsEquiv3 : ↥(coreMod 3) ≃* Multiplicative (Fin 2 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![Multiplicative.toAdd (x : PermMod 3) 0,
    Multiplicative.toAdd (x : PermMod 3) 1]
  invFun v := ⟨Multiplicative.ofAdd ![Multiplicative.toAdd v 0, Multiplicative.toAdd v 1,
    Multiplicative.toAdd v 0 + Multiplicative.toAdd v 1], by
      rw [mem_coreMod]
      simp only [Fin.sum_univ_three]
      change (Multiplicative.toAdd v 0 + Multiplicative.toAdd v 1 +
        (Multiplicative.toAdd v 0 + Multiplicative.toAdd v 1)) = 0
      generalize Multiplicative.toAdd v 0 = a
      generalize Multiplicative.toAdd v 1 = b
      revert a b
      decide⟩
  left_inv x := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have h := x.2
    rw [mem_coreMod] at h
    simp only [Fin.sum_univ_three] at h
    funext i
    fin_cases i
    · rfl
    · rfl
    · show (Multiplicative.toAdd (x : PermMod 3) 0 + Multiplicative.toAdd (x : PermMod 3) 1) =
        Multiplicative.toAdd (x : PermMod 3) 2
      generalize Multiplicative.toAdd (x : PermMod 3) 0 = a at h ⊢
      generalize Multiplicative.toAdd (x : PermMod 3) 1 = b at h ⊢
      generalize Multiplicative.toAdd (x : PermMod 3) 2 = c at h ⊢
      revert a b c
      decide
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' _ _ := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

theorem coordsEquiv3_coreAct (σ : Equiv.Perm (Fin 3)) (x : ↥(coreMod 3)) :
    coordsEquiv3 (coreAct 3 σ x) = Multiplicative.ofAdd
      ((s3Equiv σ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)).1.mulVec
        (Multiplicative.toAdd (coordsEquiv3 x))) := by
  apply Multiplicative.toAdd.injective
  have h := x.2
  rw [mem_coreMod] at h
  simp only [Fin.sum_univ_three] at h
  have hx : Multiplicative.toAdd (x : PermMod 3) =
      ![Multiplicative.toAdd (x : PermMod 3) 0, Multiplicative.toAdd (x : PermMod 3) 1,
        Multiplicative.toAdd (x : PermMod 3) 0 + Multiplicative.toAdd (x : PermMod 3) 1] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show Multiplicative.toAdd (x : PermMod 3) 2 =
        Multiplicative.toAdd (x : PermMod 3) 0 + Multiplicative.toAdd (x : PermMod 3) 1
      generalize Multiplicative.toAdd (x : PermMod 3) 0 = a at h ⊢
      generalize Multiplicative.toAdd (x : PermMod 3) 1 = b at h ⊢
      generalize Multiplicative.toAdd (x : PermMod 3) 2 = c at h ⊢
      revert a b c
      decide
  funext i
  have h1 : Multiplicative.toAdd (coordsEquiv3 (coreAct 3 σ x)) i =
      Multiplicative.toAdd (x : PermMod 3) (σ⁻¹ (Fin.castSucc i)) := by
    fin_cases i <;> rfl
  rw [h1, hx]
  exact M3_compat σ _ _ i

theorem isNatSL_one_of_isNatSym_three {Γ : Type} [Group Γ] {G V : Subgroup Γ}
    (h : IsNatSym G V 3) : IsNatSL G V 1 := by
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := h
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero]
    rfl
  let e : ZMod 2 ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  refine ⟨((slEquiv e).toMonoidHom.comp s3Equiv.toMonoidHom).comp φ,
    ((vecEquiv e).toMonoidHom.comp coordsEquiv3.toMonoidHom).comp ψ, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((slEquiv e).surjective.comp s3Equiv.surjective).comp hφs
  · rw [← hφk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · exact ((vecEquiv e).surjective.comp coordsEquiv3.surjective).comp hψs
  · rw [← hψk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · intro g w hw
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hψe g w hw, coordsEquiv3_coreAct, ← toAdd_vecEquiv_mulVec e]
    rfl

end CFSG.CGT.PushingUpLit.BHS6
