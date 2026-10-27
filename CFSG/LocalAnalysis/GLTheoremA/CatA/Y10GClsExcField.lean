module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.YS09Field
open scoped MatrixGroups Matrix

section Graph

variable {M R S : Type*} [Group M] [Group R] [Group S]

theorem graph_one (H : Subgroup M) (π : H →* R) (act : S → M → M)
    (hact1 : ∀ x, act 1 x = x) (rel : S → H → H → Prop)
    (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h) :
    LargeEvenGraphAut π (rel 1) 1 := by
  intro h h' hh'
  have e1 : (h' : M) = (h : M) := by rw [(hrel 1 h h').1 hh', hact1]
  rw [Subtype.ext e1, MulAut.one_apply]

theorem graph_inv (H : Subgroup M) (π : H →* R) (act : S → M → M)
    (hact1 : ∀ x, act 1 x = x) (hactmul : ∀ a b x, act (a * b) x = act a (act b x))
    (rel : S → H → H → Prop) (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h)
    {a : S} {f : MulAut R} (hf : LargeEvenGraphAut π (rel a) f) :
    LargeEvenGraphAut π (rel a⁻¹) f⁻¹ := by
  intro h h' hh'
  have h2 : act a (act a⁻¹ (h : M)) = (h : M) := by
    rw [← hactmul a a⁻¹, mul_inv_cancel, hact1]
  have h1 : (h : M) = act a (h' : M) := by
    rw [← h2, ← (hrel a⁻¹ h h').1 hh']
  have h3 : f (π h') = π h := hf h' h ((hrel a h' h).2 h1)
  calc f⁻¹ (π h) = f⁻¹ (f (π h')) := by rw [h3]
    _ = π h' := MulEquiv.symm_apply_apply f (π h')

end Graph

section Chev

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem chevField_closure (H : Subgroup (LargeEvenChevGL A K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, chevAct A K σ h ∈ H)
    {f : MulAut (LargeEvenCenterQuot H)}
    (hf : f ∈ Subgroup.closure (LargeEvenChevFieldImage A K H)) :
    f ∈ LargeEvenChevFieldImage A K H := by
  refine Subgroup.closure_induction (p := fun g _ => g ∈ LargeEvenChevFieldImage A K H)
    (fun x hx => hx) ?_ ?_ ?_ hf
  · exact ⟨1, graph_one H (LargeEvenCenterMk H) (fun τ g => chevAct A K τ g)
      (chevAct_one A K)
      (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
        LargeEvenEntrywise A K τ (map_zero τ)
          ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
      (fun τ h h' => by rw [Units.ext_iff, chevAct_val])⟩
  · rintro x y - - ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, FP.graph_mul H (LargeEvenCenterMk H) (fun τ g => chevAct A K τ g)
      (fun a b x => chevAct_mul A K a b x) (fun τ h => hH τ h h.2)
      (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
        LargeEvenEntrywise A K τ (map_zero τ)
          ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
      (fun τ h h' => by rw [Units.ext_iff, chevAct_val]) hσ hτ⟩
  · rintro x - ⟨σ, hσ⟩
    exact ⟨σ⁻¹, graph_inv H (LargeEvenCenterMk H) (fun τ g => chevAct A K τ g)
      (chevAct_one A K) (fun a b x => chevAct_mul A K a b x)
      (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
        LargeEvenEntrywise A K τ (map_zero τ)
          ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
      (fun τ h h' => by rw [Units.ext_iff, chevAct_val]) hσ⟩

end Chev

section Mat

variable {ι K R : Type} [Fintype ι] [DecidableEq ι] [Field K] [Group R]

theorem matField_closure (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (π : H →* R) {f : MulAut R} (hf : f ∈ Subgroup.closure (LargeEvenMatFieldImage π)) :
    f ∈ LargeEvenMatFieldImage π := by
  refine Subgroup.closure_induction (p := fun g _ => g ∈ LargeEvenMatFieldImage π)
    (fun x hx => hx) ?_ ?_ ?_ hf
  · exact ⟨1, graph_one (S := K ≃+* K) H π
      (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g) glMap_one
      (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) =
        ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
      (fun τ h h' => by rw [Units.ext_iff, coe_glMap])⟩
  · rintro x y - - ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, FP.graph_mul (S := K ≃+* K) H π
      (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g)
      (fun a b x => glMap_mul a b x) (fun τ h => hH τ h h.2)
      (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) =
        ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
      (fun τ h h' => by rw [Units.ext_iff, coe_glMap]) hσ hτ⟩
  · rintro x - ⟨σ, hσ⟩
    exact ⟨σ⁻¹, graph_inv (S := K ≃+* K) H π
      (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g)
      glMap_one (fun a b x => glMap_mul a b x)
      (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) =
        ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
      (fun τ h h' => by rw [Units.ext_iff, coe_glMap]) hσ⟩

end Mat

abbrev ClosureCont (Q : LargeEvenRawCont) : LargeEvenRawCont :=
  fun R _ I F => Q R I F ∧ ∀ f ∈ Subgroup.closure F, f ∈ F

theorem recChevalley_closure {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {q : ℕ} (derived : Bool)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived (ClosureCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun _ hf =>
    chevField_closure A K _ (fun σ h hh => chevH_stable A K derived σ h hh) hf⟩⟩

theorem recG2Derived_closure (Q : LargeEvenRawCont) (h : LargeEvenRecipeG2Derived Q) :
    LargeEvenRecipeG2Derived (ClosureCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun _ hf =>
    chevField_closure LargeEvenCartanG2 K _
      (fun σ h hh => chevH_stable LargeEvenCartanG2 K true σ h hh) hf⟩⟩

theorem recTwisted_closure {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r))
    (m n : ℕ) (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n (ClosureCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun _ hf =>
    chevField_closure A K _ (fun σ h hh => twisted_map_mem A K ρ n σ h hh) hf⟩⟩

theorem recSuzuki_closure {a : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a (ClosureCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun _ hf =>
    matField_closure _ (fun σ g hg => sz_map_mem σ g hg) _ hf⟩⟩

theorem recTwF4Inherited_closure (a : ℕ) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a (ClosureCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, fun _ hf =>
    chevField_closure LargeEvenCartanF4 K _
      (fun σ h hh => twF4H_map_mem K a σ h hh) hf⟩⟩

theorem canonAll_closure_field_exc {lab : LargeEvenLabel}
    (hfam : CFSG.LocalAnalysis.GLTheoremA.Y10GField.FamExc lab) :
    CFSG.StandardType.Canonical.LargeEvenLabelAll lab
      (fun R _ _ F => ∀ f ∈ Subgroup.closure F, f ∈ F) := by
  intro Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  simp only [CFSG.LocalAnalysis.GLTheoremA.Y10GField.FamExc] at hfam
  rcases hfam with h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact recChevalley_closure (LargeEvenCartanE 6) false _ hQ
  · subst h; exact recChevalley_closure (LargeEvenCartanE 7) false _ hQ
  · subst h; exact recChevalley_closure (LargeEvenCartanE 8) false _ hQ
  · subst h; exact recChevalley_closure LargeEvenCartanF4 false _ hQ
  · subst h; exact recTwisted_closure (LargeEvenCartanE 6) LargeEvenRhoE6 2 n _ hQ
  · subst h; exact recTwisted_closure LargeEvenCartanD4 LargeEvenRhoD4 3 n _ hQ
  · subst h; exact recChevalley_closure LargeEvenCartanG2 false _ hQ
  · subst h; exact recG2Derived_closure _ hQ
  · subst h; exact recSuzuki_closure _ hQ
  · subst h; exact recTwF4Inherited_closure _ _ hQ
  · subst h; exact recTwF4Inherited_closure _ _ hQ

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc