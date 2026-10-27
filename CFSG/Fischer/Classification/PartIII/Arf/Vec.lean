module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.Uniqueness.Abstract

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} {S : Type*}

namespace Arf

theorem bijective_reflBar_of_vec (hf : IsF3Form f) (hm : 4 ≤ m) (σ : S → Fin m → ZMod 3)
    (hσ : ∀ s, f (σ s) (σ s) = 1) (hinj : ∀ s s', σ s' = σ s ∨ σ s' = -σ s → s' = s)
    (hsurj : ∀ u, f u u = 1 → ∃ s, σ s = u ∨ σ s = -u) :
    Function.Bijective fun s => (⟨reflBar f (σ s), reflBar_mem_D3 (hσ s)⟩ : D3 f) := by
  constructor
  · intro s s' h
    have h' := congrArg Subtype.val h
    simp only at h'
    rw [reflBar_eq_reflBar_iff hf hm (hσ s) (hσ s')] at h'
    exact (hinj s s' h').symm
  · rintro ⟨q, hq⟩
    obtain ⟨u, hu, rfl⟩ := mem_D3_iff.1 hq
    obtain ⟨s, hs⟩ := hsurj u hu
    refine ⟨s, Subtype.ext ?_⟩
    rcases hs with hs | hs <;> simp only [hs, reflBar_neg]

@[expose] noncomputable def reflEquivOfVec (hf : IsF3Form f) (hm : 4 ≤ m)
    (σ : S → Fin m → ZMod 3) (hσ : ∀ s, f (σ s) (σ s) = 1)
    (hinj : ∀ s s', σ s' = σ s ∨ σ s' = -σ s → s' = s)
    (hsurj : ∀ u, f u u = 1 → ∃ s, σ s = u ∨ σ s = -u) : S ≃ D3 f :=
  Equiv.ofBijective _ (bijective_reflBar_of_vec hf hm σ hσ hinj hsurj)

theorem coe_reflEquivOfVec (hf : IsF3Form f) (hm : 4 ≤ m) (σ : S → Fin m → ZMod 3)
    (hσ : ∀ s, f (σ s) (σ s) = 1) (hinj : ∀ s s', σ s' = σ s ∨ σ s' = -σ s → s' = s)
    (hsurj : ∀ u, f u u = 1 → ∃ s, σ s = u ∨ σ s = -u) (s : S) :
    (reflEquivOfVec hf hm σ hσ hinj hsurj s : R3 f) = reflBar f (σ s) :=
  rfl

theorem reflBar_eq_conj_of_eq_or (hf : IsF3Form f) {u w z : Fin m → ZMod 3}
    (h : z = act (refl f u) w ∨ z = -act (refl f u) w) :
    reflBar f z = reflBar f u * reflBar f w * reflBar f u := by
  rw [reflBar_conj hf]
  rcases h with rfl | rfl
  · rfl
  · exact reflBar_neg _

end Arf

theorem exists_mulEquiv_R3_of_vec {X : Type} [Group X] {E : Set X} (hE : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hf : IsF3Form f) (hm : 4 ≤ m) (σ : E → Fin m → ZMod 3)
    (hσ : ∀ e, f (σ e) (σ e) = 1) (hinj : ∀ e e', σ e' = σ e ∨ σ e' = -σ e → e' = e)
    (hsurj : ∀ u, f u u = 1 → ∃ e, σ e = u ∨ σ e = -u)
    (hτ : ∀ d e, σ (tauE hE d e) = act (refl f (σ d)) (σ e) ∨
      σ (tauE hE d e) = -act (refl f (σ d)) (σ e)) :
    ∃ φ : X ≃* R3 f, (∀ e : E, φ e = reflBar f (σ e)) ∧ φ '' E = D3 f := by
  let β := Arf.reflEquivOfVec hf hm σ hσ hinj hsurj
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_tau_eq hE (pair_R3 hf hm) hZ (center_R3_eq_bot hf hm) β
    fun d e => Subtype.ext (by
      rw [tauE_coe, Arf.coe_reflEquivOfVec, Arf.coe_reflEquivOfVec, Arf.coe_reflEquivOfVec]
      exact Arf.reflBar_eq_conj_of_eq_or hf (hτ d e))
  exact ⟨φ, hφ, image_eq_of_forall_eq β hφ⟩

end CFSG.Fischer.Classification
