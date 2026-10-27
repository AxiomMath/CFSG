module

public import CFSG.GH74.QTGen4.U42.ModelExtCoords

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut

@[expose] def extAlignTau : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem extAlignTau_facts :
    extAlignTau.sign = 1 ∧ extAlignTau 0 = 0 ∧ extAlignTau 4 = 4 ∧ extAlignTau⁻¹ 4 = 4 ∧
    extAlignTau * (sigma0 * Equiv.swap 3 4 * sigma0⁻¹) * extAlignTau⁻¹ = Equiv.swap 0 1 := by
  decide +kernel

theorem extAlign_K4 (σ : Equiv.Perm (Fin 5)) :
    InK4 (extAlignTau * σ * extAlignTau⁻¹) ↔ InK4 σ := by
  constructor
  · intro h
    have hi : extAlignTau⁻¹.sign = 1 := by rw [Equiv.Perm.sign_inv, extAlignTau_facts.1]
    have := InK4_conj extAlignTau⁻¹ _ extAlignTau_facts.2.2.2.1 hi h
    simpa [mul_assoc] using this
  · exact InK4_conj extAlignTau σ extAlignTau_facts.2.2.1 extAlignTau_facts.1

theorem extAlign_fix_four (σ : Equiv.Perm (Fin 5)) :
    (extAlignTau * σ * extAlignTau⁻¹) 4 = 4 ↔ σ 4 = 4 := by
  simp only [Equiv.Perm.mul_apply, extAlignTau_facts.2.2.2.1]
  constructor
  · intro h
    exact extAlignTau.injective (h.trans extAlignTau_facts.2.2.1.symm)
  · intro h
    rw [h, extAlignTau_facts.2.2.1]

@[expose] def extAlignAut : Mc ≃* Mc := MulAut.conj (SemidirectProduct.inr extAlignTau)

theorem extAlignAut_left (x : Mc) : (extAlignAut x).left = pact extAlignTau x.left := by
  simp [extAlignAut, MulAut.conj_apply, SemidirectProduct.mul_left]

theorem extAlignAut_right (x : Mc) :
    (extAlignAut x).right = extAlignTau * x.right * extAlignTau⁻¹ := by
  simp [extAlignAut, MulAut.conj_apply]

theorem extAlignAut_inl (w : W5) :
    extAlignAut (SemidirectProduct.inl w) = SemidirectProduct.inl (pact extAlignTau w) := by
  apply SemidirectProduct.ext
  · exact extAlignAut_left _
  · simp [extAlignAut_right]

@[expose] def extAlignTop : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃*
    Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) where
  toFun x := ⟨extAlignAut (x : Mc), mem_Mof.mpr (Subgroup.mem_top _)⟩
  invFun x := ⟨extAlignAut.symm (x : Mc), mem_Mof.mpr (Subgroup.mem_top _)⟩
  left_inv x := Subtype.ext (extAlignAut.symm_apply_apply _)
  right_inv x := Subtype.ext (extAlignAut.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul extAlignAut (x : Mc) (y : Mc))

@[expose] noncomputable def extAlignedPerm (g : ↥P2h) : Equiv.Perm (Fin 5) :=
  extAlignTau * permHat4 g * extAlignTau⁻¹

theorem extAlignedPerm_fhat :
    extAlignedPerm ⟨fhatA, fhatA_mem_P2h⟩ = Equiv.swap 0 1 := by
  rw [extAlignedPerm, permHat4, permHat_fhat]
  exact extAlignTau_facts.2.2.2.2

theorem exists_model_coords_aligned :
    ∃ e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))),
      (∀ (v : Ah) (hv : v ∈ VA),
        ((e ⟨v, VA_le_P2h hv⟩ : Mof _) : Mc) =
          SemidirectProduct.inl (pact (extAlignTau * sigma0) (psiHat ⟨v, hv⟩))) ∧
      ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g := by
  obtain ⟨e, heV, heR⟩ := exists_model_coords_extension
  let e' := e.trans extAlignTop
  refine ⟨e', ?_, ?_⟩
  · intro v hv
    change extAlignAut ((e ⟨v, VA_le_P2h hv⟩ : Mof _) : Mc) = _
    rw [heV, extAlignAut_inl, map_mul, MulAut.mul_apply]
  · intro g
    change (extAlignAut ((e g : Mof _) : Mc)).right = _
    rw [extAlignAut_right, heR]
    rfl

end CFSG.GH74.QTGen4.U42
