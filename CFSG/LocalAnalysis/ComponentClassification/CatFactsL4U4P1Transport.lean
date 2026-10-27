module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup

variable {S S' : Type} [Group S] [Group S']

theorem map_oddPart (e : S ≃* S') (H : Subgroup S) :
    (Q81.oddPart H).map e.toMonoidHom = Q81.oddPart (H.map e.toMonoidHom) := by
  rw [Q81.oddPart, Q81.oddPart, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hodd⟩, rfl⟩

theorem map_centralizer_singleton (e : S ≃* S') (s : S) :
    (centralizer ({s} : Set S)).map e.toMonoidHom = centralizer ({e s} : Set S') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff]
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem card_map_equiv (e : S ≃* S') (H : Subgroup S) :
    Nat.card ↥(H.map e.toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective e.injective

theorem P1ModelFacts.of_mulEquiv (e : S ≃* S') (h : P1ModelFacts S') : P1ModelFacts S := by
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs' : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq, hs]
    have hc : Nat.card ↥(Q81.oddPart (centralizer ({e s} : Set S'))) =
        Nat.card ↥(Q81.oddPart (centralizer ({s} : Set S))) := by
      rw [← map_centralizer_singleton, ← map_oddPart, card_map_equiv]
    rw [← hc]
    exact h.inner (e s) hs'
  · intro α β L ℓ hα hβ hαβ hL hLα hLn hℓ hℓ2 h8
    set α' := MulAut.congr e α
    set β' := MulAut.congr e β
    have hα' : orderOf α' = 2 := by rw [MulEquiv.orderOf_eq, hα]
    have hβ' : orderOf β' = 2 := by rw [MulEquiv.orderOf_eq, hβ]
    have hαβ' : α' * β' = β' * α' := by rw [← map_mul, ← map_mul, hαβ]
    have hcongr : ∀ (γ : MulAut S) (y : S), MulAut.congr e γ (e y) = e (γ y) := fun γ y => by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hconj : MulAut.congr e (MulAut.conj ℓ) = MulAut.conj (e ℓ) := by
      ext y
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    have h8' : orderOf (β' * MulAut.conj (e ℓ)) = 8 := by
      rw [← hconj, ← map_mul, MulEquiv.orderOf_eq, h8]
    obtain ⟨M', hM'β, hM'n, ⟨eA⟩⟩ := h.aut α' β' (L.map e.toMonoidHom) (e ℓ) hα' hβ' hαβ'
      (by rw [card_map_equiv, hL])
      (by
        rintro _ ⟨y, hy, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hcongr, hLα y hy])
      (by
        rintro c hc _ ⟨y, hy, rfl⟩
        have hc' : α (e.symm c) = e.symm c := by
          apply e.injective
          rw [← hcongr, MulEquiv.apply_symm_apply, hc]
        refine ⟨e.symm c * y * (e.symm c)⁻¹, hLn _ hc' y hy, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply])
      ⟨ℓ, hℓ, rfl⟩ (by rw [MulEquiv.orderOf_eq, hℓ2]) h8'
    refine ⟨M'.map e.symm.toMonoidHom, ?_, ?_,
      ⟨(M'.equivMapOfInjective _ e.symm.injective).symm.trans eA⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      apply e.injective
      rw [MulEquiv.coe_toMonoidHom, ← hcongr, MulEquiv.apply_symm_apply, hM'β y hy]
    · rintro c hc _ ⟨y, hy, rfl⟩
      have hc' : β' (e c) = e c := by rw [hcongr, hc]
      refine ⟨e c * y * (e c)⁻¹, hM'n _ hc' y hy, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end CFSG.ComponentClassification.HarrisLit.P1
