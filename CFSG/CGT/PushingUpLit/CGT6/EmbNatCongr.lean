module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

theorem isNatSectionWith_of_equiv {V : Type} [CommGroup V] {k : ℕ} (hk5 : 5 ≤ k) (hk6 : k ≠ 6)
    {K : Subgroup (MulAut V)} {P Z : Subgroup V} (θ θ' : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ P Z) : IsNatSectionWith (altAct k) θ' P Z := by
  obtain ⟨hinv, β, hβs, hβk, hβe⟩ := h
  obtain ⟨τ, hτ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k hk5 hk6).2
    (θ.symm.trans θ')
  have hτ' : ∀ y : K, ((θ' y : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) =
      τ * ((θ y : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) * τ⁻¹ := by
    intro y
    have h1 := congrArg (fun e : MulAut (alternatingGroup (Fin k)) => e (θ y)) hτ
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [← h1]
    rfl
  let γ : ↥(G6.coreMod k) →* ↥(G6.coreMod k) := (G6.coreAct k τ).toMonoidHom
  have hγ : Function.Bijective γ := (G6.coreAct k τ).bijective
  refine ⟨hinv, γ.comp β, hγ.2.comp hβs, ?_, ?_⟩
  · rw [← hβk]
    ext p
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (map_eq_one_iff γ hγ.1)
  · intro y p hp
    have h1 := hβe y p hp
    show γ (β ⟨(y : MulAut V) p, hp⟩) = altAct k (θ' y) (γ (β p))
    rw [h1]
    show G6.coreAct k τ (G6.coreAct k _ (β p)) =
      G6.coreAct k ((θ' y : alternatingGroup (Fin k)) : Equiv.Perm (Fin k))
        (G6.coreAct k τ (β p))
    rw [hτ' y, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

end CFSG.CGT.PushingUpLit.CGT6
