module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Witt

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def leviV (a b a' b' : V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure ({g | ∃ c : K, g = eichler Q a (c • b')} ∪ {g | ∃ c : K, g = eichler Q b (c • a')})

variable (Q) in
@[expose] def levi (A B : HypPair Q) : Subgroup (V ≃ₗ[K] V) := leviV Q A.e B.e A.f B.f

theorem leviV_map_conj {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (a b a' b' : V) :
    (leviV Q a b a' b').map (MulAut.conj g).toMonoidHom = leviV Q (g a) (g b) (g a') (g b') := by
  rw [leviV, leviV, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_union, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Or.inl ⟨c, by rw [eichler_conj hg, map_smul]⟩
    · exact Or.inr ⟨c, by rw [eichler_conj hg, map_smul]⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨eichler Q a (c • b'), Or.inl ⟨c, rfl⟩, by rw [eichler_conj hg, map_smul]⟩
    · exact ⟨eichler Q b (c • a'), Or.inr ⟨c, rfl⟩, by rw [eichler_conj hg, map_smul]⟩

theorem exists_levi_conj (hQ : (polarBilin Q).Nondegenerate)
    {S₁ S₂ S₃ : HypPair Q} (h12 : S₁.Orth S₂) (h13 : S₁.Orth S₃) (h23 : S₂.Orth S₃)
    {T₁ T₂ : HypPair Q} (hT : T₁.Orth T₂) :
    ∃ g ∈ elementaryGroup Q,
      levi Q T₁ T₂ = (levi Q S₁ S₂).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg, h1, h2, h3, h4⟩ := exists_mem_elementaryGroup_two hQ h12 h13 h23 hT
  refine ⟨g, hg, ?_⟩
  rw [levi, levi, leviV_map_conj (elementaryGroup_le_orthogonalGroup Q hg), h1, h2, h3, h4]

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
