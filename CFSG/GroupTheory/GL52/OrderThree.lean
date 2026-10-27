module

public import CFSG.GroupTheory.GL52.OrderThreeTwo
public import CFSG.GroupTheory.GL52.OrderThreeFour

public noncomputable section

namespace CFSG.GroupTheory.GL52

theorem isInnerDirectProduct_map {G : Type*} [Group G] {A B C : Subgroup G} (f : G →* G)
    (hf : Function.Injective f) (h : IsInnerDirectProduct A B C) :
    IsInnerDirectProduct (A.map f) (B.map f) (C.map f) := by
  obtain ⟨hsup, hinf, hcomm⟩ := h
  refine ⟨by rw [← Subgroup.map_sup, hsup], by rw [← Subgroup.map_inf_eq _ _ _ hf, hinf,
    Subgroup.map_bot], ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hcomm a ha b hb]

theorem ord3_structure {τ : G52} (hτ : orderOf τ = 3) :
    (commDim τ = 4 ∧ ∃ K : Subgroup G52,
        IsInnerDirectProduct (Subgroup.zpowers τ) K (Subgroup.centralizer {τ}) ∧
        Nonempty (K ≃* alternatingGroup (Fin 5))) ∨
    (commDim τ = 2 ∧ ∃ K : Subgroup G52,
        IsInnerDirectProduct (Subgroup.zpowers τ) K (Subgroup.centralizer {τ}) ∧
        Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∧
        Nonempty (K ≃* GL (Fin 3) (ZMod 2))) := by
  rcases ord3_classify hτ with ⟨h2, hc⟩ | ⟨h4, hc⟩
  · right
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    set f := (MulAut.conj c).toMonoidHom with hf
    have hinj : Function.Injective f := (MulAut.conj c).injective
    refine ⟨h2, ord3K2.map f, ?_, ?_, ?_⟩
    · have h := isInnerDirectProduct_map f hinj ord3_centralizer_T2
      rwa [MonoidHom.map_zpowers, hf, ← centralizer_conj] at h
    · obtain ⟨e⟩ := ord3_K2_equiv_PSL
      exact ⟨(Subgroup.equivMapOfInjective ord3K2 f hinj).symm.trans e⟩
    · obtain ⟨e⟩ := ord3_K2_equiv_GL
      exact ⟨(Subgroup.equivMapOfInjective ord3K2 f hinj).symm.trans e⟩
  · left
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    set f := (MulAut.conj c).toMonoidHom with hf
    have hinj : Function.Injective f := (MulAut.conj c).injective
    refine ⟨h4, ord3K4.map f, ?_, ?_⟩
    · have h := isInnerDirectProduct_map f hinj ord3_centralizer_T4
      rwa [MonoidHom.map_zpowers, hf, ← centralizer_conj] at h
    · obtain ⟨e⟩ := ord3_K4_equiv_alternating
      exact ⟨(Subgroup.equivMapOfInjective ord3K4 f hinj).symm.trans e⟩

end CFSG.GroupTheory.GL52
