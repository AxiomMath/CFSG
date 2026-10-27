module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSym

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open Subgroup

@[expose] noncomputable def hatAut {A : Type} [Group A] (P : Subgroup A) {t : A}
    (htP : t ∈ Subgroup.normalizer (P : Set A)) :
    (↥P ⧸ CFSG.pCore 2 ↥P) ≃* (↥P ⧸ CFSG.pCore 2 ↥P) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥P) (CFSG.pCore 2 ↥P)
    (P.normalizerMonoidHom ⟨t, htP⟩ : ↥P ≃* ↥P)
    (CFSG.pCore_map_iso 2 (P.normalizerMonoidHom ⟨t, htP⟩ : ↥P ≃* ↥P))

theorem hatAut_mk {A : Type} [Group A] (P : Subgroup A) {t : A}
    (htP : t ∈ Subgroup.normalizer (P : Set A)) (x : ↥P) :
    hatAut P htP (QuotientGroup.mk x) =
      QuotientGroup.mk (P.normalizerMonoidHom ⟨t, htP⟩ x) := rfl

theorem hatOf_map_conj {A : Type} [Group A] {P J : Subgroup A} {t : A} (hJP : J ≤ P)
    (htP : t ∈ Subgroup.normalizer (P : Set A)) :
    hatOf P (J.map (MulAut.conj t).toMonoidHom) = (hatOf P J).map (hatAut P htP).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := hx
    have hjP : j ∈ P := hJP hj
    refine ⟨QuotientGroup.mk ⟨j, hjP⟩, ⟨⟨j, hjP⟩, hj, rfl⟩, ?_⟩
    show hatAut P htP (QuotientGroup.mk ⟨j, hjP⟩) = QuotientGroup.mk' _ x
    rw [hatAut_mk]
    congr 1
    apply Subtype.ext
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hjx
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨P.normalizerMonoidHom ⟨t, htP⟩ y, ⟨(y : A), hy, ?_⟩, ?_⟩
    · simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    · rfl

theorem hatOf_map_conj_symThree {A : Type} [Group A] {P J : Subgroup A} {t : A} (hJP : J ≤ P)
    (htP : t ∈ Subgroup.normalizer (P : Set A)) (hJs : IsSubnormal (hatOf P J) ⊤)
    (hJiso : Sym.IsSymThree (hatOf P J)) :
    IsSubnormal (hatOf P (J.map (MulAut.conj t).toMonoidHom)) ⊤ ∧
      Sym.IsSymThree (hatOf P (J.map (MulAut.conj t).toMonoidHom)) := by
  rw [hatOf_map_conj hJP htP]
  refine ⟨?_, ?_⟩
  · have h := hJs.map (hatAut P htP).toMonoidHom
    have h2 : (⊤ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)).map (hatAut P htP).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective (hatAut P htP).toMonoidHom (hatAut P htP).surjective
    rwa [h2] at h
  · obtain ⟨e⟩ := hJiso
    exact ⟨(Subgroup.equivMapOfInjective _ (hatAut P htP).toMonoidHom
      (hatAut P htP).injective).symm.trans e⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
