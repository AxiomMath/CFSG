module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThreeEvenClassification

section LayerTransport

variable {G₀ G₁ : Type} [Group G₀] [Group G₁]

theorem closureIn_map_mulEquiv (e : G₀ ≃* G₁) (I H : Subgroup G₀) :
    (closureIn I H).map e.toMonoidHom =
      closureIn (I.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  unfold closureIn
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    have hconj : (I.map (MulAut.conj a).toMonoidHom).map e.toMonoidHom =
        (I.map e.toMonoidHom).map (MulAut.conj (e.toMonoidHom a)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      have h : e.toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (e.toMonoidHom a)).toMonoidHom.comp e.toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [h]
    rw [hconj]
    exact le_iSup₂_of_le (e.toMonoidHom a) (Subgroup.mem_map_of_mem e.toMonoidHom ha) le_rfl
  · refine iSup₂_le fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    have hconj : (I.map (MulAut.conj a).toMonoidHom).map e.toMonoidHom =
        (I.map e.toMonoidHom).map (MulAut.conj (e.toMonoidHom a)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      have h : e.toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (e.toMonoidHom a)).toMonoidHom.comp e.toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [h]
    rw [← hconj]
    exact Subgroup.map_mono (le_iSup₂_of_le a ha le_rfl)

theorem stdLayer_map_mulEquiv (e : G₀ ≃* G₁) (d : G₀) :
    stdLayer (e d) = (stdLayer d).map e.toMonoidHom := by
  unfold stdLayer
  rw [← CFSG.centralizer_singleton_map e d]
  exact Y10F.glaLayer_map e.injective _

theorem centralizer_stdLayer_map_mulEquiv (e : G₀ ≃* G₁) (d : G₀) :
    Subgroup.centralizer (stdLayer (e d) : Set G₁) =
      (Subgroup.centralizer (stdLayer d : Set G₀)).map e.toMonoidHom := by
  rw [stdLayer_map_mulEquiv]
  exact (CFSG.RankThreeEvenClassification.Helpers.centralizer_map_equiv e (stdLayer d)).symm

theorem innerClosure_map_mulEquiv (e : G₀ ≃* G₁) (A : Subgroup G₀) (d : G₀) :
    (innerClosure A d).map e.toMonoidHom = innerClosure (A.map e.toMonoidHom) (e d) := by
  unfold innerClosure
  rw [closureIn_map_mulEquiv, ← stdLayer_map_mulEquiv, Subgroup.map_equiv_normalizer_eq]

end LayerTransport

section Std

variable {G₀ G₁ : Type} [Group G₀] [Group G₁]

theorem isStdElt_map (e : G₀ ≃* G₁) {p : ℕ} {A : Subgroup G₀} {d : G₀}
    (h : IsStdElt p A d) : IsStdElt p (A.map e.toMonoidHom) (e d) := by
  obtain ⟨hdA, hd1, hdp, hcomp, hcent⟩ := h
  refine ⟨Subgroup.mem_map_of_mem e.toMonoidHom hdA, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hd1 (e.injective (by simpa using h1))
  · rw [← map_pow, hdp, map_one]
  · rw [stdLayer_map_mulEquiv, ← CFSG.centralizer_singleton_map e d]
    exact (Y10F.isComponentOf_map_iff e.injective).2 hcomp
  · have hmap : (A.map e.toMonoidHom ⊓
        Subgroup.centralizer (stdLayer (e d) : Set G₁)) =
        (A ⊓ Subgroup.centralizer (stdLayer d : Set G₀)).map e.toMonoidHom := by
      rw [centralizer_stdLayer_map_mulEquiv]
      exact (Subgroup.map_inf_eq A (Subgroup.centralizer (stdLayer d : Set G₀))
        (f := e.toMonoidHom) e.injective).symm
    rw [hmap, hcent, MonoidHom.map_zpowers]
    rfl

theorem isStdElt_map_iff {G₀ G₁ : Type} [Group G₀] [Group G₁] (e : G₀ ≃* G₁) {p : ℕ}
    {A : Subgroup G₀} {d : G₀} :
    IsStdElt p (A.map e.toMonoidHom) (e d) ↔ IsStdElt p A d := by
  constructor
  · intro h
    have h' := isStdElt_map e.symm h
    rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm e A,
      e.symm_apply_apply] at h'
  · exact isStdElt_map e

end Std

section Outcomes

variable {G₀ G₁ : Type} [Group G₀] [Group G₁]

theorem stdVanishes_of_map (e : G₀ ≃* G₁) {A : Subgroup G₀} {d : G₀}
    (h : StdVanishes (A.map e.toMonoidHom) (e d)) : StdVanishes A d := by
  rintro ⟨T, hTne, hT2, hTN⟩
  refine h ⟨T.map e.toMonoidHom, ?_, hT2.map _, ?_⟩
  · intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective T (f := e.toMonoidHom) e.injective).mp hbot)
  · have hmap := Subgroup.map_mono (f := e.toMonoidHom) hTN
    rwa [Subgroup.map_sup, innerClosure_map_mulEquiv,
      Subgroup.map_equiv_normalizer_eq] at hmap

theorem stdVanishes_map_iff {G₀ G₁ : Type} [Group G₀] [Group G₁] (e : G₀ ≃* G₁) {A : Subgroup G₀}
    {d : G₀} :
    StdVanishes (A.map e.toMonoidHom) (e d) ↔ StdVanishes A d := by
  constructor
  · exact stdVanishes_of_map e
  · intro h
    have h' : StdVanishes ((A.map e.toMonoidHom).map e.symm.toMonoidHom) (e.symm (e d)) := by
      rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm e A,
        e.symm_apply_apply]
    exact stdVanishes_of_map e.symm h'

theorem stdExtendsN_map (e : G₀ ≃* G₁) {p : ℕ} {A : Subgroup G₀} {d : G₀}
    (h : StdExtendsN p A d) : StdExtendsN p (A.map e.toMonoidHom) (e d) := by
  obtain ⟨⟨T, hTne, hT2, hTK, hAsplit⟩, y, hyA, hyK, hyp, hyAnot⟩ := h
  refine ⟨⟨T.map e.toMonoidHom, ?_, hT2.map _, ?_, ?_⟩, e y, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective T (f := e.toMonoidHom) e.injective).mp hbot)
  · rw [stdLayer_map_mulEquiv]
    exact Subgroup.map_mono hTK
  · calc A.map e.toMonoidHom
        = ((A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.normalizer (T : Set G₀))).map e.toMonoidHom :=
          congrArg (fun B : Subgroup G₀ => B.map e.toMonoidHom) hAsplit
      _ = (A ⊓ stdLayer d).map e.toMonoidHom ⊔
            (A ⊓ Subgroup.normalizer (T : Set G₀)).map e.toMonoidHom := Subgroup.map_sup ..
      _ = (A.map e.toMonoidHom ⊓ stdLayer (e d)) ⊔
            (A.map e.toMonoidHom ⊓ Subgroup.normalizer (T.map e.toMonoidHom : Set G₁)) := by
          rw [Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.map_inf_eq _ _ _ e.injective,
            stdLayer_map_mulEquiv, Subgroup.map_equiv_normalizer_eq]
  · rw [Subgroup.mem_centralizer_iff] at hyA ⊢
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    change e w * e y = e y * e w
    simpa only [map_mul] using congrArg e (hyA w hw)
  · rw [Subgroup.mem_centralizer_iff] at hyK ⊢
    intro z hz
    rw [stdLayer_map_mulEquiv] at hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    change e w * e y = e y * e w
    simpa only [map_mul] using congrArg e (hyK w hw)
  · rw [← map_pow, hyp, map_one]
  · intro hmem
    exact hyAnot (by
      simpa using ((Subgroup.mem_map_equiv (f := e) (K := A)).mp hmem))

theorem stdExtendsN_map_iff {G₀ G₁ : Type} [Group G₀] [Group G₁] (e : G₀ ≃* G₁) {p : ℕ}
    {A : Subgroup G₀} {d : G₀} :
    StdExtendsN p (A.map e.toMonoidHom) (e d) ↔ StdExtendsN p A d := by
  constructor
  · intro h
    have h' := stdExtendsN_map e.symm h
    rwa [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_equiv_symm e A,
      e.symm_apply_apply] at h'
  · exact stdExtendsN_map e

end Outcomes

theorem modelFactV_of_frame {p : ℕ} {G₀ : Type} [Group G₀] [Finite G₀] (V : Subgroup G₀)
    (hframe : ∀ A : Subgroup G₀, GLAIsBmax p A → ∃ g : G₀, A.map (MulAut.conj g).toMonoidHom = V)
    (hV : ∀ d : G₀, IsStdElt p V d → StdVanishes V d) : ModelFactV p G₀ := by
  intro A d hA hd
  obtain ⟨g, hg⟩ := hframe A hA
  have hd' : IsStdElt p V ((MulAut.conj g) d) := by
    rw [← hg]
    exact (isStdElt_map_iff (MulAut.conj g)).2 hd
  have hv := hV ((MulAut.conj g) d) hd'
  exact (stdVanishes_map_iff (MulAut.conj g)).1 (by rwa [hg])

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
