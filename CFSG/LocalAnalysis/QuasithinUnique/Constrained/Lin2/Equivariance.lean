module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem IsElemAbelian.mono {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem IsElemAbelian.comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) :=
  CFSG.Open.isElemAbelian_bot _

theorem isElemAbelian_map_equiv_iff (f : G ≃* G) (A : Subgroup G) :
    IsElemAbelian 2 (A.map f.toMonoidHom) ↔ IsElemAbelian 2 A := by
  constructor
  · intro h
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have := IsElemAbelian.comm h (Subgroup.mem_map_of_mem f.toMonoidHom a.2)
        (Subgroup.mem_map_of_mem f.toMonoidHom b.2)
      apply f.injective
      simpa using this
    · have := h.2 (f x) (Subgroup.mem_map_of_mem f.toMonoidHom hx)
      apply f.injective
      simpa using this
  · intro h
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      have := IsElemAbelian.comm h ha' hb'
      change (a : G) * b = b * a
      rw [← ha, ← hb]
      simpa using congrArg f this
    · rintro _ ⟨x, hx, rfl⟩
      have := h.2 x hx
      simpa using congrArg f this

theorem isMaxElemAbelian_map_equiv_of (f : G ≃* G) {S A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian (S.map f.toMonoidHom) (A.map f.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hA.1, (isElemAbelian_map_equiv_iff f A).2 hA.2.1, fun B hB hBe => ?_⟩
  have hB' : B.map f.symm.toMonoidHom ≤ S := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨s, hs, hsb⟩ := hB hb
    have : s = f.symm b := by rw [← hsb]; simp
    simpa [this] using hs
  have hBe' : IsElemAbelian 2 (B.map f.symm.toMonoidHom) :=
    (isElemAbelian_map_equiv_iff f.symm B).2 hBe
  have h1 := hA.2.2 _ hB' hBe'
  have hBB : (B.map f.symm.toMonoidHom).map f.toMonoidHom = B := map_equiv_map_equiv_symm f B
  have h2 : Nat.card B = Nat.card (B.map f.symm.toMonoidHom) := by
    conv_lhs => rw [← hBB]
    exact card_map_equiv f _
  rw [h2, card_map_equiv f A]
  exact h1

theorem isMaxElemAbelian_map_equiv_iff (f : G ≃* G) (S A : Subgroup G) :
    IsMaxElemAbelian (S.map f.toMonoidHom) (A.map f.toMonoidHom) ↔ IsMaxElemAbelian S A := by
  refine ⟨fun h => ?_, isMaxElemAbelian_map_equiv_of f⟩
  have := isMaxElemAbelian_map_equiv_of f.symm h
  rwa [map_equiv_symm_map_equiv, map_equiv_symm_map_equiv] at this

theorem thompsonJ_map_equiv (f : G ≃* G) (S : Subgroup G) :
    thompsonJ (S.map f.toMonoidHom) = (thompsonJ S).map f.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hA' : IsMaxElemAbelian S (A.map f.symm.toMonoidHom) := by
      have := isMaxElemAbelian_map_equiv_of f.symm hA
      rwa [map_equiv_symm_map_equiv] at this
    have h1 : A.map f.symm.toMonoidHom ≤ thompsonJ S := le_iSup₂_of_le _ hA' le_rfl
    have h2 := Subgroup.map_mono (f := f.toMonoidHom) h1
    rwa [map_equiv_map_equiv_symm] at h2
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le _ (isMaxElemAbelian_map_equiv_of f hA) le_rfl

theorem centerOf_map_equiv (f : G ≃* G) (X : Subgroup G) :
    centerOf (X.map f.toMonoidHom) = (centerOf X).map f.toMonoidHom := by
  unfold centerOf
  rw [centralizer_map_equiv, map_equiv_inf]

theorem omegaOneOf_map_equiv (f : G ≃* G) (X : Subgroup G) :
    omegaOneOf (X.map f.toMonoidHom) = (omegaOneOf X).map f.toMonoidHom := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy2⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply f.injective
    simpa using hy2
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hx, by simpa using congrArg f hx2⟩

theorem isElemAbelian_conjR_iff (A : Subgroup G) (g : G) :
    IsElemAbelian 2 (conjR A g) ↔ IsElemAbelian 2 A :=
  isElemAbelian_map_equiv_iff (MulAut.conj g⁻¹) A

theorem isMaxElemAbelian_conjR_iff (S A : Subgroup G) (g : G) :
    IsMaxElemAbelian (conjR S g) (conjR A g) ↔ IsMaxElemAbelian S A :=
  isMaxElemAbelian_map_equiv_iff (MulAut.conj g⁻¹) S A

theorem conjR_thompsonJ (S : Subgroup G) (g : G) :
    conjR (thompsonJ S) g = thompsonJ (conjR S g) :=
  (thompsonJ_map_equiv (MulAut.conj g⁻¹) S).symm

theorem conjR_centerOf (X : Subgroup G) (g : G) : conjR (centerOf X) g = centerOf (conjR X g) :=
  (centerOf_map_equiv (MulAut.conj g⁻¹) X).symm

theorem conjR_omegaOneOf (X : Subgroup G) (g : G) :
    conjR (omegaOneOf X) g = omegaOneOf (conjR X g) :=
  (omegaOneOf_map_equiv (MulAut.conj g⁻¹) X).symm

theorem thompsonJ_normalized {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    conjR (thompsonJ S) g = thompsonJ S := by
  rw [conjR_thompsonJ, conjR_eq_of_mem_normalizer hg]

theorem centerOf_normalized {R : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    conjR (centerOf R) g = centerOf R := by
  rw [conjR_centerOf, conjR_eq_of_mem_normalizer hg]

end CFSG.QuasithinUnique.Lin2
