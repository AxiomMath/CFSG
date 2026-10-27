module

public import CFSG.CGT.T75E.Excl
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75

variable {K K' : Type} [Group K] [Group K']

theorem classD_map_mulEquiv (e : K ≃* K') (T : Subgroup K) :
    classD (T.map e.toMonoidHom) = e '' classD T := by
  ext x
  constructor
  · rintro ⟨g, t, ht, ht1, rfl⟩
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
    refine ⟨(e.symm g)⁻¹ * t₀ * e.symm g, ⟨e.symm g, t₀, ht₀, fun h => ht1 (by simp [h]), rfl⟩, ?_⟩
    simp
  · rintro ⟨y, ⟨g, t, ht, ht1, rfl⟩, rfl⟩
    exact ⟨e g, e t, Subgroup.mem_map_of_mem _ ht, fun h => ht1 (e.injective (by simpa using h)),
      by simp⟩

theorem isRootInvolutionSet_image (e : K ≃* K') {D : Set K}
    (h : CFSG.Timmesfeld.IsRootInvolutionSet D) :
    CFSG.Timmesfeld.IsRootInvolutionSet (e '' D) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [MulEquiv.orderOf_eq]
    exact h1 d hd
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h2 d hd d' hd'
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩ h4
    rw [← map_mul, MulEquiv.orderOf_eq] at h4
    exact ⟨_, h3 d hd d' hd' h4, by rw [map_pow, map_mul]⟩

theorem lemma26Hyp_map_mulEquiv (e : K ≃* K') {T : Subgroup K} (h : Lemma26Hyp K T) :
    Lemma26Hyp K' (T.map e.toMonoidHom) := by
  obtain ⟨hT, h2, ⟨d₀, hd₀⟩, hroot, hgen⟩ := h
  refine ⟨hT.map_mulEquiv e, ?_, ⟨e d₀, ?_⟩, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rw [classD_map_mulEquiv, hd₀]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact MonoidHom.map_isConj e.toMonoidHom hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      simpa using MonoidHom.map_isConj e.symm.toMonoidHom hx
  · rw [classD_map_mulEquiv]
    exact isRootInvolutionSet_image e hroot
  · rw [classD_map_mulEquiv]
    have hmap := MonoidHom.map_closure e.toMonoidHom (classD T)
    rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    exact hmap.symm

theorem lemma26Nondeg_map_mulEquiv (e : K ≃* K') {T : Subgroup K} (h : Lemma26Nondeg T) :
    Lemma26Nondeg (T.map e.toMonoidHom) := by
  obtain ⟨d, hd, d', hd', h4⟩ := h
  rw [Lemma26Nondeg, classD_map_mulEquiv]
  exact ⟨e d, ⟨d, hd, rfl⟩, e d', ⟨d', hd', rfl⟩, by rw [← map_mul, MulEquiv.orderOf_eq]; exact h4⟩

end CFSG.CGT.T75E
