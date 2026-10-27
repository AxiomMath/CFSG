module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG Subgroup GSThmB
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag

theorem layerIn_eq_layerOf {H : Type*} [Group H] (X : Subgroup H) : layerIn X = layerOf X := by
  apply le_antisymm
  · rw [layerIn, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hLX : (L.map X.subtype).subgroupOf X = L :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective L
    exact le_layerOf (Subgroup.map_subtype_le L) (by rw [hLX]; exact hL)
  · refine sSup_le fun M ⟨hMX, hM⟩ => ?_
    have hMeq : (M.subgroupOf X).map X.subtype = M := by
      rw [subgroupOf_map_subtype, inf_of_le_left hMX]
    rw [← hMeq, layerIn]
    exact map_mono (le_sSup hM)

theorem fixSubgroup_eq_fixOf {Y : Type*} [Group Y] (e : MulAut Y) :
    Eight.fixSubgroup e = fixOf e := by
  ext x
  rfl

theorem cfSp4Layer : CFSp4Layer := by
  intro K₀ _ _ p f hp hp2 hf h5 hK₀ ε hε α hα2 R R₁ hRE hRn hR₁R hR₁n hR₁o hR2 hidx
  rcases hK₀ with hK₀ | ⟨rfl, rfl, -⟩
  swap
  · norm_num at h5
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  set Φ := MulAut.congr e with hΦ
  set ε' := Φ ε with hε'
  have hcommε : ∀ x, e (ε x) = ε' (e x) := fun x => by
    simp [hε', hΦ, MulAut.congr_apply]
  have hε'2 : ε' * ε' = 1 := by rw [hε', ← map_mul, hε.sq, map_one]
  have hout : ε' ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨u, hu⟩
    apply hε.out
    refine ⟨e.symm u, ?_⟩
    apply Φ.injective
    rw [← hε', ← hu]
    ext x
    simp [hΦ, MulAut.congr_apply, MulAut.conj_apply]
  have hfixε : Nat.card (fixOf ε') = Nat.card (Eight.fixSubgroup ε) := by
    rw [fixSubgroup_eq_fixOf, ← map_fixOf_of_comm hcommε]
    exact (Nat.card_congr ((fixOf ε).equivMapOfInjective _ e.injective).toEquiv).symm
  obtain ⟨B, hBε, d, hd0, hdsq, -, hμB⟩ :=
    exists_typeII_of_admissible hp hp2 hf hK ε' hε'2 hout (hfixε ▸ hε.dvd)
  have hmB : (multiplierUnit B : K) = d := by
    have h1 := multiplierUnit_spec B
    rw [hμB] at h1
    exact (smul_formJ_injective 2 h1).symm
  have hB : ∀ l : K, l ^ 2 ≠ (multiplierUnit B : K) := by rw [hmB]; exact hdsq
  set α' := Φ α with hα'
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by
    simp [hα', hΦ, MulAut.congr_apply]
  have hα'2 : α' * α' = 1 := by rw [hα', ← map_mul, hα2, map_one]
  rw [fixSubgroup_eq_fixOf, layerIn_eq_layerOf] at hRE hRn hidx ⊢
  set E := layerOf (fixOf α) with hE
  have hEmap : E.map e.toMonoidHom = layerOf (fixOf α') := by
    rw [hE, map_layerOf, map_fixOf_of_comm hcomm]
  have hR'E := map_mono (f := e.toMonoidHom) hRE
  rw [hEmap] at hR'E
  have hR'n := normal_subgroupOf_map e hRE hRn
  rw [hEmap] at hR'n
  have hidx' : (R.map e.toMonoidHom).relIndex (layerOf (fixOf α')) ≤
      p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [← hEmap, relIndex_map_equiv e hRE]
    exact hidx
  obtain ⟨hrel, y', hy'I, hy'α, hy'E, hy'o⟩ := layer_P hp hp2 hf hK h5 hs B hB α' hα'2 hR'E hR'n
    (map_mono hR₁R) (normal_subgroupOf_map e hR₁R hR₁n)
    (by rw [card_map_equiv]; exact hR₁o)
    (by
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨k, hk⟩ := hR2 r hr
      exact ⟨k, by rw [← map_pow]; exact mem_map_of_mem _ hk⟩) hidx'
  refine ⟨?_, Φ.symm y', ?_, ?_, ?_, ?_⟩
  · rw [← relIndex_map_equiv e hRE, hEmap]
    exact hrel
  ·
    have hle : (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range ⊔ zpowers ε' ≤
        (Cat8.Inn K₀ ⊔ zpowers ε).map Φ.toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨u, rfl⟩
        refine ⟨MulAut.conj (e.symm u), mem_sup_left ⟨e.symm u, rfl⟩, ?_⟩
        ext x
        simp [hΦ, MulAut.congr_apply, MulAut.conj_apply]
      · rw [zpowers_le]
        exact ⟨ε, mem_sup_right (mem_zpowers ε), rfl⟩
    rw [← hBε] at hy'I
    obtain ⟨z, hz, hzy⟩ := hle hy'I
    have : Φ.symm y' = z := by
      rw [← hzy]
      simp
    rw [this]
    exact hz
  · apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hα', hy'α]
  · intro t ht
    have h1 := hy'E (e t) (by rw [← hEmap]; exact mem_map_of_mem _ ht)
    simp only [hΦ, MulAut.congr_symm_apply, MulEquiv.trans_apply]
    rw [h1, MulEquiv.symm_apply_apply]
  · rw [MulEquiv.orderOf_eq]
    rcases hy'o with h | ⟨h1, h1'⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, fun h => h1' ?_⟩
      have := congrArg Φ h
      rwa [MulEquiv.apply_symm_apply, map_one] at this

end CFSG.ComponentClassification.CatFactsSp4
