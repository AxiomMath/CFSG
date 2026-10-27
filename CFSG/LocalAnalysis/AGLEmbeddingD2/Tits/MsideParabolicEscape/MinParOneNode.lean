module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

structure OneNode (S : Type) [Group S] (T : Subgroup S) : Prop where
  pgroup : IsPGroup 2 T
  coatom : IsCoatom (Subgroup.normalizer (T : Set S))
  ov : ∀ X : Subgroup S, T ≤ X → ¬ X ≤ Subgroup.normalizer (T : Set S) →
    pElementSubgroup 2 (⊤ : Subgroup S) ≤ X

theorem normal_pElementSubgroup_top (S : Type) [Group S] :
    (pElementSubgroup 2 (⊤ : Subgroup S)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := pElementSubgroup_map_equiv (MulAut.conj g) (⊤ : Subgroup S)
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
  have hmem : g * n * g⁻¹ ∈ (pElementSubgroup 2 (⊤ : Subgroup S)).map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, by simp⟩
  rw [← h] at hmem
  exact hmem

@[expose] noncomputable def minParData_of_oneNode {S : Type} [Group S] {T : Subgroup S}
    (hS : IsSimpleGroup S) (h : OneNode S T) : MinParData (⊤ : Subgroup S) T where
  ι := Unit
  P := fun _ => ⊤
  P_min := fun _ => by
    refine ⟨le_top, ?_, fun Q hQ1 _ => ?_⟩
    · rw [top_inf_eq]; exact lt_top_iff_ne_top.2 h.coatom.1
    · rw [top_inf_eq] at hQ1 ⊢
      rcases eq_or_lt_of_le hQ1 with e | e
      · exact Or.inl e.symm
      · exact Or.inr (h.coatom.2 _ e)
  P_all := fun A hA => ⟨(), by
    obtain ⟨-, h1, -⟩ := hA
    rw [top_inf_eq] at h1
    exact h.coatom.2 _ h1⟩
  P_inj := fun _ _ _ => Subsingleton.elim _ _
  OV := fun X hTX _ hX => ⟨(), h.ov X hTX hX⟩
  sub := fun J k hJ _ => by
    obtain ⟨j, hj⟩ := hJ
    have : j = k := Subsingleton.elim _ _
    exact this ▸ hj
  two := fun J a hJ ha h2 => by
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨m, hm⟩ := h2
    exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) => pElementSubgroup 2 (⊤ : Subgroup S)) j hj
      le_rfl (Subgroup.subset_closure ⟨Subgroup.mem_top a, m, hm⟩)
  nonnorm := fun _ hle => by
    haveI := normal_pElementSubgroup_top S
    have hT : T ≠ ⊥ := fun e => h.coatom.1 (by
      rw [e]; exact Subgroup.normalizer_eq_top_iff.2 inferInstance)
    have hne : pElementSubgroup 2 (⊤ : Subgroup S) ≠ ⊥ := by
      intro e
      apply hT
      rw [eq_bot_iff, ← e]
      exact le_pElementSubgroup_of_isPGroup le_top h.pgroup
    rcases hS.eq_bot_or_eq_top_of_normal (pElementSubgroup 2 (⊤ : Subgroup S)) with e | e
    · exact hne e
    · rw [e] at hle
      exact h.coatom.1 (eq_top_iff.2 hle)

theorem OneNode.map {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {T : Subgroup S}
    (h : OneNode S T) : OneNode S' (T.map e.toMonoidHom) where
  pgroup := h.pgroup.map _
  coatom := by
    have hN : (Subgroup.normalizer (T : Set S)).map e.toMonoidHom =
        Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup S') : Set S') :=
      Subgroup.map_equiv_normalizer_eq T e
    rw [← hN, show (Subgroup.normalizer (T : Set S)).map e.toMonoidHom =
      (Subgroup.normalizer (T : Set S)).comap e.symm.toMonoidHom from
      (Subgroup.comap_equiv_eq_map_symm e.symm _).symm]
    exact (Subgroup.isCoatom_comap e.symm).2 h.coatom
  ov := by
    intro X' hTX' hX'
    have hN : (Subgroup.normalizer (T : Set S)).map e.toMonoidHom =
        Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup S') : Set S') :=
      Subgroup.map_equiv_normalizer_eq T e
    have hTX : T ≤ X'.comap e.toMonoidHom := fun x hx => hTX' ⟨x, hx, rfl⟩
    have hX : ¬ X'.comap e.toMonoidHom ≤ Subgroup.normalizer (T : Set S) := by
      intro hle
      apply hX'
      rw [← hN]
      intro y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, hle hy, rfl⟩
    have h1 := h.ov _ hTX hX
    have h2 := Subgroup.map_mono (f := e.toMonoidHom) h1
    rw [← pElementSubgroup_map_equiv e, Subgroup.map_top_of_surjective _ e.surjective,
      Subgroup.map_comap_eq_self_of_surjective e.surjective] at h2
    exact h2

theorem OneNode.of_sylow {S : Type} [Group S] [Finite S] {T₀ T : Subgroup S}
    (h0 : IsSylowTwoOf T₀ ⊤) (hT : IsSylowTwoOf T ⊤) (h : OneNode S T₀) : OneNode S T := by
  obtain ⟨g, hg⟩ := exists_conj_of_sylowTwo h0 hT
  rw [← hg]
  exact h.map (MulAut.conj g)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
