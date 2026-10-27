module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
import CFSG.Quasithin.Background.C126Glue

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.C126

variable {G : Type} [Group G] [Finite G]

@[expose] def BlocksGen (H T : Subgroup G) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
    (∀ i, IsChiBlock H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
    (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
    (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
    (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j)

omit [Finite G] in
theorem isChiBlock_conjSub {H T K : Subgroup G} (hT : T ≤ H) (hK : IsChiBlock H K) {t : G}
    (ht : t ∈ T) : IsChiBlock H (B6.conjSub t K) := by
  rw [conjSub_eq_map]
  obtain ⟨hb, htype⟩ := hK
  refine ⟨IsBlock2.conjByElt_of_mem hb (hT ht), ?_⟩
  rcases htype with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj t)⟩
  · exact Or.inr ⟨m, hm, hm3, L238.IsAltType.map_equiv halt (MulAut.conj t)⟩

theorem blocksGen_of_oneBlock {H T : Subgroup G} (hF : CharTwo H) (hT : IsSylowTwoOf T H)
    (h : OneBlockGen H T) : BlocksGen H T := by
  classical
  obtain ⟨K, hK, hKJ, hH⟩ := h
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let 𝒦 : Set (Subgroup G) := {K' | ∃ t ∈ T, K' = B6.conjSub t K}
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥𝒦
  let Kf : Fin r → Subgroup G := fun i => (e.symm i).1
  have hmem : ∀ i, ∃ t ∈ T, Kf i = B6.conjSub t K := fun i => (e.symm i).2
  have hKf : ∀ t ∈ T, ∃ j, Kf j = B6.conjSub t K := fun t ht =>
    ⟨e ⟨B6.conjSub t K, t, ht, rfl⟩, by simp [Kf]⟩
  have hblock : ∀ i, IsChiBlock H (Kf i) := fun i => by
    obtain ⟨t, ht, hti⟩ := hmem i
    rw [hti]
    exact isChiBlock_conjSub hT.1 hK ht
  have hne : ∀ i j, i ≠ j → Kf i ≠ Kf j := fun i j hij hKij =>
    hij (e.symm.injective (Subtype.ext hKij))
  have hsup_eq : (⨆ i, Kf i) = conjJoin T K := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨t, ht, hti⟩ := hmem i
      rw [hti]
      exact le_iSup (fun s : T => K.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩
    · refine iSup_le fun s => ?_
      obtain ⟨j, hj⟩ := hKf s s.2
      show B6.conjSub (s : G) K ≤ _
      rw [← hj]
      exact le_iSup Kf j
  have hNH : conjJoin T K ≤ H :=
    CFSG.QuasithinUnique.A5.G3.conjJoin_le_of_le hT.1 hK.1.2.1
  have hTN : T ≤ Subgroup.normalizer (conjJoin T K : Set G) :=
    CFSG.QuasithinUnique.A5.G3.le_normalizer_conjJoin' T K
  have hHsup : T ⊔ conjJoin T K = H := by
    rw [← conjClosure_eq_conjJoin]
    exact hH.symm
  have hHN : H ≤ Subgroup.normalizer (conjJoin T K : Set G) := by
    rw [← hHsup]
    exact sup_le hTN Subgroup.le_normalizer
  have h2 := B6.isTwoQuotient_of_sup_eq hT.2.1 hHN hHsup
  have hres : twoResidual H = conjJoin T K := by
    apply le_antisymm
    · exact twoResidual_le_of_isTwoQuotient hNH hHN h2
    · refine iSup_le fun s => ?_
      have hb : IsChiBlock H (B6.conjSub (s : G) K) := isChiBlock_conjSub hT.1 hK s.2
      exact le_twoResidual_of_short hb.1.2.1 hb.1.1
  have hone : 1 ≤ r := (e ⟨K, 1, T.one_mem, (B6.conjSub_one K).symm⟩).pos
  refine ⟨r, Kf, hone, fun i => ⟨hblock i, ?_⟩, fun i j hij => ?_, hres.trans hsup_eq.symm,
    fun t ht i => ?_, fun i j => ?_⟩
  · obtain ⟨t, ht, hti⟩ := hmem i
    rw [hti]
    exact commutator_conjSub_thompsonJ hKJ ht
  · exact distinctBlocksCommuteStatement H (Kf i) (Kf j) hF (hblock i).1 (hblock j).1 (hne i j hij)
  · obtain ⟨t', ht', hti⟩ := hmem i
    obtain ⟨j, hj⟩ := hKf (t * t') (T.mul_mem ht ht')
    exact ⟨j, by rw [hj, hti, B6.conjSub_mul]⟩
  · obtain ⟨t₁, ht₁, hi⟩ := hmem i
    obtain ⟨t₂, ht₂, hj⟩ := hmem j
    refine ⟨t₂ * t₁⁻¹, T.mul_mem ht₂ (T.inv_mem ht₁), ?_⟩
    rw [hi, hj, ← B6.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem concl_of_concl1Gen {C₁ C₂ H T : Subgroup G} (hF : CharTwo H) (hT : IsSylowTwoOf T H)
    (h : Concl1Gen C₁ C₂ H T) :
    C₁ ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ : Set G) ∨ BlocksGen H T := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (blocksGen_of_oneBlock hF hT h))

end CFSG.AGLEmbeddingD2.GN
