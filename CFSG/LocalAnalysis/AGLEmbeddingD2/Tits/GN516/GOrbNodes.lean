module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviBQ

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Nodes

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {K S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

private theorem map_map_symm_mulAut (α : MulAut S) (X : Subgroup S) :
    (X.map α.toMonoidHom).map α.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hid : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id S :=
    MonoidHom.ext fun x => MulEquiv.symm_apply_apply α x
  rw [hid, Subgroup.map_id]

private theorem map_symm_map_mulAut (α : MulAut S) (X : Subgroup S) :
    (X.map α.symm.toMonoidHom).map α.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hid : α.toMonoidHom.comp α.symm.toMonoidHom = MonoidHom.id S :=
    MonoidHom.ext fun x => MulEquiv.apply_symm_apply α x
  rw [hid, Subgroup.map_id]

private theorem map_mulAut_injective (α : MulAut S) {X Y : Subgroup S}
    (e : X.map α.toMonoidHom = Y.map α.toMonoidHom) : X = Y :=
  calc X = (X.map α.toMonoidHom).map α.symm.toMonoidHom := (map_map_symm_mulAut α X).symm
    _ = (Y.map α.toMonoidHom).map α.symm.toMonoidHom := by rw [e]
    _ = Y := map_map_symm_mulAut α Y

theorem isMinOverBorel_map_of_map_eq (α : MulAut S) {T A : Subgroup S}
    (hT : T.map α.toMonoidHom = T) (hA : IsMinOverBorel (⊤ : Subgroup S) T A) :
    IsMinOverBorel (⊤ : Subgroup S) T (A.map α.toMonoidHom) := by
  unfold IsMinOverBorel at hA ⊢
  obtain ⟨hAL, hBA, hmin⟩ := hA
  rw [top_inf_eq] at hBA hmin ⊢
  have hN : (Subgroup.normalizer (T : Set S)).map α.toMonoidHom =
      Subgroup.normalizer (T : Set S) := by
    rw [Subgroup.map_equiv_normalizer_eq, hT]
  have hN' : (Subgroup.normalizer (T : Set S)).map α.symm.toMonoidHom =
      Subgroup.normalizer (T : Set S) := by
    calc (Subgroup.normalizer (T : Set S)).map α.symm.toMonoidHom
        = ((Subgroup.normalizer (T : Set S)).map α.toMonoidHom).map α.symm.toMonoidHom := by
          rw [hN]
      _ = Subgroup.normalizer (T : Set S) := map_map_symm_mulAut α _
  refine ⟨le_top, lt_of_le_of_ne ?_ ?_, fun Q hQ1 hQ2 => ?_⟩
  · calc Subgroup.normalizer (T : Set S)
        = (Subgroup.normalizer (T : Set S)).map α.toMonoidHom := hN.symm
      _ ≤ A.map α.toMonoidHom := Subgroup.map_mono hBA.le
  · intro heq
    apply hBA.ne
    calc Subgroup.normalizer (T : Set S)
        = (Subgroup.normalizer (T : Set S)).map α.symm.toMonoidHom := hN'.symm
      _ = (A.map α.toMonoidHom).map α.symm.toMonoidHom := by rw [← heq]
      _ = A := map_map_symm_mulAut α A
  · have hQ1' : Subgroup.normalizer (T : Set S) ≤ Q.map α.symm.toMonoidHom := by
      calc Subgroup.normalizer (T : Set S)
          = (Subgroup.normalizer (T : Set S)).map α.symm.toMonoidHom := hN'.symm
        _ ≤ Q.map α.symm.toMonoidHom := Subgroup.map_mono hQ1
    have hQ2' : Q.map α.symm.toMonoidHom ≤ A := by
      calc Q.map α.symm.toMonoidHom ≤ (A.map α.toMonoidHom).map α.symm.toMonoidHom :=
            Subgroup.map_mono hQ2
        _ = A := map_map_symm_mulAut α A
    rcases hmin _ hQ1' hQ2' with e | e
    · left
      calc Q = (Q.map α.symm.toMonoidHom).map α.toMonoidHom := (map_symm_map_mulAut α Q).symm
        _ = (Subgroup.normalizer (T : Set S)).map α.toMonoidHom := by rw [e]
        _ = Subgroup.normalizer (T : Set S) := hN
    · right
      calc Q = (Q.map α.symm.toMonoidHom).map α.toMonoidHom := (map_symm_map_mulAut α Q).symm
        _ = A.map α.toMonoidHom := by rw [e]

private theorem exists_map_parJ_mulAut (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    ∃ i, ((parJ D H {j}).map π).map α.toMonoidHom = (parJ D H {i}).map π :=
  exists_eq_map_parJ h (isMinOverBorel_map_of_map_eq α hα (isMinOverBorel_map_parJ h j))

private noncomputable def nodeImg (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    Fin D.rank :=
  Classical.choose (exists_map_parJ_mulAut h α hα j)

private theorem nodeImg_spec (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    ((parJ D H {j}).map π).map α.toMonoidHom = (parJ D H {nodeImg h α hα j}).map π :=
  Classical.choose_spec (exists_map_parJ_mulAut h α hα j)

private theorem nodeImg_injective (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) :
    Function.Injective (nodeImg h α hα) := by
  intro j j' e
  have e1 := nodeImg_spec h α hα j
  have e2 := nodeImg_spec h α hα j'
  rw [e] at e1
  exact parJ_map_injective h (map_mulAut_injective α (e1.trans e2.symm))

noncomputable def nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) :
    Equiv.Perm (Fin D.rank) :=
  Equiv.ofBijective (nodeImg h α hα) (Finite.injective_iff_bijective.1 (nodeImg_injective h α hα))

private theorem nodePerm_apply (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    nodePerm h α hα j = nodeImg h α hα j :=
  rfl

theorem map_parJ_singleton_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    ((parJ D H {j}).map π).map α.toMonoidHom = (parJ D H {nodePerm h α hα j}).map π := by
  rw [nodePerm_apply]
  exact nodeImg_spec h α hα j

theorem nodePerm_eq_iff (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j k : Fin D.rank) :
    nodePerm h α hα j = k ↔
      ((parJ D H {j}).map π).map α.toMonoidHom = (parJ D H {k}).map π := by
  rw [nodePerm_apply]
  constructor
  · rintro rfl
    exact nodeImg_spec h α hα j
  · intro e
    exact parJ_map_injective h ((nodeImg_spec h α hα j).symm.trans e)

private theorem parJ_eq_sup_iSup_singleton (J : Set (Fin D.rank)) :
    parJ D H J = borel D H ⊔ ⨆ j ∈ J, parJ D H {j} := by
  have hsingle : ∀ j : Fin D.rank, parJ D H {j} = borel D H ⊔ rankOne D.rootGroup j := by
    intro j
    show borel D H ⊔ ⨆ i ∈ ({j} : Set (Fin D.rank)), rankOne D.rootGroup i = _
    rw [iSup_singleton]
  apply le_antisymm
  · show borel D H ⊔ ⨆ j ∈ J, rankOne D.rootGroup j ≤ _
    refine sup_le le_sup_left (iSup₂_le fun j hj => le_sup_of_le_right ?_)
    exact (rankOne_le_parJ (Set.mem_singleton j)).trans
      (le_iSup₂_of_le (f := fun k (_ : k ∈ J) => parJ D H {k}) j hj le_rfl)
  · refine sup_le (borel_le_parJ J) (iSup₂_le fun j hj => ?_)
    rw [hsingle j]
    exact sup_le (borel_le_parJ J) (rankOne_le_parJ hj)

private theorem map_parJ_eq_sup (J : Set (Fin D.rank)) :
    (parJ D H J).map π = (borel D H).map π ⊔ ⨆ j ∈ J, (parJ D H {j}).map π := by
  rw [parJ_eq_sup_iSup_singleton J, Subgroup.map_sup]
  congr 1
  simp only [Subgroup.map_iSup]

theorem map_parJ_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (J : Set (Fin D.rank)) :
    ((parJ D H J).map π).map α.toMonoidHom = (parJ D H (nodePerm h α hα '' J)).map π := by
  have hB : ((borel D H).map π).map α.toMonoidHom = (borel D H).map π := by
    rw [← h.normalizer_map_posUnipotent, Subgroup.map_equiv_normalizer_eq, hα]
  rw [map_parJ_eq_sup J, map_parJ_eq_sup (nodePerm h α hα '' J), Subgroup.map_sup, hB,
    iSup_image]
  congr 1
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun j => iSup_congr fun _ => map_parJ_singleton_nodePerm h α hα j

theorem map_unipJ_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (J : Set (Fin D.rank)) :
    ((unipJ D J).map π).map α.toMonoidHom = (unipJ D (nodePerm h α hα '' J)).map π := by
  rw [← pElement_map_parJ h J, ← pElement_map_parJ h (nodePerm h α hα '' J),
    ← CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.pElementSubgroup_map_equiv α,
    map_parJ_nodePerm h α hα J]

private theorem mulAut_toMonoidHom_mul (α β : MulAut S) :
    (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem posUnipotent_map_mulAut_mul (α β : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (hβ : ((posUnipotent D).map π).map β.toMonoidHom = (posUnipotent D).map π) :
    ((posUnipotent D).map π).map (α * β).toMonoidHom = (posUnipotent D).map π := by
  rw [mulAut_toMonoidHom_mul, ← Subgroup.map_map, hβ, hα]

theorem nodePerm_mul (h : BorelQuotient D n H π M) (α β : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (hβ : ((posUnipotent D).map π).map β.toMonoidHom = (posUnipotent D).map π) :
    nodePerm h (α * β) (posUnipotent_map_mulAut_mul α β hα hβ) =
      nodePerm h α hα * nodePerm h β hβ := by
  refine Equiv.ext fun j => ?_
  rw [Equiv.Perm.mul_apply, nodePerm_eq_iff, mulAut_toMonoidHom_mul, ← Subgroup.map_map,
    map_parJ_singleton_nodePerm h β hβ j,
    map_parJ_singleton_nodePerm h α hα (nodePerm h β hβ j)]

@[expose] noncomputable def nodeHom (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) :
    ↥𝒜 →* Equiv.Perm (Fin D.rank) :=
  MonoidHom.mk' (fun α => nodePerm h α.1 (h𝒜 α.1 α.2)) fun α β =>
    nodePerm_mul h α.1 β.1 (h𝒜 α.1 α.2) (h𝒜 β.1 β.2)

theorem nodeHom_apply (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (α : ↥𝒜) (j : Fin D.rank) :
    nodeHom h 𝒜 h𝒜 α j = nodePerm h α.1 (h𝒜 α.1 α.2) j :=
  rfl

end CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
