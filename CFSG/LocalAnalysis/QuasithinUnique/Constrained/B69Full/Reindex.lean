module

public import CFSG.Milestones.ASVolI.B6
public import CFSG.Quasithin.Background.B69SolvStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.ASVolI.ChB
open scoped Pointwise

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem canonFamily_enum_exists {G : Type*} [Group G] (𝓗 : Finset (Subgroup G)) :
    ∃ Hs : Fin 𝓗.card → Subgroup G, Function.Injective Hs ∧ ∀ H, H ∈ 𝓗 ↔ ∃ i, Hs i = H := by
  refine ⟨fun i => ((𝓗.equivFin.symm i : ↥𝓗) : Subgroup G), ?_, ?_⟩
  · intro i j hij
    exact 𝓗.equivFin.symm.injective (Subtype.val_injective hij)
  · intro H
    constructor
    · intro hH
      exact ⟨𝓗.equivFin ((⟨H, hH⟩ : ↥𝓗)),
        congrArg Subtype.val (𝓗.equivFin.symm_apply_apply ((⟨H, hH⟩ : ↥𝓗)))⟩
    · rintro ⟨i, rfl⟩
      exact (𝓗.equivFin.symm i).2

theorem canonFamily_iSup_eq {G ι : Type*} [Group G] {α : Type*} [CompleteLattice α]
    {𝓗 : Finset (Subgroup G)} {Hs : ι → Subgroup G} (hmem : ∀ H, H ∈ 𝓗 ↔ ∃ i, Hs i = H)
    (f : Subgroup G → α) : ⨆ i, f (Hs i) = ⨆ H ∈ 𝓗, f H := by
  apply le_antisymm
  · exact iSup_le fun i => le_iSup₂_of_le (Hs i) ((hmem _).2 ⟨i, rfl⟩) le_rfl
  · refine iSup₂_le fun H hH => ?_
    obtain ⟨i, rfl⟩ := (hmem H).1 hH
    exact le_iSup (fun i => f (Hs i)) i

theorem canonFamily_iSup_ne_eq {G ι : Type*} [Group G] {α : Type*} [CompleteLattice α]
    {𝓗 : Finset (Subgroup G)} {Hs : ι → Subgroup G} (hinj : Function.Injective Hs)
    (hmem : ∀ H, H ∈ 𝓗 ↔ ∃ i, Hs i = H) (f : Subgroup G → α) (i : ι) :
    ⨆ j, ⨆ (_ : j ≠ i), f (Hs j) = ⨆ H ∈ 𝓗, ⨆ (_ : H ≠ Hs i), f H := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    exact le_iSup₂_of_le (Hs j) ((hmem _).2 ⟨j, rfl⟩) (le_iSup_of_le (hinj.ne hj) le_rfl)
  · refine iSup₂_le fun H hH => ?_
    obtain ⟨j, rfl⟩ := (hmem H).1 hH
    refine iSup_le fun hne => ?_
    exact le_iSup₂_of_le j (fun hji => hne (congrArg Hs hji)) le_rfl

theorem canonFamily_inf_sup_comm {α : Type*} [Lattice α] {a b c d e : α}
    (h : (b ⊔ a) ⊓ (d ⊔ c) = e) : (a ⊔ b) ⊓ (c ⊔ d) = e := by
  rwa [sup_comm a b, sup_comm c d]

theorem canonFamily_of {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}
    (h : StructConcl X T M 𝓗) (hperm : ∀ g ∈ X, ∀ H ∈ 𝓗, B6.conjSub g H ∈ 𝓗) (hTX : T ≤ X) :
    ∃ (s : ℕ) (Hs : Fin s → Subgroup (MulAut V)), Function.Injective Hs ∧
      (∀ H, H ∈ 𝓗 ↔ ∃ i, Hs i = H) ∧
      IsIntDirProd (ffJ X) Hs ∧
      IsIntDirSumMod (commV (ffJ X)) (fixV (ffJ X)) (fun i => commV (Hs i)) ∧
      (∀ i j, i ≠ j → commSub (commV (Hs i)) (Hs j) = ⊥) ∧
      ((∀ t ∈ T, ∀ i, ∃ j, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j) ∧
        (∀ i j, ∃ t ∈ T, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j)) ∧
      (((ffJ X : Subgroup (MulAut V)) : Set (MulAut V)) * (T : Set (MulAut V)) =
        (X : Set (MulAut V))) := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  obtain ⟨Hs, hinj, hmem⟩ := canonFamily_enum_exists 𝓗
  have hin : ∀ i, Hs i ∈ 𝓗 := fun i => (hmem _).2 ⟨i, rfl⟩
  have eId : ⨆ i, Hs i = ffJ X :=
    (canonFamily_iSup_eq hmem (fun H : Subgroup (MulAut V) => H)).trans h2.symm
  have eComm : ⨆ i, commV (Hs i) = ⨆ H ∈ 𝓗, commV H :=
    canonFamily_iSup_eq hmem commV
  have eNe : ∀ i, ⨆ j, ⨆ (_ : j ≠ i), commV (Hs j) = ⨆ H ∈ 𝓗, ⨆ (_ : H ≠ Hs i), commV H :=
    fun i => canonFamily_iSup_ne_eq hinj hmem commV i
  have eNeId : ∀ i, ⨆ j, ⨆ (_ : j ≠ i), Hs j = ⨆ H ∈ 𝓗, ⨆ (_ : H ≠ Hs i), H :=
    fun i => canonFamily_iSup_ne_eq hinj hmem (fun H : Subgroup (MulAut V) => H) i
  refine ⟨𝓗.card, Hs, hinj, hmem, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold IsIntDirProd
    refine ⟨fun i j hij a ha b hb => h3 (Hs i) (hin i) (Hs j) (hin j) (hinj.ne hij) a ha b hb,
      ?_, eId⟩
    rw [iSupIndep_def]
    intro i
    rw [eNeId i, disjoint_iff]
    exact h4 (Hs i) (hin i)
  · unfold IsIntDirSumMod
    refine ⟨?_, fun i => ?_⟩
    · show fixV (ffJ X) ⊔ ⨆ i, commV (Hs i) = fixV (ffJ X) ⊔ commV (ffJ X)
      rw [eComm]
      exact (sup_comm _ _).trans (h5.symm.trans (sup_comm _ _))
    · show (fixV (ffJ X) ⊔ commV (Hs i)) ⊓
          (fixV (ffJ X) ⊔ ⨆ j, ⨆ (_ : j ≠ i), commV (Hs j)) = fixV (ffJ X)
      rw [eNe i]
      exact canonFamily_inf_sup_comm (h6 (Hs i) (hin i))
  · intro i j hij
    exact h7 (Hs i) (hin i) (Hs j) (hin j) (hinj.ne hij)
  · intro t ht i
    obtain ⟨j, hj⟩ := (hmem _).1 (hperm t (hTX ht) (Hs i) (hin i))
    exact ⟨j, hj.symm⟩
  · intro i j
    obtain ⟨t, ht, hte⟩ := h8 (Hs i) (hin i) (Hs j) (hin j)
    exact ⟨t, ht, hte⟩
  · have hTN : T ≤ Subgroup.normalizer ((ffJ X : Subgroup (MulAut V)) : Set (MulAut V)) :=
      hTX.trans (B6.le_normalizer_ffJ X)
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (ffJ X) T hTN, ← h9]

end B69

end CFSG.Quasithin
