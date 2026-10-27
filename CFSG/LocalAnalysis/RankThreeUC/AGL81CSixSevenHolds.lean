module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixSeven
public import Certificates.Certificate1255001
import CFSG.LocalAnalysis.RankThreeUC.GL33.Classes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.GL33 CFSG.SectionRank.Ccomm

section Coordinates

variable {D : Type} [Group D] (e : D ≃* Multiplicative (Fin 3 → ZMod 3))

private noncomputable def pullSub : AddSubgroup V ≃o Subgroup D :=
  AddSubgroup.toSubgroup.trans (MulEquiv.mapSubgroup e.symm)

private theorem mem_pullSub {B : AddSubgroup V} {d : D} :
    d ∈ pullSub e B ↔ Multiplicative.toAdd (e d) ∈ B := by
  change d ∈ (AddSubgroup.toSubgroup B).map e.symm.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Multiplicative.mem_toSubgroup]

private theorem card_pullSub (B : AddSubgroup V) : Nat.card (pullSub e B) = Nat.card B :=
  Nat.card_congr ((e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv fun _ => mem_pullSub e)

private theorem act_coord (α : MulAut D) (d : D) :
    act (elemAutEquivGL e α) (Multiplicative.toAdd (e d)) = Multiplicative.toAdd (e (α d)) :=
  elemAutEquivGL_mulVec e α d

private theorem irr_map {W : Subgroup (MulAut D)} (hW : IsIrreducibleAut W) :
    Irr (W.map (elemAutEquivGL e).toMonoidHom) := by
  intro B hB
  have hinv : ∀ w ∈ W, ∀ b ∈ pullSub e B, w b ∈ pullSub e B := by
    intro w hw b hb
    rw [mem_pullSub] at hb ⊢
    rw [← act_coord e w b]
    exact hB _ ⟨w, hw, rfl⟩ _ hb
  rcases hW _ hinv with h | h
  · left
    rw [← (pullSub e).map_bot] at h
    exact (pullSub e).injective h
  · right
    rw [← (pullSub e).map_top] at h
    exact (pullSub e).injective h

end Coordinates

private theorem normal_map_symm {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    {W : Subgroup A} {U : Subgroup B} (hUW : U ≤ W.map φ.toMonoidHom)
    (hUn : (U.subgroupOf (W.map φ.toMonoidHom)).Normal) :
    U.map φ.symm.toMonoidHom ≤ W ∧ ((U.map φ.symm.toMonoidHom).subgroupOf W).Normal := by
  have hle : U.map φ.symm.toMonoidHom ≤ W := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hUW hu
    simpa using hw
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff hle).2 fun h k hh hk => ?_⟩
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hh
  have hc := (Subgroup.normal_subgroupOf_iff hUW).1 hUn (φ h) (φ k) hh ⟨k, hk, rfl⟩
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, map_mul, map_mul, map_inv]
  exact hc


private theorem sixSevenGL_cert {W : Subgroup G} (hW : Irr W) :
    (∃ Bi : Fin 3 → AddSubgroup V, (∀ i, Nat.card (Bi i) = 3) ∧ (⨆ i, Bi i) = ⊤ ∧
        (∀ w ∈ W, ∀ i, ∃ j, ∀ v ∈ Bi i, act w v ∈ Bi j) ∧ Nat.card W ∣ 48) ∨
      (∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧ Nat.card U = 13) ∨
      (∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧
        Nonempty (U ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))) :=
  Certificates.certificate1255001 W hW

theorem sixSeven_holds : SixSeven := by
  intro D _ _ hDc hD3 hD W hW
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (p := 3) (W := D) (n := 3)
    (fun a b => hDc.is_comm.comm a b) hD3 (by rw [hD]; norm_num)
  have hcardW : Nat.card (W.map (elemAutEquivGL e).toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective (f := (elemAutEquivGL e).toMonoidHom)
      (elemAutEquivGL e).injective
  rcases sixSevenGL_cert (irr_map e hW) with ⟨Bi, hcard, hsup, hperm, h48⟩ |
    ⟨U, hUW, hUn, hU13⟩ | ⟨U, hUW, hUn, ⟨hU⟩⟩
  · refine Or.inl ⟨fun i => pullSub e (Bi i), fun i => (card_pullSub e _).trans (hcard i), ?_,
      fun w hw i => ?_, hcardW ▸ h48⟩
    · rw [← (pullSub e).map_iSup, hsup, (pullSub e).map_top]
    · obtain ⟨j, hj⟩ := hperm _ ⟨w, hw, rfl⟩ i
      refine ⟨j, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
      · rintro _ ⟨d, hd, rfl⟩
        have h := hj _ ((mem_pullSub e).1 hd)
        rw [MulEquiv.coe_toMonoidHom, act_coord] at h
        exact (mem_pullSub e).2 h
      · rw [Subgroup.card_map_of_injective (w : D ≃* D).injective, card_pullSub, card_pullSub,
          hcard, hcard]
  · obtain ⟨hle, hn⟩ := normal_map_symm (elemAutEquivGL e) hUW hUn
    refine Or.inr (Or.inl ⟨_, hle, hn, ?_⟩)
    rw [Subgroup.card_map_of_injective (f := (elemAutEquivGL e).symm.toMonoidHom)
      (elemAutEquivGL e).symm.injective, hU13]
  · obtain ⟨hle, hn⟩ := normal_map_symm (elemAutEquivGL e) hUW hUn
    exact Or.inr (Or.inr ⟨_, hle, hn, ⟨((U.equivMapOfInjective _
      (elemAutEquivGL e).symm.injective).symm).trans hU⟩⟩)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
