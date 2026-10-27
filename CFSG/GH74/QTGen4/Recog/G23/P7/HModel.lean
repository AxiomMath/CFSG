module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.GH74.QTGen4.Recog.G23.GlueExtD
public import CFSG.GH74.QTGen4.Recog.G23.GlueExtC
public import CFSG.GH74.QTGen4.Recog.G23.HLettersB

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.CosetTable CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {G : Type} [Group G]

theorem HLetters.mem_castSucc {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hL : HLetters H H₁ H₂ e)
    (i : Fin 5) : e i.castSucc ∈ H := by
  rw [← hL.gen]
  exact Subgroup.subset_closure ⟨i, rfl⟩

section

theorem exists_mulEquiv_Hc [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hH : G23One H H₁ H₂) (hL : HLetters H H₁ H₂ e) :
    ∃ φ : ↥H ≃* Hc, ∀ i : Fin 5,
      ((φ ⟨e i.castSucc, hL.mem_castSucc i⟩ : Hc) : Equiv.Perm (Fin 32)) =
        f5 (Fin.cast len5.symm i) := by
  obtain ⟨ψ, hψ⟩ := exists_iso_PG_Hc
  have hfin : Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) := g23H5_card_le.1
  let f : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length → H :=
    fun i => ⟨e (Fin.cast len5 i).castSucc, hL.mem_castSucc _⟩
  have hrel : ∀ r ∈ {r : FreeGroup (Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) |
      r ∈ g23H5.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply H.subtype_injective
    have h1 : H.subtype.comp (FreeGroup.lift f) = FreeGroup.lift (fun i => (f i : G)) :=
      FreeGroup.ext_hom _ _ fun i => by simp
    have h2 := congrArg (fun φ : FreeGroup _ →* G => φ (FreeGroup.mk w)) h1
    simp only [MonoidHom.comp_apply] at h2
    rw [h2, map_one]
    exact sat_H5 e hL.rels w hw
  let χ : PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5 →* H := PresentedGroup.toGroup hrel
  have hχof : ∀ i, χ (PresentedGroup.of i) = f i := fun i => PresentedGroup.toGroup.of hrel
  have hsurj : Function.Surjective χ := by
    have hsub : Subgroup.closure (Set.range fun i : Fin 5 => e i.castSucc) ≤ χ.range.map H.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨⟨e i.castSucc, hL.mem_castSucc i⟩, ⟨PresentedGroup.of (Fin.cast len5.symm i), ?_⟩, rfl⟩
      rw [hχof]
      simp [f]
    rw [hL.gen] at hsub
    intro y
    obtain ⟨y', ⟨x, hx⟩, hy'⟩ := hsub y.2
    exact ⟨x, Subtype.ext (hx ▸ hy')⟩
  have hHcard : Nat.card H = 576 := card_H_of_G23One hH
  have hG : Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ≤ Nat.card H := by
    rw [hHcard]; exact g23H5_card_le.2
  have hbij : Function.Bijective χ := hsurj.bijective_of_nat_card_le hG
  refine ⟨(MulEquiv.ofBijective χ hbij).symm.trans ψ, fun i => ?_⟩
  have hi : (⟨e i.castSucc, hL.mem_castSucc i⟩ : H) =
      χ (PresentedGroup.of (Fin.cast len5.symm i)) := by
    rw [hχof]; simp [f]
  have hsymm : ∀ x, (MulEquiv.ofBijective χ hbij).symm (χ x) = x := fun x =>
    (MulEquiv.ofBijective χ hbij).symm_apply_apply x
  rw [hi, MulEquiv.trans_apply, hsymm]
  exact hψ (Fin.cast len5.symm i)

end

end CFSG.GH74.QTGen4.Recog.G23.P7
